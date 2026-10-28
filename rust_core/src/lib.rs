use pyo3::prelude::*;
use pyo3::types::PyBytes;
use std::thread;

/// Версия набора функций. Python-часть проверяет, что нужные функции есть.
#[pyfunction]
fn api_version() -> u32 {
    2
}

/// Таблица для одной оси увеличения: для каждого выходного пикселя два соседних
/// входных и вес второго в долях 1/256. Считается один раз, а не для каждого пикселя.
fn axis_table(out_len: usize, in_len: usize, scale: usize) -> Vec<(usize, usize, u32)> {
    let s = scale as f32;
    (0..out_len)
        .map(|o| {
            let f = ((o as f32 + 0.5) / s - 0.5).max(0.0);
            let i0 = (f.floor() as usize).min(in_len - 1);
            let i1 = (i0 + 1).min(in_len - 1);
            let w = (((f - i0 as f32) * 256.0).round() as u32).min(256);
            (i0, i1, w)
        })
        .collect()
}

/// Вся работа без Python: серый цвет, инверсия тёмного фона, контраст, увеличение.
fn preprocess_impl(bgra: &[u8], width: usize, height: usize, scale: usize) -> Vec<u8> {
    let n = width * height;

    // 1. Серый цвет по формуле Pillow (чтобы результат совпадал с Python-версией),
    //    заодно считаем гистограмму и сумму яркости за один проход.
    let mut gray = vec![0u8; n];
    let mut hist = [0usize; 256];
    let mut sum: u64 = 0;
    for (g, px) in gray.iter_mut().zip(bgra[..n * 4].chunks_exact(4)) {
        let v = ((px[2] as u32 * 19595 + px[1] as u32 * 38470 + px[0] as u32 * 7471 + 0x8000) >> 16)
            as u8;
        *g = v;
        hist[v as usize] += 1;
        sum += v as u64;
    }

    // 2. Тёмный фон (игры, Discord): инвертируем. OCR лучше читает тёмный текст на светлом.
    let invert = (sum / n as u64) < 110;
    if invert {
        hist.reverse();
    }

    // 3. Границы контраста: отбрасываем 1% самых тёмных и самых светлых пикселей.
    let cut = n / 100;
    let mut acc = 0usize;
    let mut lo = 0usize;
    for i in 0..256 {
        acc += hist[i];
        if acc > cut {
            lo = i;
            break;
        }
    }
    acc = 0;
    let mut hi = 255usize;
    for i in (0..256).rev() {
        acc += hist[i];
        if acc > cut {
            hi = i;
            break;
        }
    }

    // Инверсия и растяжение контраста сводятся к одной таблице из 256 значений.
    let mut lut = [0u8; 256];
    for v in 0..256usize {
        let t = if invert { 255 - v } else { v };
        lut[v] = if hi > lo + 8 {
            let x = (t as f32 - lo as f32) / (hi - lo) as f32;
            (x.clamp(0.0, 1.0) * 255.0).round() as u8
        } else {
            t as u8
        };
    }
    for g in gray.iter_mut() {
        *g = lut[*g as usize];
    }

    // 4. Увеличение в `scale` раз (билинейно, целыми числами), полосами по строкам в нескольких потоках.
    let ow = width * scale;
    let oh = height * scale;
    let xs = axis_table(ow, width, scale);
    let ys = axis_table(oh, height, scale);
    let mut out = vec![0u8; ow * oh];

    let base_threads = if ow * oh < 300_000 {
        1
    } else {
        thread::available_parallelism().map(|p| p.get()).unwrap_or(1).min(4)
    };
    let threads = base_threads.min(oh).max(1);
    let rows_per = (oh + threads - 1) / threads;

    let gray_ref = &gray;
    let xs_ref = &xs;
    let ys_ref = &ys;
    thread::scope(|sc| {
        for (bi, band) in out.chunks_mut(rows_per * ow).enumerate() {
            sc.spawn(move || {
                let y_start = bi * rows_per;
                for (r, row) in band.chunks_mut(ow).enumerate() {
                    let (y0, y1, wy) = ys_ref[y_start + r];
                    let r0 = &gray_ref[y0 * width..(y0 + 1) * width];
                    let r1 = &gray_ref[y1 * width..(y1 + 1) * width];
                    for (px, &(x0, x1, wx)) in row.iter_mut().zip(xs_ref.iter()) {
                        let top = r0[x0] as u32 * (256 - wx) + r0[x1] as u32 * wx;
                        let bot = r1[x0] as u32 * (256 - wx) + r1[x1] as u32 * wx;
                        *px = ((top * (256 - wy) + bot * wy + 32768) >> 16) as u8;
                    }
                }
            });
        }
    });
    out
}

/// Кадр BGRA -> серая контрастная картинка, увеличенная в `scale` раз.
/// Python во время расчёта не блокируется (GIL отпускается).
#[pyfunction]
fn preprocess<'py>(
    py: Python<'py>,
    bgra: &[u8],
    width: usize,
    height: usize,
    scale: usize,
) -> PyResult<Bound<'py, PyBytes>> {
    let n = width.checked_mul(height).unwrap_or(0);
    if width == 0 || height == 0 || scale == 0 || scale > 16 || bgra.len() < n * 4 {
        return Err(pyo3::exceptions::PyValueError::new_err(
            "неверный размер изображения",
        ));
    }
    let out = py.allow_threads(|| preprocess_impl(bgra, width, height, scale));
    Ok(PyBytes::new_bound(py, &out))
}

/// Какая доля пикселей двух BGRA-кадров отличается больше, чем на `threshold`
/// (по самому изменившемуся из каналов). 0.0 = кадры одинаковы, 1.0 = всё другое.
/// Нужна кэшу распознавания: если экран не изменился, OCR повторять не надо.
#[pyfunction]
#[pyo3(signature = (a, b, threshold=24))]
fn diff_ratio(py: Python<'_>, a: &[u8], b: &[u8], threshold: u8) -> PyResult<f64> {
    if a.is_empty() || a.len() != b.len() || a.len() % 4 != 0 {
        return Err(pyo3::exceptions::PyValueError::new_err(
            "кадры должны быть одного размера (BGRA)",
        ));
    }
    let total = (a.len() / 4) as f64;
    let changed = py.allow_threads(|| {
        a.chunks_exact(4)
            .zip(b.chunks_exact(4))
            .filter(|(p, q)| {
                let d0 = p[0].abs_diff(q[0]);
                let d1 = p[1].abs_diff(q[1]);
                let d2 = p[2].abs_diff(q[2]);
                d0.max(d1).max(d2) > threshold
            })
            .count()
    });
    Ok(changed as f64 / total)
}

#[pymodule]
fn fast_core(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(api_version, m)?)?;
    m.add_function(wrap_pyfunction!(preprocess, m)?)?;
    m.add_function(wrap_pyfunction!(diff_ratio, m)?)?;
    Ok(())
}
