@echo off
chcp 65001 >nul
cd /d "%~dp0"
where rustc >nul 2>nul
if errorlevel 1 goto norust
if exist rust_core\Cargo.toml goto build
if not exist Cargo.toml goto nofiles
echo Раскладываю файлы Rust по папкам...
mkdir rust_core\src 2>nul
move /Y Cargo.toml rust_core\Cargo.toml >nul
if exist pyproject.toml move /Y pyproject.toml rust_core\pyproject.toml >nul
if exist lib.rs move /Y lib.rs rust_core\src\lib.rs >nul
:build
if not exist rust_core\src\lib.rs goto nolib
echo === Сборка Rust-ускорителя ===
call venv\Scripts\activate.bat
pip install maturin
cd rust_core
maturin develop --release
if errorlevel 1 goto fail
echo.
echo === Готово. Запустите check.bat: там должно быть "Rust-модуль fast_core подключён" ===
pause
exit /b 0
:norust
echo Rust не найден. Установите его с rustup.rs, закройте это окно и откройте заново.
pause
exit /b 1
:nofiles
echo Не нашёл Cargo.toml. Положите Cargo.toml, pyproject.toml и lib.rs в эту же папку и запустите снова.
pause
exit /b 1
:nolib
echo Не нашёл lib.rs. Положите lib.rs в эту же папку и запустите снова.
pause
exit /b 1
:fail
echo Сборка не удалась. Программа и без Rust работает. Пришлите мне текст ошибки, если хотите довести.
pause
exit /b 1
