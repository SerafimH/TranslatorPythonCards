@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo === Создаю окружение (нужен Python 3.12 с галочкой Add to PATH) ===
py -3.12 -m venv venv || py -3 -m venv venv
if not exist venv\Scripts\python.exe goto nopython
venv\Scripts\python.exe -m pip install --upgrade pip
venv\Scripts\python.exe -m pip install -r requirements.txt
if errorlevel 1 goto fail
echo.
echo === Готово. Теперь запустите check.bat ===
pause
exit /b 0
:nopython
echo Python не найден. Установите Python 3.12 с python.org и поставьте галочку "Add python.exe to PATH".
pause
exit /b 1
:fail
echo Установка пакетов не удалась. Скопируйте текст ошибки выше и пришлите мне.
pause
exit /b 1
