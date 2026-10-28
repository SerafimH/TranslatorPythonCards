@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo Экранный переводчик запущен. Это окно можно свернуть. Закрытие окна = выход.
venv\Scripts\python.exe translator.py %*
pause
