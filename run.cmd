@echo off
setlocal
cd /d "%~dp0"
where py >nul 2>nul
if not errorlevel 1 (
  py -3 scripts\verify.py --fetch-cache
  exit /b
)
where python >nul 2>nul
if errorlevel 1 (
  echo Python 3 is required. CI installs Python and Lean automatically.
  exit /b 2
)
python scripts\verify.py --fetch-cache
exit /b %errorlevel%
