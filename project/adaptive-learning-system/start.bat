@echo off
chcp 65001 >nul
echo 🎓 FormalMath 自适应学习路径系统启动脚本
echo ==========================================
echo.

REM 检查Python
echo 检查Python环境...
python --version >nul 2>&1
if errorlevel 1 (
    echo ❌ 未找到Python，请先安装Python 3.9+
    exit /b 1
)
echo ✅ Python已安装

REM 检查Node.js
echo 检查Node.js环境...
node --version >nul 2>&1
if errorlevel 1 (
    echo ❌ 未找到Node.js，请先安装Node.js 16+
    exit /b 1
)
echo ✅ Node.js已安装

echo.
echo ==========================================
echo 启动后端服务...
echo ==========================================
cd backend

REM 检查虚拟环境
if not exist venv (
    echo 创建虚拟环境...
    python -m venv venv
)

echo 激活虚拟环境...
call venv\Scripts\activate

echo 安装后端依赖...
pip install -q -r requirements.txt

echo 启动后端服务 (端口 8000)...
start "Adaptive Learning Backend" cmd /k "python src/main.py"

cd ..

echo.
echo ==========================================
echo 启动前端服务...
echo ==========================================
cd frontend

echo 安装前端依赖...
call npm install

echo 启动前端服务 (端口 3000)...
start "Adaptive Learning Frontend" cmd /k "npm start"

cd ..

echo.
echo ==========================================
echo ✅ 系统启动完成！
echo ==========================================
echo.
echo 访问地址:
echo   - 前端界面: http://localhost:3000
echo   - API文档:  http://localhost:8000/docs
echo   - API基础:  http://localhost:8000/api/v1
echo.
echo 按任意键关闭所有服务...
pause >nul

echo 关闭服务...
taskkill /FI "WINDOWTITLE eq Adaptive Learning Backend*" /F >nul 2>&1
taskkill /FI "WINDOWTITLE eq Adaptive Learning Frontend*" /F >nul 2>&1
echo 服务已关闭。
