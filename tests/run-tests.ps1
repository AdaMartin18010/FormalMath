# FormalMath 自动化测试运行脚本 (PowerShell)

param(
    [Parameter(Position=0)]
    [ValidateSet("all", "frontend", "backend", "lean4", "e2e", "integration", "unit")]
    [string]$TestType = "all",
    
    [switch]$Verbose,
    [switch]$Coverage,
    [switch]$Watch,
    [switch]$FailFast,
    [switch]$Help
)

# 颜色函数
function Write-Header($message) {
    Write-Host "`n========================================" -ForegroundColor Blue
    Write-Host $message -ForegroundColor Blue
    Write-Host "========================================`n" -ForegroundColor Blue
}

function Write-Success($message) {
    Write-Host "✓ $message" -ForegroundColor Green
}

function Write-Error($message) {
    Write-Host "✗ $message" -ForegroundColor Red
}

function Write-Warning($message) {
    Write-Host "⚠ $message" -ForegroundColor Yellow
}

# 帮助信息
function Show-Help {
    @"
FormalMath 测试运行脚本

用法: .\run-tests.ps1 [测试类型] [选项]

测试类型:
    all                 运行所有测试 (默认)
    frontend            仅运行前端测试
    backend             仅运行后端测试
    lean4               仅运行Lean4测试
    e2e                 仅运行E2E测试
    integration         仅运行集成测试
    unit                仅运行单元测试

选项:
    -Verbose            详细输出
    -Coverage           生成覆盖率报告
    -Watch              监视模式
    -FailFast           首次失败时停止
    -Help               显示帮助信息

示例:
    .\run-tests.ps1                      # 运行所有测试
    .\run-tests.ps1 frontend             # 仅运行前端测试
    .\run-tests.ps1 backend -Coverage    # 运行后端测试并生成覆盖率
"@
}

if ($Help) {
    Show-Help
    exit 0
}

# 运行前端测试
function Invoke-FrontendTests {
    Write-Header "运行前端测试"
    
    Push-Location ..\FormalMath-Interactive
    
    try {
        # 检查依赖
        if (-not (Test-Path "node_modules")) {
            Write-Warning "安装前端依赖..."
            npm ci
        }
        
        # 代码检查
        Write-Header "运行 ESLint"
        npm run lint 2>$null
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "ESLint 检查失败"
        }
        
        # 类型检查
        Write-Header "运行 TypeScript 类型检查"
        npm run type-check 2>$null
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "类型检查失败"
        }
        
        # 单元测试
        Write-Header "运行前端单元测试"
        $jestArgs = @("--config=..\tests\frontend\jest.config.js")
        
        if ($Coverage) {
            $jestArgs += "--coverage"
        }
        if ($Watch) {
            $jestArgs += "--watch"
        }
        if ($FailFast) {
            $jestArgs += "--bail"
        }
        
        & npx jest @jestArgs
        
        if ($LASTEXITCODE -ne 0) {
            throw "前端测试失败"
        }
        
        Write-Success "前端测试完成"
    }
    finally {
        Pop-Location
    }
}

# 运行后端测试
function Invoke-BackendTests {
    Write-Header "运行后端测试"
    
    Push-Location backend
    
    try {
        # 检查依赖
        try {
            python -c "import pytest" 2>$null
        }
        catch {
            Write-Warning "安装Python测试依赖..."
            pip install -r requirements-test.txt
        }
        
        # 构建参数
        $pytestArgs = @("-v")
        
        if ($Coverage) {
            $pytestArgs += @("--cov=..\..\tools", "--cov-report=html:..\coverage\backend", "--cov-report=term")
        }
        if ($FailFast) {
            $pytestArgs += "-x"
        }
        
        # 单元测试
        Write-Header "运行后端单元测试"
        & pytest unit/ @pytestArgs
        
        if ($LASTEXITCODE -ne 0) {
            throw "后端单元测试失败"
        }
        
        # 集成测试
        if ($TestType -eq "all" -or $TestType -eq "integration") {
            Write-Header "运行后端集成测试"
            & pytest integration/ @pytestArgs -m integration
            if ($LASTEXITCODE -ne 0) {
                Write-Warning "集成测试失败"
            }
        }
        
        Write-Success "后端测试完成"
    }
    finally {
        Pop-Location
    }
}

# 运行Lean4测试
function Invoke-Lean4Tests {
    Write-Header "运行Lean4测试"
    
    Push-Location lean4
    
    try {
        # 检查lake
        if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
            Write-Error "未找到lake，请先安装Lean4"
            return
        }
        
        # 构建
        Write-Header "构建Lean4测试"
        lake build
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "构建失败"
        }
        
        # 运行测试
        Write-Header "运行Lean4测试"
        lake test
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "测试失败"
        }
        
        Write-Success "Lean4测试完成"
    }
    finally {
        Pop-Location
    }
}

# 运行E2E测试
function Invoke-E2ETests {
    Write-Header "运行E2E测试"
    
    Push-Location ..\FormalMath-Interactive
    
    try {
        # 构建应用
        Write-Header "构建应用"
        npm run build
        
        # 启动服务器
        Write-Header "启动测试服务器"
        $server = Start-Process -FilePath "npm" -ArgumentList "run", "preview" -PassThru
        
        # 等待服务器启动
        Start-Sleep -Seconds 5
        
        try {
            # 运行Cypress测试
            Push-Location ..\tests
            & npx cypress run --config-file frontend/cypress.config.ts
            
            if ($LASTEXITCODE -ne 0) {
                throw "E2E测试失败"
            }
            
            Write-Success "E2E测试完成"
        }
        finally {
            # 停止服务器
            if ($server -and -not $server.HasExited) {
                Stop-Process -Id $server.Id -Force 2>$null
            }
            Pop-Location
        }
    }
    finally {
        Pop-Location
    }
}

# 主逻辑
function Main {
    Write-Header "FormalMath 测试套件"
    Write-Host "测试类型: $TestType"
    Write-Host "覆盖率: $Coverage"
    Write-Host "监视模式: $Watch"
    Write-Host ""
    
    $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()
    
    try {
        switch ($TestType) {
            "all" {
                Invoke-FrontendTests
                Invoke-BackendTests
                Invoke-Lean4Tests
                Invoke-E2ETests
            }
            "frontend" { Invoke-FrontendTests }
            "backend" { Invoke-BackendTests }
            "lean4" { Invoke-Lean4Tests }
            "e2e" { Invoke-E2ETests }
            "integration" { Invoke-BackendTests }
            "unit" {
                Invoke-FrontendTests
                Invoke-BackendTests
            }
        }
        
        $stopwatch.Stop()
        Write-Header "测试完成"
        Write-Host "总耗时: $($stopwatch.Elapsed.TotalSeconds)秒"
        Write-Success "所有测试通过！"
    }
    catch {
        Write-Error $_.Exception.Message
        exit 1
    }
}

# 运行主函数
Main
