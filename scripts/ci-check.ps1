# =============================================================================
# FormalMath 本地CI检查脚本 (Windows PowerShell)
# 描述: 在本地运行类似CI的检查，帮助开发者在提交前发现问题
# 使用方法: .\scripts\ci-check.ps1 [选项]
# =============================================================================

#requires -Version 5.1

[CmdletBinding()]
param(
    [switch]$Help,           # 显示帮助
    [switch]$Markdown,       # 仅检查Markdown
    [switch]$Python,         # 仅检查Python
    [switch]$Links,          # 检查链接
    [switch]$Lean,           # 检查Lean4
    [switch]$All,            # 运行所有检查
    [switch]$Fix,            # 自动修复
    [switch]$Verbose,        # 详细输出
    [switch]$Quick           # 快速模式
)

# 颜色定义
$Colors = @{
    Red = 'Red'
    Green = 'Green'
    Yellow = 'Yellow'
    Blue = 'Cyan'
}

# 默认配置
$Config = @{
    CheckMarkdown = $true
    CheckPython = $true
    CheckLinks = $false
    CheckLean = $false
    FixMode = $false
    Verbose = $false
}

# 计数器
$script:Errors = 0
$script:Warnings = 0

# 帮助信息
function Show-Help {
    @"
FormalMath 本地CI检查脚本 (Windows)

使用方法: .\scripts\ci-check.ps1 [选项]

选项:
    -Help              显示此帮助信息
    -Markdown          仅检查Markdown格式
    -Python            仅检查Python脚本
    -Links             检查链接有效性
    -Lean              检查Lean4代码
    -All               运行所有检查（包括链接和Lean）
    -Fix               自动修复可修复的问题
    -Verbose           显示详细输出
    -Quick             快速模式（仅关键检查）

示例:
    .\scripts\ci-check.ps1              # 运行默认检查
    .\scripts\ci-check.ps1 -All         # 运行所有检查
    .\scripts\ci-check.ps1 -Fix         # 自动修复格式问题
    .\scripts\ci-check.ps1 -Markdown -Python  # 仅检查Markdown和Python
"@
}

# 解析参数
function Initialize-Config {
    if ($Help) {
        Show-Help
        exit 0
    }
    
    if ($Markdown) {
        $Config.CheckPython = $false
        $Config.CheckLinks = $false
        $Config.CheckLean = $false
    }
    
    if ($Python) {
        $Config.CheckMarkdown = $false
        $Config.CheckLinks = $false
        $Config.CheckLean = $false
    }
    
    if ($Links) {
        $Config.CheckLinks = $true
    }
    
    if ($Lean) {
        $Config.CheckLean = $true
    }
    
    if ($All) {
        $Config.CheckLinks = $true
        $Config.CheckLean = $true
    }
    
    if ($Fix) {
        $Config.FixMode = $true
    }
    
    if ($Verbose) {
        $Config.Verbose = $true
        $VerbosePreference = 'Continue'
    }
    
    if ($Quick) {
        $Config.CheckLinks = $false
        $Config.CheckLean = $false
    }
}

# 打印标题
function Write-Header {
    param([string]$Message)
    Write-Host ""
    Write-Host "══════════════════════════════════════════════════════════════" -ForegroundColor $Colors.Blue
    Write-Host "  $Message" -ForegroundColor $Colors.Blue
    Write-Host "══════════════════════════════════════════════════════════════" -ForegroundColor $Colors.Blue
}

# 打印成功信息
function Write-Success {
    param([string]$Message)
    Write-Host "✅ $Message" -ForegroundColor $Colors.Green
}

# 打印警告信息
function Write-Warning {
    param([string]$Message)
    Write-Host "⚠️  $Message" -ForegroundColor $Colors.Yellow
    $script:Warnings++
}

# 打印错误信息
function Write-Error {
    param([string]$Message)
    Write-Host "❌ $Message" -ForegroundColor $Colors.Red
    $script:Errors++
}

# 打印信息
function Write-Info {
    param([string]$Message)
    if ($Config.Verbose) {
        Write-Host "  $Message"
    }
}

# 检查命令是否存在
function Test-Command {
    param([string]$Command)
    $null -ne (Get-Command $Command -ErrorAction SilentlyContinue)
}

# ==================== Markdown格式检查 ====================
function Test-Markdown {
    Write-Header "检查 Markdown 格式"
    
    if (Test-Command -Command "markdownlint") {
        Write-Host "🔍 使用 markdownlint 检查..."
        
        if ($Config.FixMode -and (Test-Command -Command "markdownlint-fix")) {
            Write-Host "  尝试自动修复..."
            markdownlint '**/*.md' --fix --ignore 'node_modules/**' --ignore '00-归档/**' --config .markdownlint.json 2>$null
        }
        
        $output = markdownlint '**/*.md' --ignore 'node_modules/**' --ignore '00-归档/**' --config .markdownlint.json 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Markdown格式检查通过"
        } else {
            Write-Warning "发现Markdown格式问题:"
            $output | Select-Object -First 20 | ForEach-Object { Write-Host "  $_" }
            if ($output.Count -gt 20) {
                Write-Host "  ... (还有 $($output.Count - 20) 个问题)"
            }
        }
    } else {
        Write-Host "⚠️  markdownlint 未安装，使用基础检查..." -ForegroundColor $Colors.Yellow
        Write-Host "   安装: npm install -g markdownlint-cli"
        
        # 基础检查
        $files = Get-ChildItem -Path . -Filter "*.md" -Recurse | 
                 Where-Object { $_.FullName -notmatch 'node_modules' -and $_.FullName -notmatch '00-归档' }
        
        $filesNoNewline = 0
        foreach ($file in $files) {
            $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
            if ($content -and -not $content.EndsWith("`n")) {
                Write-Info "$($file.Name) 缺少末尾空行"
                $filesNoNewline++
            }
        }
        
        if ($filesNoNewline -eq 0) {
            Write-Success "基础Markdown检查通过"
        } else {
            Write-Warning "$filesNoNewline 个文件缺少末尾空行"
        }
    }
}

# ==================== Python脚本检查 ====================
function Test-Python {
    Write-Header "检查 Python 脚本"
    
    $pythonCmd = if (Test-Command -Command "python") { "python" } elseif (Test-Command -Command "python3") { "python3" } else { $null }
    
    if (-not $pythonCmd) {
        Write-Error "Python 未安装"
        return
    }
    
    # 语法检查
    Write-Host "🔍 检查Python语法..."
    & $pythonCmd -m compileall tools/ -q 2>$null
    if ($LASTEXITCODE -eq 0) {
        Write-Success "Python语法检查通过"
    } else {
        Write-Error "发现Python语法错误"
    }
    
    # 检查flake8
    if (Test-Command -Command "flake8") {
        Write-Host "🔍 使用 flake8 检查代码风格..."
        $output = flake8 tools/ --count --select=E9,F63,F7,F82 --show-source --statistics 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Success "flake8基础检查通过"
        } else {
            Write-Warning "flake8发现代码风格问题"
        }
    } else {
        Write-Info "flake8 未安装，跳过代码风格检查"
        Write-Info "安装: pip install flake8"
    }
    
    # 检查black
    if (Test-Command -Command "black") {
        Write-Host "🔍 使用 Black 检查代码格式..."
        if ($Config.FixMode) {
            Write-Host "  自动格式化..."
            black tools/ --quiet 2>$null
            Write-Success "代码格式化完成"
        } else {
            $output = black --check --diff tools/ 2>$null
            if ($LASTEXITCODE -eq 0) {
                Write-Success "Black格式检查通过"
            } else {
                Write-Warning "代码格式不符合Black标准 (运行 -Fix 自动修复)"
            }
        }
    } else {
        Write-Info "black 未安装，跳过代码格式检查"
    }
    
    # 运行单元测试
    if ((Test-Path "tests") -and (Test-Command -Command "pytest")) {
        Write-Host "🧪 运行单元测试..."
        pytest tests/ -q --tb=short 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Success "单元测试通过"
        } else {
            Write-Error "单元测试失败"
        }
    }
}

# ==================== 链接检查 ====================
function Test-Links {
    Write-Header "检查链接有效性"
    
    if (Test-Path "tools\link_checker.py") {
        Write-Host "🔍 使用 link_checker.py 检查..."
        python tools\link_checker.py --internal-only 2>$null
        if ($LASTEXITCODE -eq 0) {
            Write-Success "内部链接检查通过"
        } else {
            Write-Warning "发现链接问题"
        }
    } else {
        # 基础链接检查
        Write-Host "🔍 运行基础链接检查..."
        
        $mdFiles = Get-ChildItem -Path . -Filter "*.md" -Recurse | 
                   Where-Object { $_.FullName -notmatch 'node_modules' -and $_.FullName -notmatch '00-归档' }
        
        $issues = @()
        $linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
        
        foreach ($file in $mdFiles) {
            $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
            if ($content) {
                $matches = [regex]::Matches($content, $linkPattern)
                foreach ($match in $matches) {
                    $link = $match.Groups[2].Value
                    if ($link -notmatch '^https?://' -and $link -notmatch '^#') {
                        $target = Join-Path $file.DirectoryName ($link -replace '^\./', '')
                        if (-not (Test-Path $target) -and -not (Test-Path "$target.md")) {
                            $issues += "$($file.FullName): 链接 '$link' 无效"
                        }
                    }
                }
            }
        }
        
        if ($issues.Count -gt 0) {
            Write-Warning "发现 $($issues.Count) 个链接问题:"
            $issues | Select-Object -First 10 | ForEach-Object { Write-Host "  - $_" }
            if ($issues.Count -gt 10) {
                Write-Host "  ... 还有 $($issues.Count - 10) 个问题"
            }
        } else {
            Write-Success "所有内部链接有效"
        }
    }
}

# ==================== Lean代码检查 ====================
function Test-Lean {
    Write-Header "检查 Lean4 代码"
    
    if (-not (Test-Command -Command "lean")) {
        Write-Warning "Lean4 未安装，跳过检查"
        Write-Info "安装: https://leanprover.github.io/lean4/doc/quickstart.html"
        return
    }
    
    Write-Host "🔍 编译Lean文件..."
    $failed = 0
    $leanFiles = Get-ChildItem -Path . -Filter "*.lean" -Recurse -ErrorAction SilentlyContinue | 
                 Where-Object { $_.FullName -notmatch '\.lake' }
    
    foreach ($file in $leanFiles) {
        lean $file.FullName 2>$null
        if ($LASTEXITCODE -ne 0) {
            Write-Error "编译失败: $($file.Name)"
            $failed++
        }
    }
    
    if ($failed -eq 0) {
        Write-Success "所有Lean文件编译成功"
    } else {
        Write-Error "$failed 个Lean文件编译失败"
    }
}

# ==================== 主程序 ====================
function Main {
    Write-Host ""
    Write-Host "╔══════════════════════════════════════════════════════════════╗" -ForegroundColor $Colors.Blue
    Write-Host "║          FormalMath 本地CI检查                              ║" -ForegroundColor $Colors.Blue
    Write-Host "╚══════════════════════════════════════════════════════════════╝" -ForegroundColor $Colors.Blue
    Write-Host ""
    
    Initialize-Config
    
    # 获取项目根目录
    $scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
    Set-Location (Join-Path $scriptDir "..")
    
    Write-Host "📁 工作目录: $(Get-Location)"
    Write-Host ""
    
    # 运行各项检查
    if ($Config.CheckMarkdown) {
        Test-Markdown
    }
    
    if ($Config.CheckPython) {
        Test-Python
    }
    
    if ($Config.CheckLinks) {
        Test-Links
    }
    
    if ($Config.CheckLean) {
        Test-Lean
    }
    
    # 输出汇总
    Write-Host ""
    Write-Host "══════════════════════════════════════════════════════════════" -ForegroundColor $Colors.Blue
    Write-Host "  检查完成" -ForegroundColor $Colors.Blue
    Write-Host "══════════════════════════════════════════════════════════════" -ForegroundColor $Colors.Blue
    Write-Host ""
    
    if ($script:Errors -eq 0 -and $script:Warnings -eq 0) {
        Write-Host "🎉 所有检查通过！可以安全提交。" -ForegroundColor $Colors.Green
        exit 0
    } else {
        if ($script:Errors -gt 0) {
            Write-Host "❌ 发现 $script:Errors 个错误" -ForegroundColor $Colors.Red
        }
        if ($script:Warnings -gt 0) {
            Write-Host "⚠️  发现 $script:Warnings 个警告" -ForegroundColor $Colors.Yellow
        }
        Write-Host ""
        if ($script:Errors -gt 0) {
            Write-Host "请修复错误后再提交。" -ForegroundColor $Colors.Red
            exit 1
        } else {
            Write-Host "建议修复警告，但不是必须。" -ForegroundColor $Colors.Yellow
            exit 0
        }
    }
}

# 运行主程序
Main
