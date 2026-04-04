#!/usr/bin/env pwsh
# FormalMath 文档自动生成 PowerShell 脚本
# 一键运行所有文档生成任务

param(
    [string]$OutputDir = "docs/generated",
    [switch]$ApiOnly,
    [switch]$ConceptsOnly,
    [switch]$Lean4Only,
    [switch]$I18nOnly,
    [switch]$Verbose,
    [switch]$Help
)

# 显示帮助
if ($Help) {
    Write-Host @"
FormalMath 文档自动生成脚本

用法: .\generate-all-docs.ps1 [选项]

选项:
    -OutputDir <路径>    指定输出目录 (默认: docs/generated)
    -ApiOnly             只生成API文档
    -ConceptsOnly        只生成概念图谱
    -Lean4Only           只生成Lean4文档
    -I18nOnly            只生成国际化文档
    -Verbose             显示详细输出
    -Help                显示此帮助信息

示例:
    # 生成所有文档
    .\generate-all-docs.ps1

    # 只生成API文档
    .\generate-all-docs.ps1 -ApiOnly

    # 指定输出目录
    .\generate-all-docs.ps1 -OutputDir ./my-docs -Verbose
"@
    exit 0
}

# 设置错误处理
$ErrorActionPreference = "Continue"

# 获取脚本所在目录
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProjectRoot = Split-Path -Parent $ScriptDir

Write-Host "========================================"
Write-Host "FormalMath 文档自动生成系统"
Write-Host "========================================"
Write-Host ""

# 检查Python
$PythonCmd = Get-Command python -ErrorAction SilentlyContinue
if (-not $PythonCmd) {
    $PythonCmd = Get-Command python3 -ErrorAction SilentlyContinue
}

if (-not $PythonCmd) {
    Write-Error "错误: 未找到Python。请安装Python 3.8或更高版本。"
    exit 1
}

Write-Host "Python版本:"
& $PythonCmd.Source --version
Write-Host ""

# 构建参数
$Args = @()

if ($ApiOnly) { $Args += "--api-only" }
if ($ConceptsOnly) { $Args += "--concepts-only" }
if ($Lean4Only) { $Args += "--lean4-only" }
if ($I18nOnly) { $Args += "--i18n-only" }
if ($Verbose) { $Args += "--verbose" }

$Args += "--output"
$Args += $OutputDir

# 切换到项目根目录
Set-Location $ProjectRoot

Write-Host "工作目录: $(Get-Location)"
Write-Host "输出目录: $OutputDir"
Write-Host "参数: $Args"
Write-Host ""

# 运行文档生成器
$DocGenerator = Join-Path $ScriptDir "doc-generator\generate_docs.py"

if (-not (Test-Path $DocGenerator)) {
    Write-Error "错误: 找不到文档生成器: $DocGenerator"
    exit 1
}

Write-Host "开始生成文档..."
Write-Host "========================================"

$StartTime = Get-Date

try {
    & $PythonCmd.Source $DocGenerator $Args
    
    if ($LASTEXITCODE -ne 0) {
        Write-Error "文档生成失败，退出代码: $LASTEXITCODE"
        exit $LASTEXITCODE
    }
}
catch {
    Write-Error "执行失败: $_"
    exit 1
}

$EndTime = Get-Date
$Duration = $EndTime - $StartTime

Write-Host ""
Write-Host "========================================"
Write-Host "文档生成完成!"
Write-Host "========================================"
Write-Host "开始时间: $($StartTime.ToString('yyyy-MM-dd HH:mm:ss'))"
Write-Host "结束时间: $($EndTime.ToString('yyyy-MM-dd HH:mm:ss'))"
Write-Host "总耗时: $($Duration.TotalSeconds.ToString('F2')) 秒"
Write-Host ""

# 显示输出文件
$OutputPath = Join-Path $ProjectRoot $OutputDir
if (Test-Path $OutputPath) {
    $Files = Get-ChildItem $OutputPath -Recurse -File | Select-Object -First 20
    
    Write-Host "生成的文件 (前20个):"
    foreach ($File in $Files) {
        $RelativePath = $File.FullName.Replace($ProjectRoot, "").TrimStart("\", "/")
        Write-Host "  - $RelativePath"
    }
    
    $TotalFiles = (Get-ChildItem $OutputPath -Recurse -File).Count
    Write-Host ""
    Write-Host "总文件数: $TotalFiles"
}

Write-Host ""
Write-Host "主索引: $OutputDir/index.md"
Write-Host ""

# 可选: 自动打开索引文件
# Invoke-Item (Join-Path $OutputPath "index.md")
