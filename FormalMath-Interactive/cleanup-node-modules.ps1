# FormalMath node_modules 清理脚本
# 清理不必要的文档、示例、测试文件
# 注意：保留核心代码文件和必要的类型定义

param(
    [string]$Path = "./node_modules",
    [switch]$DryRun = $false
)

$startTime = Get-Date
$stats = @{
    FilesDeleted = 0
    DirsDeleted = 0
    BytesFreed = 0
    Errors = @()
}

# 定义要清理的文件模式（在子目录中的文档文件）
$filePatterns = @(
    "CHANGELOG*",
    "HISTORY*",
    "CHANGES*",
    "AUTHORS*",
    "CONTRIBUTORS*",
    "PATENTS*",
    "NOTICE*",
    "CODE_OF_CONDUCT*",
    "GOVERNANCE*",
    ".travis.yml",
    ".appveyor.yml",
    ".github",
    ".gitattributes",
    ".gitignore",
    ".editorconfig",
    ".eslintrc*",
    ".prettierrc*",
    ".babelrc*",
    ".tern-project",
    ".jshintrc",
    ".flowconfig",
    "tsconfig.json",
    "jsconfig.json",
    "webpack.config.js",
    "rollup.config.js",
    "gulpfile.js",
    "Gruntfile.js",
    "*.map",           # Source map files
    "*.test.js",       # Test files
    "*.spec.js",
    "*.test.ts",
    "*.spec.ts",
    "*.test.tsx",
    "*.spec.tsx",
    "*.min.js.map",    # Minified source maps
    "*.ts",            # TypeScript source (keep .d.ts)
    "*.tsx",
    "*.flow",
    "*.coffee",        # CoffeeScript source
    "*.ls",            # LiveScript source
    "*.jst",           # Underscore templates
    "*.ejs",           # EJS templates
    "*.swp",           # Vim swap files
    "*.swo",
    "*~",              # Backup files
    "*.orig",          # Merge conflict files
    "*.rej",
    ".DS_Store",       # macOS files
    "Thumbs.db",       # Windows files
    "desktop.ini",
    ".npmignore",
    ".jscsrc",
    ".jshintignore",
    ".eslintignore",
    ".prettierignore",
    ".mocharc*",
    ".nycrc*",
    ".istanbul*",
    "jest.config*",
    "karma.conf*",
    "protractor.conf*",
    "angular.json",
    "vue.config.js",
    "svelte.config.js"
)

# 定义要保留的文件（排除在根目录的README和LICENSE）
$keepPatterns = @(
    "package.json",    # 必须保留
    "*.d.ts",          # TypeScript声明文件
    "*.js",            # JavaScript代码
    "*.mjs",           # ES模块
    "*.cjs",           # CommonJS模块
    "*.json",          # JSON配置（除特定文件外）
    "*.node",          # Native模块
    "*.wasm",          # WebAssembly
    "*.css",           # CSS样式
    "*.scss",
    "*.less",
    "*.sass",
    "*.png",           # 图片资源
    "*.jpg",
    "*.jpeg",
    "*.gif",
    "*.svg",
    "*.ico",
    "*.woff",          # 字体
    "*.woff2",
    "*.ttf",
    "*.eot",
    "*.otf"
)

# 定义要清理的目录
$dirPatterns = @(
    "test",
    "tests",
    "__tests__",
    "__mocks__",
    "spec",
    "specs",
    "docs",
    "doc",
    "documentation",
    "example",
    "examples",
    "demo",
    "demos",
    "sample",
    "samples",
    "benchmark",
    "benchmarks",
    "perf",
    "performance",
    "coverage",
    ".nyc_output",
    ".coverage",
    "node_modules/.cache",  # 缓存目录
    ".github",
    ".git",
    ".svn",
    ".hg",
    "website",
    "site",
    "manual",
    "guide",
    "guides",
    "tutorial",
    "tutorials",
    "storybook",
    ".storybook",
    ".vuepress",
    ".docusaurus",
    ".next",           # Next.js build (if in package)
    "dist",            # Build output (may be needed)
    "build"            # Build output (may be needed)
)

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "FormalMath node_modules 清理脚本" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "目标路径: $Path" -ForegroundColor Yellow
Write-Host "模式: $(if ($DryRun) { '预览模式 (不会删除)' } else { '执行模式' })" -ForegroundColor Yellow
Write-Host ""

# 获取所有包目录
$packageDirs = Get-ChildItem -Path $Path -Directory -ErrorAction SilentlyContinue
Write-Host "发现 $($packageDirs.Count) 个包目录" -ForegroundColor Green
Write-Host ""

# 处理每个包
foreach ($packageDir in $packageDirs) {
    $packageName = $packageDir.Name
    Write-Host "处理包: $packageName" -ForegroundColor Gray
    
    # 1. 清理文件（递归）
    foreach ($pattern in $filePatterns) {
        $files = Get-ChildItem -Path $packageDir.FullName -Recurse -File -Filter $pattern -ErrorAction SilentlyContinue
        foreach ($file in $files) {
            # 检查是否是根目录的README或LICENSE（保留）
            $relativePath = $file.FullName.Substring($packageDir.FullName.Length + 1)
            $isRootLevel = ($relativePath -split '[\\/]').Length -eq 1
            
            # 保留根目录的README和LICENSE
            if ($isRootLevel -and ($file.Name -match "^(README|LICENSE|LICENCE)")) {
                continue
            }
            
            # 保留 .d.ts 文件
            if ($file.Name -match "\.d\.ts$") {
                continue
            }
            
            if ($DryRun) {
                Write-Host "  [预览] 将删除文件: $relativePath" -ForegroundColor DarkGray
            } else {
                try {
                    $size = $file.Length
                    Remove-Item -Path $file.FullName -Force -ErrorAction Stop
                    $stats.FilesDeleted++
                    $stats.BytesFreed += $size
                } catch {
                    $stats.Errors += "无法删除文件: $($file.FullName) - $($_.Exception.Message)"
                }
            }
        }
    }
    
    # 2. 清理目录
    foreach ($pattern in $dirPatterns) {
        $dirs = Get-ChildItem -Path $packageDir.FullName -Recurse -Directory -Filter $pattern -ErrorAction SilentlyContinue
        # 按深度排序，先删除深层目录
        $sortedDirs = $dirs | Sort-Object { $_.FullName.Split([IO.Path]::DirectorySeparatorChar).Length } -Descending
        
        foreach ($dir in $sortedDirs) {
            $relativePath = $dir.FullName.Substring($packageDir.FullName.Length + 1)
            
            # 跳过 node_modules 内部的 node_modules（那是依赖的依赖）
            if ($relativePath -like "*node_modules*") {
                continue
            }
            
            if ($DryRun) {
                # 计算目录大小
                $size = (Get-ChildItem -Path $dir.FullName -Recurse -File -ErrorAction SilentlyContinue | Measure-Object -Property Length -Sum).Sum
                Write-Host "  [预览] 将删除目录: $relativePath ({0:N2} MB)" -f ($size / 1MB) -ForegroundColor DarkGray
            } else {
                try {
                    $size = (Get-ChildItem -Path $dir.FullName -Recurse -File -ErrorAction SilentlyContinue | Measure-Object -Property Length -Sum).Sum
                    Remove-Item -Path $dir.FullName -Recurse -Force -ErrorAction Stop
                    $stats.DirsDeleted++
                    $stats.BytesFreed += $size
                } catch {
                    $stats.Errors += "无法删除目录: $($dir.FullName) - $($_.Exception.Message)"
                }
            }
        }
    }
}

# 输出统计
Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "清理完成统计" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "模式: $(if ($DryRun) { '预览模式' } else { '执行模式' })" -ForegroundColor Yellow
Write-Host "删除文件数: $($stats.FilesDeleted)" -ForegroundColor $(if ($stats.FilesDeleted -gt 0) { 'Green' } else { 'Gray' })
Write-Host "删除目录数: $($stats.DirsDeleted)" -ForegroundColor $(if ($stats.DirsDeleted -gt 0) { 'Green' } else { 'Gray' })
Write-Host "释放空间: {0:N2} MB ({1:N2} GB)" -f ($stats.BytesFreed / 1MB), ($stats.BytesFreed / 1GB) -ForegroundColor Green

if ($stats.Errors.Count -gt 0) {
    Write-Host ""
    Write-Host "错误 ($($stats.Errors.Count)):" -ForegroundColor Red
    $stats.Errors | Select-Object -First 10 | ForEach-Object { Write-Host "  - $_" -ForegroundColor Red }
    if ($stats.Errors.Count -gt 10) {
        Write-Host "  ... 还有 $($stats.Errors.Count - 10) 个错误" -ForegroundColor Red
    }
}

$endTime = Get-Date
$duration = $endTime - $startTime
Write-Host ""
Write-Host "耗时: {0:N2} 秒" -f $duration.TotalSeconds -ForegroundColor Cyan

# 返回统计
return $stats
