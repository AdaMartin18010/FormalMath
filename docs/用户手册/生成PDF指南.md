---
msc_primary: 00

  - 00A99
title: FormalMath 用户手册 - PDF 生成指南
processed_at: '2026-04-05'
---
# FormalMath 用户手册 - PDF 生成指南

**版本**: v1.0  
**发布日期**: 2026年4月4日

---

## 方法一：使用 Pandoc（推荐）

### 安装 Pandoc

**Windows**:
```powershell
# 使用 chocolatey
choco install pandoc

# 或使用 msi 安装包
# 下载地址: https://pandoc.org/installing.html[需更新[需更新]]
```

**macOS**:
```bash
brew install pandoc
```

**Linux**:
```bash
# Ubuntu/Debian
sudo apt-get install pandoc

# Fedora
sudo dnf install pandoc
```

### 安装 LaTeX（用于高质量 PDF）

**Windows**:
```powershell
# 使用 chocolatey
choco install miktex
```

**macOS**:
```bash
brew install --cask mactex
```

**Linux**:
```bash
sudo apt-get install texlive-full
```

### 生成 PDF

```bash
# 基础转换
pandoc README.md 01-快速开始指南.md 02-功能使用说明.md 03-学习路径指南.md 04-常见问题解答.md 05-故障排除指南.md -o 用户手册.pdf

# 带目录的高质量版本
pandoc README.md \
  01-快速开始指南.md \
  02-功能使用说明.md \
  03-学习路径指南.md \
  04-常见问题解答.md \
  05-故障排除指南.md \
  -o 用户手册.pdf \
  --pdf-engine=xelatex \
  -V CJKmainfont="SimSun" \
  -V geometry:margin=2.5cm \
  --toc \
  --toc-depth=3 \
  -V colorlinks=true \
  -V linkcolor=blue

# 简化版本（无需 LaTeX）
pandoc *.md -o 用户手册.pdf --pdf-engine=wkhtmltopdf
```

---

## 方法二：使用 wkhtmltopdf

### 安装 wkhtmltopdf

下载地址: https://wkhtmltopdf.org/downloads.html[需更新[需更新]]

### 生成步骤

```bash
# 1. 先转换为 HTML
pandoc README.md 01-*.md 02-*.md 03-*.md 04-*.md 05-*.md -o 用户手册.html --standalone --toc

# 2. 转换为 PDF
wkhtmltopdf --enable-local-file-access \
  --page-size A4 \
  --margin-top 20mm \
  --margin-bottom 20mm \
  --margin-left 20mm \
  --margin-right 20mm \
  --encoding utf-8 \
  --footer-center "[page]/[topage]" \
  用户手册.html 用户手册.pdf
```

---

## 方法三：使用 Python

### 安装依赖

```bash
pip install markdown weasyprint
```

### Python 脚本

```python
import markdown
from weasyprint import HTML, CSS

# 读取所有 Markdown 文件
files = [
    'README.md',
    '01-快速开始指南.md',
    '02-功能使用说明.md',
    '03-学习路径指南.md',
    '04-常见问题解答.md',
    '05-故障排除指南.md'
]

content = []
for f in files:
    with open(f, 'r', encoding='utf-8') as file:
        content.append(file.read())

# 合并并转换为 HTML
md_text = '\n\n---\n\n'.join(content)
html_text = markdown.markdown(md_text, extensions=['tables', 'fenced_code', 'toc'])

# 添加样式
html_full = f'''
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<style>
    body {{
        font-family: "Segoe UI", "Microsoft YaHei", sans-serif;
        line-height: 1.6;
        max-width: 800px;
        margin: 0 auto;
        padding: 20px;
    }}
    h1, h2, h3 {{
        color: #2c3e50;
    }}
    code {{
        background: #f4f4f4;
        padding: 2px 5px;
        border-radius: 3px;
    }}
    pre {{
        background: #f4f4f4;
        padding: 15px;
        border-radius: 5px;
        overflow-x: auto;
    }}
    table {{
        border-collapse: collapse;
        width: 100%;
    }}
    th, td {{
        border: 1px solid #ddd;
        padding: 8px;
    }}
    th {{
        background: #f2f2f2;
    }}
</style>
</head>
<body>
{html_text}
</body>
</html>
'''

# 保存 HTML
with open('用户手册.html', 'w', encoding='utf-8') as f:
    f.write(html_full)

# 转换为 PDF
HTML('用户手册.html').write_pdf('用户手册.pdf')
print("PDF 生成完成！")
```

---

## 方法四：使用 VS Code 插件

### 推荐插件

1. **Markdown PDF**
   - 安装: 在 VS Code 扩展商店搜索 "Markdown PDF"
   - 使用: 打开 Markdown 文件 → 右键 → "Markdown PDF: Export (pdf)"

2. **Markdown Preview Enhanced**
   - 安装: 搜索 "Markdown Preview Enhanced"
   - 使用: 预览 → 右键 → "Chrome (Puppeteer) / PDF"

---

## 方法五：使用在线工具

### 推荐在线转换器

1. **md2pdf.netlify.app**
   - 直接粘贴 Markdown 内容
   - 在线生成 PDF

2. **Pandoc Try**
   - https://pandoc.org/try/[需更新[需更新]]
   - 在线测试转换效果

---

## 单文件 Markdown 版本

我们也提供了合并后的单文件 Markdown 版本，方便打印和分享：

**文件**: `用户手册-完整版.md`

此版本包含：
- 所有五章内容
- 完整目录结构
- 优化的内部链接

---

## PDF 生成建议

### 打印设置

- **纸张**: A4
- **边距**: 上下 20mm，左右 25mm
- **字体大小**: 正文 11pt，标题 14-18pt
- **行距**: 1.5 倍

### 阅读优化

- **目录**: 确保包含目录，方便导航
- **页码**: 添加页眉/页脚
- **链接**: 保留彩色链接，方便电子阅读
- **书签**: 生成 PDF 书签，便于跳转

---

## 故障排除

### 中文显示问题

如果使用 LaTeX 生成 PDF 时中文显示为方块：

```bash
# 指定中文字体
pandoc input.md -o output.pdf --pdf-engine=xelatex -V CJKmainfont="SimSun"

# 或使用其他字体
pandoc input.md -o output.pdf --pdf-engine=xelatex -V CJKmainfont="Noto Sans CJK SC"
```

### 表格换行问题

```bash
# 使用 longtable 包
pandoc input.md -o output.pdf --pdf-engine=xelatex -V classoption=table
```

### 代码块换行

```bash
# 使用 listings 包处理代码
pandoc input.md -o output.pdf --listings --pdf-engine=xelatex
```

---

**如有问题，请参考**：[05-故障排除指南.md](./05-故障排除指南.md)
