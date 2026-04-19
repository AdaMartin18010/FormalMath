---
title: FormalMath 知识图谱导出工具使用文档
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 知识图谱导出工具使用文档

## 概述

`export_graph.py` 是一个功能强大的知识图谱多格式导出工具，支持将概念图谱数据导出为多种常用格式，便于分享、打印和进一步分析。

## 功能特性

| 格式 | 扩展名 | 用途 | 依赖 |
|------|--------|------|------|
| JSON | `.json` | 数据交换、程序处理 | 无 |
| CSV | `.csv` | 表格分析、Excel处理 | 无 |
| GraphML | `.graphml` | Gephi/Cytoscape网络分析 | 无 |
| HTML | `.html` | 交互式网页、浏览器查看 | 无 |
| SVG | `.svg` | 矢量图、网页嵌入 | 无 |
| PNG | `.png` | 位图、演示文稿 | CairoSVG 或 Pillow |
| PDF | `.pdf` | 打印、分享、存档 | Playwright 或 ReportLab |

## 安装

### 基础安装

```bash
cd tools/knowledge-graph-exporter
pip install -r requirements.txt
```

### 完整依赖安装（推荐）

```bash
# 安装所有依赖
pip install playwright pyyaml reportlab cairosvg pillow

# 安装 Playwright Chromium 浏览器
playwright install chromium
```

### 依赖说明

| 依赖 | 用途 | 是否必需 |
|------|------|----------|
| `playwright` | PDF导出（推荐，渲染效果好） | 可选 |
| `pyyaml` | YAML文件读取 | 可选 |
| `reportlab` | PDF导出（备选） | 可选 |
| `cairosvg` | PNG导出（质量更好） | 可选 |
| `pillow` | PNG导出（备选）、图片处理 | 可选 |

## 命令行使用

### 基本用法

```bash
# 导出所有格式
python export_graph.py -i data.json -o ./output

# 从YAML文件导出
python export_graph.py -i concept_prerequisites.yaml -o ./export

# 只导出特定格式
python export_graph.py -i data.json -f json csv pdf

# 指定图片尺寸
python export_graph.py -i data.json -f svg png -W 1600 -H 1200

# 显示帮助
python export_graph.py --help
```

### 参数说明

| 参数 | 简写 | 说明 | 默认值 |
|------|------|------|--------|
| `--input` | `-i` | 输入文件路径 (JSON/YAML) | **必需** |
| `--output` | `-o` | 输出目录 | `output/export` |
| `--formats` | `-f` | 导出格式列表 | `all` |
| `--width` | `-W` | 图片宽度 (像素) | `1200` |
| `--height` | `-H` | 图片高度 (像素) | `800` |
| `--version` | `-v` | 显示版本信息 | - |

### 格式选项

- `json` - JSON数据格式
- `csv` - CSV表格格式（生成 nodes.csv, edges.csv, statistics.csv）
- `graphml` - GraphML网络图格式
- `html` - 交互式HTML网页
- `svg` - SVG矢量图形
- `png` - PNG位图
- `pdf` - PDF文档
- `all` - 导出所有格式

## Python API 使用

### 基础用法

```python
from export_graph import GraphExporter
from pathlib import Path

# 创建导出器
exporter = GraphExporter(output_dir=Path("output"))

# 加载数据
exporter.load_from_json(Path("data.json"))
# 或
exporter.load_from_yaml(Path("data.yaml"))

# 导出所有格式
results = exporter.export_all()

# 导出特定格式
exporter.export_json()
exporter.export_csv()
exporter.export_graphml()
exporter.export_html()
exporter.export_svg(width=1600, height=1200)
exporter.export_png(width=1600, height=1200)

# PDF导出（异步）
import asyncio
asyncio.run(exporter.export_pdf_playwright())

# 或使用ReportLab（同步）
exporter.export_pdf_reportlab()
```

### 高级用法

```python
import asyncio
from export_graph import GraphExporter

# 创建导出器并加载数据
exporter = GraphExporter(output_dir="my_export")
exporter.load_from_json("project/visualization_data.json")

# 自定义HTML导出（不包含图谱可视化）
exporter.export_html(
    output_path="my_export/simple.html",
    include_graph=False
)

# 导出高质量PNG
exporter.export_png(
    output_path="my_export/poster.png",
    width=2400,
    height=1600
)

# 使用Playwright导出PDF（推荐）
async def export_high_quality_pdf():
    await exporter.export_pdf_playwright(
        output_path="my_export/document.pdf"
    )

asyncio.run(export_high_quality_pdf())
```

## 输入数据格式

### JSON 格式

```json
{
  "metadata": {
    "version": "1.0",
    "generated_date": "2026-04-04T12:00:00"
  },
  "nodes": [
    {
      "id": "C001",
      "label": "群论",
      "category": "代数学",
      "difficulty": 2,
      "estimated_hours": 20,
      "msc_code": "20-XX",
      "description": "群的定义与基本性质"
    }
  ],
  "edges": [
    {
      "from": "C000",
      "to": "C001",
      "label": "依赖",
      "level": "L1"
    }
  ]
}
```

### YAML 格式

```yaml
version: "2.0"
concepts:
  - concept_id: "C001"
    name: "群论"
    category: "代数学"
    difficulty: 2
    estimated_hours: 20
    msc_code: "20-XX"
    description: "群的定义与基本性质"
    prerequisites:
      - concept_id: "C000"
        relation: "依赖"
        level: "L1"
```

## 输出文件说明

### 1. JSON 导出 (`knowledge_graph.json`)

包含完整的节点和边数据，添加了导出元信息。

```json
{
  "metadata": {
    "version": "1.0",
    "export_date": "2026-04-04T12:00:00",
    "total_nodes": 150,
    "total_edges": 280
  },
  "nodes": [...],
  "edges": [...]
}
```

### 2. CSV 导出 (`csv_export/`)

生成三个CSV文件：

- `nodes.csv` - 概念节点数据
- `edges.csv` - 关系边数据  
- `statistics.csv` - 统计汇总

### 3. GraphML 导出 (`knowledge_graph.graphml`)

Gephi/Cytoscape兼容的网络图格式，包含：
- 节点颜色属性
- 类别标签
- 难度级别
- 预计学时

### 4. HTML 导出 (`knowledge_graph.html`)

交互式网页，包含：
- 响应式布局
- 统计概览
- 概念列表
- 力导向图谱可视化
- 打印优化样式
- 一键导出JSON/CSV按钮

### 5. SVG 导出 (`knowledge_graph.svg`)

矢量图形格式，包含：
- 力导向布局
- 类别颜色编码
- 节点大小反映难度
- 带阴影效果的图例

### 6. PNG 导出 (`knowledge_graph.png`)

位图格式，适用于：
- 演示文稿
- 文档插图
- 社交媒体分享

### 7. PDF 导出 (`knowledge_graph.pdf`)

打印优化的PDF文档，包含：
- A4页面布局
- 页眉页脚
- 自动分页
- 统计表格
- 概念详情

## 打印优化

HTML导出包含专门的打印优化CSS：

```css
@media print {
  @page {
    size: A4;
    margin: 1.5cm;
  }
  /* 自动分页控制 */
  /* 颜色精确还原 */
  /* 隐藏交互元素 */
}
```

在浏览器中打开HTML文件，按 `Ctrl+P` (Windows) 或 `Cmd+P` (Mac) 即可打印。

## 类别颜色映射

| 类别 | 颜色代码 | 预览 |
|------|----------|------|
| 分析学 | #E3F2FD | ![分析学](https://via.placeholder.com/15/E3F2FD/000000?text=+) |
| 代数学 | #F3E5F5 | ![代数学](https://via.placeholder.com/15/F3E5F5/000000?text=+) |
| 几何拓扑 | #E8F5E9 | ![几何拓扑](https://via.placeholder.com/15/E8F5E9/000000?text=+) |
| 数论逻辑 | #FBE9E7 | ![数论逻辑](https://via.placeholder.com/15/FBE9E7/000000?text=+) |
| 概率统计 | #FFF8E1 | ![概率统计](https://via.placeholder.com/15/FFF8E1/000000?text=+) |
| 最优化 | #E0F2F1 | ![最优化](https://via.placeholder.com/15/E0F2F1/000000?text=+) |
| 控制论 | #E1F5FE | ![控制论](https://via.placeholder.com/15/E1F5FE/000000?text=+) |
| 信息论 | #F3E5F5 | ![信息论](https://via.placeholder.com/15/F3E5F5/000000?text=+) |
| 密码学 | #ECEFF1 | ![密码学](https://via.placeholder.com/15/ECEFF1/000000?text=+) |

## 故障排除

### Playwright 未安装

```bash
pip install playwright
playwright install chromium
```

### PDF 导出失败

**方案1：使用 Playwright（推荐）**
```bash
pip install playwright
playwright install chromium
```

**方案2：使用 ReportLab（备选）**
```bash
pip install reportlab
```

### PNG 导出质量不佳

**方案1：使用 CairoSVG（推荐）**
```bash
pip install cairosvg
```

**方案2：使用 Pillow（备选）**
```bash
pip install pillow
```

### 中文显示问题

确保系统安装了中文字体：
- **Windows**: 微软雅黑、宋体
- **macOS**: 华文细黑、苹方
- **Linux**: Noto Sans CJK

### YAML 文件无法读取

```bash
pip install pyyaml
```

## 示例脚本

### 批量导出脚本

```bash
#!/bin/bash
# batch_export.sh

INPUT_FILE="../../project/concept_prerequisites.yaml"
OUTPUT_DIR="./batch_output"

# 导出所有格式
python export_graph.py -i "$INPUT_FILE" -o "$OUTPUT_DIR/all" -f all

# 导出适合打印的版本
python export_graph.py -i "$INPUT_FILE" -o "$OUTPUT_DIR/print" -f pdf html

# 导出适合网页嵌入的版本
python export_graph.py -i "$INPUT_FILE" -o "$OUTPUT_DIR/web" -f svg png json

echo "批量导出完成!"
```

### Python 批处理脚本

```python
#!/usr/bin/env python3
# batch_export.py

from export_graph import GraphExporter
from pathlib import Path

# 处理多个文件
files = [
    "project/concept_prerequisites.yaml",
    "project/visualization_data.json"
]

for file in files:
    print(f"\n处理: {file}")
    exporter = GraphExporter(output_dir=f"output/{Path(file).stem}")
    
    if file.endswith('.json'):
        exporter.load_from_json(file)
    else:
        exporter.load_from_yaml(file)
    
    results = exporter.export_all(['pdf', 'html', 'svg'])
    print(f"完成: {len(results)} 个文件")
```

## 更新日志

### v2.0.0
- 新增 Playwright PDF 导出（渲染效果更好）
- 新增交互式 HTML 导出
- 优化打印样式
- 添加 CLI 参数支持
- 改进力导向布局算法

### v1.0.0
- 初始版本发布
- 支持 JSON、CSV、GraphML、SVG、PNG、PDF 导出

## 许可

MIT License - 参见项目主 LICENSE 文件
