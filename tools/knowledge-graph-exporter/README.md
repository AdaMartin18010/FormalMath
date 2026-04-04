# FormalMath 知识图谱多格式导出工具

强大的知识图谱导出工具，支持多种格式导出，便于分享、打印和进一步分析。

## ✨ 功能特性

| 格式 | 文件名 | 用途 | 状态 |
|------|--------|------|------|
| 📄 JSON | `knowledge_graph.json` | 数据交换、程序处理 | ✅ |
| 📊 CSV | `csv_export/*.csv` | 表格分析、Excel处理 | ✅ |
| 🕸️ GraphML | `knowledge_graph.graphml` | Gephi/Cytoscape网络分析 | ✅ |
| 🌐 HTML | `knowledge_graph.html` | 交互式网页、浏览器查看 | ✅ |
| 🎨 SVG | `knowledge_graph.svg` | 矢量图、网页嵌入 | ✅ |
| 🖼️ PNG | `knowledge_graph.png` | 位图、演示文稿 | ✅ |
| 📑 PDF | `knowledge_graph.pdf` | 打印、分享、存档 | ✅ |

## 🚀 快速开始

### 安装

```bash
cd tools/knowledge-graph-exporter

# 基础安装（仅JSON/CSV/GraphML/HTML/SVG）
pip install -r requirements.txt

# 完整安装（包含PDF/PNG高级导出）
pip install playwright pyyaml reportlab cairosvg pillow
playwright install chromium
```

### 基础用法

```bash
# 导出所有格式
python export_graph.py -i data.json -o ./output

# 从YAML导出
python export_graph.py -i concept_prerequisites.yaml -o ./export

# 只导出PDF和PNG
python export_graph.py -i data.json -f pdf png -W 1600 -H 1200
```

### 使用项目数据

```bash
# 从FormalMath项目概念数据导出
python export_graph.py -i ../../project/concept_prerequisites.yaml -o ./output
```

## 📖 详细文档

- **[使用文档](USAGE.md)** - 完整的使用指南和API参考
- **[示例数据](example_data.json)** - 示例输入数据格式

## 🛠️ 依赖说明

| 依赖 | 用途 | 优先级 |
|------|------|--------|
| `playwright` | PDF导出（高质量渲染） | ⭐⭐⭐ 推荐 |
| `reportlab` | PDF导出（备选） | ⭐⭐ 备选 |
| `cairosvg` | PNG导出（高质量） | ⭐⭐⭐ 推荐 |
| `pillow` | PNG导出/PDF备选 | ⭐⭐ 备选 |
| `pyyaml` | YAML文件读取 | ⭐⭐⭐ 推荐 |

## 📁 输出示例

```
output/
├── knowledge_graph.json      # 完整数据
├── csv_export/
│   ├── nodes.csv             # 概念节点
│   ├── edges.csv             # 关系边
│   └── statistics.csv        # 统计汇总
├── knowledge_graph.graphml   # Gephi兼容格式
├── knowledge_graph.html      # 交互式网页
├── knowledge_graph.svg       # 矢量图
├── knowledge_graph.png       # 位图
└── knowledge_graph.pdf       # PDF文档
```

## 🎯 核心特性

- **多格式支持** - 7种导出格式，满足不同场景需求
- **打印优化** - PDF和HTML针对A4打印优化
- **交互式网页** - HTML包含力导向图谱可视化
- **高质量渲染** - 使用Playwright生成精美PDF
- **零依赖基础** - 核心功能仅需Python标准库
- **灵活配置** - 支持自定义图片尺寸、布局等

## 🔧 Python API

```python
from export_graph import GraphExporter

# 创建导出器
exporter = GraphExporter(output_dir="output")

# 加载数据
exporter.load_from_json("data.json")

# 导出所有格式
results = exporter.export_all()

# 导出特定格式
exporter.export_pdf_playwright()  # 高质量PDF
exporter.export_svg(width=1600, height=1200)  # 自定义尺寸SVG
```

## 📚 相关文件

| 文件 | 说明 |
|------|------|
| `export_graph.py` | 主导出工具 |
| `knowledge_graph_exporter.py` | 原版导出器（向后兼容）|
| `html_exporter.py` | HTML导出器 |
| `print.css` | 打印优化样式表 |
| `requirements.txt` | Python依赖 |
| `USAGE.md` | 详细使用文档 |

## 📄 许可

MIT License - 参见项目主 LICENSE 文件

---

**FormalMath Project** | 让数学知识更有条理
