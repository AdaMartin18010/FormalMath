# FormalMath 知识图谱导出工具

强大的知识图谱多格式导出功能，支持PDF、图片、GraphML、JSON等多种格式，便于分享、打印和进一步分析。

## ✨ 功能特性

| 格式 | 文件扩展名 | 用途 | 特点 |
|------|-----------|------|------|
| 📄 JSON | `.json` | 数据交换 | 完整数据结构，适合程序处理 |
| 📊 CSV | `.csv` | 表格分析 | Excel兼容，节点边分离存储 |
| 🕸️ GraphML | `.graphml` | 网络分析 | Gephi/Cytoscape兼容 |
| 🎨 SVG | `.svg` | 矢量图 | 无损缩放，网页嵌入 |
| 🖼️ PNG | `.png` | 位图 | 演示文稿，透明背景 |
| 📑 PDF | `.pdf` | 打印存档 | A4优化，打印友好 |
| 🌐 HTML | `.html` | 交互界面 | 浏览器预览，在线导出 |

## 🚀 快速开始

### 安装依赖

```bash
cd tools/export

# 基础安装（JSON/CSV/GraphML/SVG）
pip install pyyaml

# 完整安装（包含PDF/PNG）
pip install -r requirements.txt
```

### 命令行使用

```bash
# 导出所有格式
python main_exporter.py -i data.json -o ./output

# 只导出PDF和PNG
python main_exporter.py -i data.json -f pdf png

# 从YAML导出
python main_exporter.py -i concepts.yaml -o ./export

# 显示交互式菜单
python -c "from export_ui import ExportUI; ExportUI('.').cli_interactive(lambda f: print(f'导出: {f}'))"
```

### Python API 使用

```python
from main_exporter import KnowledgeGraphExporter

# 创建导出器
exporter = KnowledgeGraphExporter(output_dir="./output")

# 加载数据
exporter.load_from_json("knowledge_graph.json")
# 或
exporter.load_from_yaml("concepts.yaml")

# 导出所有格式
results = exporter.export_all()

# 导出特定格式
exporter.export_all(['pdf', 'svg', 'json'])

# 查看导出结果
for fmt, path in results.items():
    print(f"{fmt}: {path}")
```

### 单独使用各导出器

```python
from json_exporter import JSONExporter
from graphml_exporter import GraphMLExporter
from pdf_exporter import PDFExporter
from image_exporter import ImageExporter
from export_ui import ExportUI

# JSON导出
json_exp = JSONExporter("./output")
json_exp.set_data(nodes, edges, metadata)
json_exp.export_json()
json_exp.export_csv()

# GraphML导出
graphml_exp = GraphMLExporter("./output")
graphml_exp.set_data(nodes, edges, metadata)
graphml_exp.export_graphml()
graphml_exp.export_for_gephi()  # Gephi优化

# PDF导出
pdf_exp = PDFExporter("./output")
pdf_exp.set_data(nodes, edges, metadata)
pdf_exp.export_pdf(method="playwright")  # 或 "reportlab"

# 图片导出
img_exp = ImageExporter("./output")
img_exp.set_data(nodes, edges, metadata)
img_exp.export_svg(width=1600, height=1200)
img_exp.export_png(width=1200, height=800)
img_exp.export_thumbnail(size=300)

# 生成导出界面
ui = ExportUI("./output")
ui.generate_export_portal()  # 完整门户
ui.generate_embedded_widget()  # 嵌入式组件
```

## 📁 输出文件结构

```
output/
├── knowledge_graph.json          # JSON完整数据
├── knowledge_graph_simple.json   # JSON简化版
├── knowledge_graph_d3.json       # D3.js兼容格式
├── csv_export/
│   ├── nodes.csv                 # 概念节点
│   ├── edges.csv                 # 关系边
│   └── statistics.csv            # 统计汇总
├── knowledge_graph.graphml       # GraphML标准格式
├── knowledge_graph_gephi.graphml # Gephi优化版
├── knowledge_graph.svg           # SVG矢量图
├── knowledge_graph.png           # PNG位图
├── knowledge_graph.pdf           # PDF文档
├── knowledge_graph.html          # HTML预览
├── export_portal.html            # 导出中心
├── export_widget.html            # 嵌入组件
└── print.css                     # 打印样式表
```

## 🛠️ 导出器说明

### JSONExporter

支持多种JSON格式：
- 完整JSON：包含所有元数据、节点和边
- 简化JSON：仅节点和边
- D3兼容JSON：适合D3.js力导向图

### GraphMLExporter

支持网络分析工具：
- 标准GraphML格式
- Gephi优化版（额外可视化属性）
- Cytoscape兼容格式

### PDFExporter

两种导出方式：
- **Playwright**（推荐）：使用Chromium渲染，效果最好
- **ReportLab**：纯Python方案，无需外部依赖

### ImageExporter

支持图片格式：
- SVG：力导向或圆形布局
- PNG：高质量位图
- 缩略图：小尺寸预览图

两种布局算法：
- 力导向布局：模拟物理力自动排列
- 圆形布局：按类别分组排列

### ExportUI

界面组件：
- 命令行交互菜单
- HTML导出门户（完整界面）
- 嵌入式导出组件（iframe）

## 📊 数据格式

### 输入JSON格式

```json
{
  "metadata": {
    "version": "1.0",
    "generated_date": "2024-01-01T00:00:00"
  },
  "nodes": [
    {
      "id": "calculus_001",
      "name": "微积分基础",
      "category": "分析学",
      "difficulty": 3,
      "estimated_hours": 20,
      "description": "微积分的核心概念",
      "msc_code": "26-01"
    }
  ],
  "edges": [
    {
      "source": "algebra_001",
      "target": "calculus_001",
      "relation_type": "依赖",
      "level": "L1"
    }
  ]
}
```

### 输入YAML格式

```yaml
version: "1.0"
concepts:
  - concept_id: calculus_001
    name: 微积分基础
    category: 分析学
    difficulty: 3
    estimated_hours: 20
    prerequisites:
      - concept_id: algebra_001
        relation: 依赖
        level: L1
```

## 🎨 类别颜色

| 类别 | 背景色 | 边框色 |
|------|--------|--------|
| 分析学 | #E3F2FD | #1565C0 |
| 代数学 | #F3E5F5 | #7B1FA2 |
| 几何拓扑 | #E8F5E9 | #2E7D32 |
| 数论逻辑 | #FBE9E7 | #D84315 |
| 概率统计 | #FFF8E1 | #F9A825 |
| 最优化 | #E0F2F1 | #00695C |
| 控制论 | #E1F5FE | #0277BD |
| 信息论 | #F3E5F5 | #6A1B9A |
| 密码学 | #ECEFF1 | #455A64 |
| 基础数学 | #F5F5F5 | #616161 |

## 🔧 高级配置

### 自定义样式

修改 `print.css` 可自定义打印样式：

```css
@media print {
    @page {
        size: A4 landscape;  /* 横向打印 */
        margin: 1cm;
    }
}
```

### 自定义布局参数

```python
from image_exporter import ImageExporter

exp = ImageExporter("./output")
exp.set_data(nodes, edges)

# 自定义力导向参数
exp._calculate_force_layout(
    width=1600,
    height=1200,
    iterations=150  # 更多迭代，更好布局
)
```

## 📝 命令行参数

```
python main_exporter.py -h

选项:
  -i, --input     输入文件路径 (JSON或YAML)
  -o, --output    输出目录 (默认: output/export)
  -f, --formats   导出格式列表
                  可选: json, csv, graphml, pdf, svg, png, html, all

示例:
  python main_exporter.py -i data.json -f json csv pdf
  python main_exporter.py -i concepts.yaml -o ./export -f all
```

## 🐛 故障排除

### PDF导出失败

```bash
# 安装Playwright
pip install playwright
playwright install chromium

# 或使用ReportLab（备选）
pip install reportlab
```

### PNG导出失败

```bash
# 安装cairosvg（推荐）
pip install cairosvg

# 或安装Pillow（备选）
pip install pillow
```

### 中文字体问题

PDF导出需要支持中文的字体。确保系统安装了以下字体之一：
- Noto Sans CJK SC
- Source Han Sans SC
- Microsoft YaHei

## 📄 许可

MIT License - 参见项目主 LICENSE 文件

---

**FormalMath Project** | 让数学知识更有条理
