# FormalMath 知识图谱多格式导出工具

知识图谱导出工具，支持多种格式导出，便于分享、打印和进一步分析。

## 功能特性

| 格式 | 文件名 | 用途 |
|------|--------|------|
| JSON | `knowledge_graph.json` | 数据交换、程序处理 |
| CSV | `csv_export/*.csv` | 表格分析、Excel处理 |
| GraphML | `knowledge_graph.graphml` | Gephi/Cytoscape网络分析 |
| PDF | `knowledge_graph.pdf` | 打印、分享、存档 |
| SVG | `knowledge_graph.svg` | 矢量图、网页嵌入 |
| PNG | `knowledge_graph.png` | 位图、演示文稿 |

## 安装

### 1. 安装依赖

```bash
cd tools/knowledge-graph-exporter
pip install -r requirements.txt
```

### 2. 可选依赖说明

- **ReportLab**: PDF导出必需
- **CairoSVG**: PNG导出推荐（质量更好）
- **Pillow**: PNG导出备选

## 使用方法

### 命令行使用

```bash
# 导出所有格式
python knowledge_graph_exporter.py -i input.json -o output/

# 只导出特定格式
python knowledge_graph_exporter.py -i input.json -f json csv pdf

# 从YAML加载
python knowledge_graph_exporter.py -i concept_prerequisites.yaml -o export/
```

### 参数说明

| 参数 | 简写 | 说明 | 默认值 |
|------|------|------|--------|
| `--input` | `-i` | 输入文件路径 (JSON/YAML) | 必需 |
| `--output` | `-o` | 输出目录 | `output/export` |
| `--formats` | `-f` | 导出格式列表 | `all` |

### Python API使用

```python
from knowledge_graph_exporter import KnowledgeGraphExporter
from pathlib import Path

# 创建导出器
exporter = KnowledgeGraphExporter(output_dir=Path("output"))

# 加载数据
exporter.load_from_json(Path("data.json"))
# 或
exporter.load_from_yaml(Path("data.yaml"))

# 导出所有格式
results = exporter.export_all()

# 或导出特定格式
exporter.export_pdf()
exporter.export_svg(width=1600, height=1200)
exporter.export_graphml()
```

## 输入数据格式

### JSON格式示例

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
      "msc_code": "20-XX"
    }
  ],
  "edges": [
    {
      "from": "C001",
      "to": "C002",
      "label": "依赖",
      "level": "L1"
    }
  ]
}
```

### YAML格式示例

```yaml
concepts:
  - concept_id: "C001"
    name: "群论"
    category: "代数学"
    difficulty: 2
    estimated_hours: 20
    prerequisites:
      - concept_id: "C000"
        relation: "依赖"
        level: "L1"
```

## 输出文件说明

### 1. JSON导出
- 包含完整的节点和边数据
- 添加了导出元信息
- 适合程序间数据交换

### 2. CSV导出
生成三个文件：
- `nodes.csv`: 概念节点数据
- `edges.csv`: 关系边数据
- `statistics.csv`: 统计汇总

### 3. GraphML导出
- Gephi兼容格式
- 包含节点颜色、类别属性
- 支持有向图

### 4. PDF导出
- A4页面优化
- 包含统计表格和概念详情
- 支持打印分页

### 5. SVG/PNG导出
- 力导向布局可视化
- 节点大小反映难度
- 颜色区分类别
- 包含图例

## 打印优化

使用提供的 `print.css` 样式表优化打印效果：

```html
<link rel="stylesheet" href="print.css" media="print">
```

打印样式特性：
- A4页面适配
- 自动分页控制
- 页眉页脚
- 页码
- 颜色精确还原

## 类别颜色映射

| 类别 | 颜色代码 | 预览 |
|------|----------|------|
| 分析学 | #E3F2FD | ![分析学](https://via.placeholder.com/15/E3F2FD/E3F2FD) |
| 代数学 | #F3E5F5 | ![代数学](https://via.placeholder.com/15/F3E5F5/F3E5F5) |
| 几何拓扑 | #E8F5E9 | ![几何拓扑](https://via.placeholder.com/15/E8F5E9/E8F5E9) |
| 数论逻辑 | #FBE9E7 | ![数论逻辑](https://via.placeholder.com/15/FBE9E7/FBE9E7) |
| 概率统计 | #FFF8E1 | ![概率统计](https://via.placeholder.com/15/FFF8E1/FFF8E1) |

## 故障排除

### PDF导出失败
```bash
# 安装ReportLab
pip install reportlab
```

### PNG导出质量不佳
```bash
# 安装CairoSVG以获得更好质量
pip install cairosvg
```

### 中文显示问题
确保系统安装了中文字体：
- Windows: 微软雅黑/宋体
- macOS: 华文细黑/苹方
- Linux: Noto Sans CJK

## 许可

MIT License - 参见项目主LICENSE文件
