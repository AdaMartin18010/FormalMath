# 知识图谱导出工具 - 使用指南

## 快速开始

### 1. 安装依赖

```bash
cd tools/knowledge-graph-exporter
pip install -r requirements.txt
```

### 2. 导出示例数据

```bash
# 导出所有格式
python knowledge_graph_exporter.py -i example_data.json -o output/demo

# 仅导出特定格式
python knowledge_graph_exporter.py -i example_data.json -f json csv svg
```

### 3. 批量导出项目数据

```bash
# 导出所有数据源
python batch_export.py

# 导出示例数据
python batch_export.py --example

# 导出特定文件
python batch_export.py -i ../../concept/concept_prerequisites.yaml -o output/my_export
```

## 导出格式详解

### JSON 导出
- **文件**: `knowledge_graph.json`
- **用途**: 数据交换、程序处理
- **特点**: 
  - 包含完整节点和边数据
  - 添加导出元信息（时间、版本）
  - 标准JSON格式，易于解析

### CSV 导出
- **目录**: `csv_export/`
- **文件**: 
  - `nodes.csv` - 概念节点数据
  - `edges.csv` - 关系边数据
  - `statistics.csv` - 统计汇总
- **用途**: Excel分析、数据科学工具

### GraphML 导出
- **文件**: `knowledge_graph.graphml`
- **用途**: Gephi、Cytoscape网络分析
- **特点**:
  - 标准GraphML格式
  - 包含节点颜色属性
  - 支持有向图

### PDF 导出
- **文件**: `knowledge_graph.pdf`
- **用途**: 打印、分享、存档
- **要求**: 安装 reportlab
- **特点**:
  - A4页面优化
  - 自动分页
  - 统计表格和概念详情

### SVG 导出
- **文件**: `knowledge_graph.svg`
- **用途**: 网页嵌入、矢量编辑
- **特点**:
  - 力导向布局
  - 节点大小反映难度
  - 颜色区分类别

### PNG 导出
- **文件**: `knowledge_graph.png`
- **用途**: 演示文稿、位图应用
- **要求**: 安装 cairosvg 或 pillow
- **注意**: PNG由SVG转换生成，质量取决于SVG渲染

### HTML 导出
- **文件**: `knowledge_graph.html`
- **用途**: 交互式网页展示
- **生成**: 使用 `html_exporter.py`
- **特点**:
  - 响应式设计
  - 打印优化CSS
  - 交互式图谱可视化

## Python API 使用

### 基础用法

```python
from knowledge_graph_exporter import KnowledgeGraphExporter
from pathlib import Path

# 创建导出器
exporter = KnowledgeGraphExporter(output_dir=Path("output"))

# 加载数据
exporter.load_from_json(Path("data.json"))

# 导出所有格式
results = exporter.export_all()
```

### 高级用法

```python
# 导出特定格式
exporter.export_pdf()           # PDF
exporter.export_svg(width=1600) # 自定义尺寸SVG
exporter.export_graphml()       # Gephi格式

# 获取导出文件路径
print(results['pdf'])   # PosixPath('output/knowledge_graph.pdf')
```

### 处理YAML数据

```python
# 从概念前置关系YAML加载
exporter.load_from_yaml(Path("concept_prerequisites.yaml"))
```

## 数据源配置

编辑 `batch_export.py` 中的 `DATA_SOURCES` 配置：

```python
DATA_SOURCES = {
    "my_data": {
        "path": "path/to/my/data.json",
        "type": "json",  # 或 "yaml"
        "description": "我的数据"
    }
}
```

## 故障排除

### 问题: PDF导出失败
**解决**: 
```bash
pip install reportlab
```

### 问题: PNG导出质量不佳
**解决**:
```bash
pip install cairosvg  # 推荐
# 或
pip install pillow    # 备选
```

### 问题: 中文显示为方框
**解决**: 安装中文字体
- Windows: 已内置微软雅黑
- macOS: 安装字体文件到 ~/Library/Fonts/
- Linux: `sudo apt install fonts-noto-cjk`

### 问题: YAML加载失败
**解决**:
```bash
pip install pyyaml
```

## 文件结构

```
knowledge-graph-exporter/
├── knowledge_graph_exporter.py   # 主导出工具
├── html_exporter.py              # HTML导出器
├── batch_export.py               # 批量导出脚本
├── example_data.json             # 示例数据
├── requirements.txt              # 依赖项
├── print.css                     # 打印优化CSS
├── README.md                     # 主要文档
└── USAGE.md                      # 本使用指南
```

## 扩展开发

### 添加新导出格式

1. 在 `KnowledgeGraphExporter` 类中添加新方法:

```python
def export_xml(self, output_path: Path = None) -> Path:
    """导出为XML格式"""
    if output_path is None:
        output_path = self.output_dir / "knowledge_graph.xml"
    
    # 实现导出逻辑
    # ...
    
    return output_path
```

2. 在 `export_all()` 方法中添加:

```python
elif fmt == 'xml':
    results['xml'] = self.export_xml()
```

### 自定义样式

修改 `print.css` 来自定义PDF打印样式。

## 许可

MIT License
