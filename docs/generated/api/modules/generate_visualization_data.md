---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# generate_visualization_data

**源文件**: `tools\generate_visualization_data.py`

## 函数

### parse_concepts

```python
def parse_concepts(yaml_file)

```

解析YAML文件提取概念数据

**参数**:

- `yaml_file`

### generate_visualization_data

```python
def generate_visualization_data(concepts, metadata)

```

生成可视化数据

**参数**:

- `concepts`
- `metadata`

### get_category_group

```python
def get_category_group(category)

```

获取类别的颜色组

**参数**:

- `category`

### generate_mermaid_diagram

```python
def generate_mermaid_diagram(concepts, max_nodes = 50)

```

生成Mermaid图表代码（简化版）

**参数**:

- `concepts`
- `max_nodes`

### generate_statistics_report

```python
def generate_statistics_report(concepts, metadata)

```

生成统计报告

**参数**:

- `concepts`
- `metadata`

### main

```python
def main()

```

