# wikipedia_fast_align

**源文件**: `tools\wikipedia_fast_align.py`

## 函数

### load_concepts

```python
def load_concepts(yaml_path: str)
```

加载概念列表

**参数**:

- `yaml_path: str`

### generate_multilang_table

```python
def generate_multilang_table(concepts)
```

生成多语言对照表

**参数**:

- `concepts`

### generate_json_output

```python
def generate_json_output(table, output_path: str)
```

生成JSON输出

**参数**:

- `table`
- `output_path: str`

### generate_markdown_report

```python
def generate_markdown_report(table, output_path: str)
```

生成Markdown报告

**参数**:

- `table`
- `output_path: str`

### update_yaml_with_multilang

```python
def update_yaml_with_multilang(yaml_path: str, table, output_path: str)
```

更新YAML文件添加多语言字段

**参数**:

- `yaml_path: str`
- `table`
- `output_path: str`

### main

```python
def main()
```

主函数

