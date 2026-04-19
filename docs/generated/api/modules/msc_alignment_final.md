---
msc_primary: 00

  - 00A99
title: msc_alignment_final
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# msc_alignment_final

**源文件**: `tools\msc_alignment_final.py`

## 函数

### extract_frontmatter

```python
def extract_frontmatter(content: str)

```

提取YAML frontmatter

**参数**:

- `content: str`

### get_msc_info

```python
def get_msc_info(frontmatter)

```

提取MSC编码信息

**参数**:

- `frontmatter`

### scan_concepts

```python
def scan_concepts()

```

扫描所有概念文档

### validate_msc_code

```python
def validate_msc_code(code: str)

```

验证MSC编码格式

**参数**:

- `code: str`

### check_classification_accuracy

```python
def check_classification_accuracy(concepts) -> Dict

```

检查MSC分类准确性

**参数**:

- `concepts`

### generate_correction_plan

```python
def generate_correction_plan(check_results: Dict)

```

生成分类修正计划

**参数**:

- `check_results: Dict`

### create_msc_reverse_index

```python
def create_msc_reverse_index(concepts) -> Dict

```

创建MSC到概念的反向索引

**参数**:

- `concepts`

### generate_hierarchy_data

```python
def generate_hierarchy_data(reverse_index: Dict) -> Dict

```

生成MSC层级可视化数据

**参数**:

- `reverse_index: Dict`

### generate_report

```python
def generate_report(concepts, check_results: Dict, corrections, reverse_index: Dict, hierarchy: Dict) -> str

```

生成MSC对齐报告

**参数**:

- `concepts`
- `check_results: Dict`
- `corrections`
- `reverse_index: Dict`
- `hierarchy: Dict`

### main

```python
def main()

```

主函数

