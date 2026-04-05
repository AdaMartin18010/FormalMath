---
msc_primary: 00A99
msc_secondary:
- 00A99
title: msc_annotation_phase2
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# msc_annotation_phase2

**源文件**: `tools\msc_annotation_phase2.py`

## 函数

### has_msc

```python
def has_msc(content)

```

检查文件是否已有MSC编码

**参数**:

- `content`

### detect_msc_from_filename

```python
def detect_msc_from_filename(filename, content)

```

根据文件名和内容检测MSC编码

**参数**:

- `filename`
- `content`

### add_msc_to_frontmatter

```python
def add_msc_to_frontmatter(content, primary, secondary)

```

添加MSC编码到frontmatter

**参数**:

- `content`
- `primary`
- `secondary`

### process_file

```python
def process_file(filepath)

```

处理单个文件

**参数**:

- `filepath`

### main

```python
def main()

```

主函数

