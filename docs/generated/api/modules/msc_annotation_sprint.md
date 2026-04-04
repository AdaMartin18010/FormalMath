---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# msc_annotation_sprint

**源文件**: `tools\msc_annotation_sprint.py`

## 函数

### detect_msc_from_content

```python
def detect_msc_from_content(filepath, content, branch)

```

根据文件内容检测MSC编码

**参数**:

- `filepath`
- `content`
- `branch`

### has_frontmatter

```python
def has_frontmatter(content)

```

检查文件是否已有frontmatter

**参数**:

- `content`

### has_msc

```python
def has_msc(content)

```

检查文件是否已有MSC编码

**参数**:

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
def process_file(filepath, branch)

```

处理单个文件

**参数**:

- `filepath`
- `branch`

### main

```python
def main()

```

主函数

