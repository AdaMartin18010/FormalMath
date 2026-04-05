---
msc_primary: 00A99
msc_secondary:
- 00A99
title: msc_batch_processor
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# msc_batch_processor

**源文件**: `tools\msc_batch_processor.py`

## 函数

### has_msc_encoding

```python
def has_msc_encoding(file_path)

```

检查文件是否已有MSC编码

**参数**:

- `file_path`

### determine_msc_code

```python
def determine_msc_code(file_path, relative_path)

```

根据文件路径确定MSC编码

**参数**:

- `file_path`
- `relative_path`

### add_msc_to_file

```python
def add_msc_to_file(file_path, msc_code)

```

向文件添加MSC编码

**参数**:

- `file_path`
- `msc_code`

### scan_and_process

```python
def scan_and_process(base_dir)

```

扫描并处理所有md文件

**参数**:

- `base_dir`

### print_report

```python
def print_report(stats)

```

打印处理报告

**参数**:

- `stats`

