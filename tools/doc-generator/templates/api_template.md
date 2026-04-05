---
title: '{{ module_name }}'
msc_primary: 00A99
processed_at: '2026-04-05'
---
# {{ module_name }}

**源文件**: `{{ source_file }}`

## 概述

{{ description }}

## 类

{% for class in classes %}
### {{ class.name }}

{{ class.docstring }}

**继承**: {{ class.bases | join(", ") }}

#### 方法

{% for method in class.methods %}
##### {{ method.name }}{{ method.signature }}

{{ method.docstring }}

{% endfor %}

{% endfor %}

## 函数

{% for func in functions %}
### {{ func.name }}{{ func.signature }}

{{ func.docstring }}

**参数**:
{% for param in func.parameters %}
- `{{ param.name }}`{% if param.type %} (`{{ param.type }}`){% endif %}: {{ param.description }}
{% endfor %}

**返回**: {{ func.returns }}

---

{% endfor %}

---

*由 FormalMath API文档生成器自动生成*
