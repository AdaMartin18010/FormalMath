---
title: '{{ theorem_name }}'
msc_primary: 00A99
processed_at: '2026-04-05'
---
# {{ theorem_name }}

## 定理陈述

```lean4
theorem {{ theorem_name }} {{ theorem_statement }}
```

## 描述

{{ docstring }}

## 证明

{% if is_sorry %}
⚠️ 此定理使用 `sorry` 占位，证明尚未完成。
{% else %}
```lean4
{{ proof }}
```
{% endif %}

## 元信息

| 属性 | 值 |
|------|-----|
| **源文件** | `{{ file_path }}` |
| **行号** | {{ line_number }} |
| **标签** | {{ tags | join(", ") }} |
| **依赖** | {{ dependencies | join(", ") }} |
| **Mathlib** | {{ "是" if uses_mathlib else "否" }} |

## 相关定理

{% for related in related_theorems %}
- [{{ related.name }}]({{ related.link }})
{% endfor %}

---

*由 FormalMath Lean4文档生成器自动生成*
