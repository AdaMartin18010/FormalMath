---
title: '{{ concept_name }}'
msc_primary: 00A99
processed_at: '2026-04-05'
---
# {{ concept_name }}

## 基本信息

| 属性 | 值 |
|------|-----|
| **ID** | {{ concept_id }} |
| **英文名** | {{ name_en }} |
| **类别** | {{ category }} |
| **难度** | {{ difficulty }}/5 |
| **预计学时** | {{ estimated_hours }} 小时 |
| **MSC编码** | {{ msc_code }} |

## 描述

{{ description }}

## 前置知识

{% for prereq in prerequisites %}
- [{{ prereq.name }}]({{ prereq.concept_id }}.md) - {{ prereq.relation }}
{% endfor %}

## 学习目标

{% for objective in learning_objectives %}
- {{ objective }}
{% endfor %}

## 相关内容

{% for related in related_concepts %}
- [{{ related }}]
{% endfor %}

## 可视化

```mermaid
graph TD
    {% for prereq in prerequisites %}
    {{ prereq.concept_id }}["{{ prereq.name }}"] --> {{ concept_id }}["{{ concept_name }}"]
    {% endfor %}
```

---

*由 FormalMath 概念图谱生成器自动生成*
