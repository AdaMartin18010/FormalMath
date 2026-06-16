---
msc_primary: '00

  - 00A99'
title: FormalMath 与 Mathlib4 概念映射
processed_at: '2026-04-05'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/function
  wikipedia_url: https://en.wikipedia.org/wiki/Function_(mathematics)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E6%98%A0%E5%B0%84
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q11348
    consulted_at: '2026-06-16'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# FormalMath 与 Mathlib4 概念映射
**生成时间**: 2026-04-04 13:07:54
**映射总数**: 8

| FormalMath概念 | Mathlib4位置 | 状态 |
|----------------|--------------|------|
| `Group` | `Mathlib.Algebra.Group.Defs` | ✅ 已对齐 |
| `Ring` | `Mathlib.Algebra.Ring.Defs` | ✅ 已对齐 |
| `Field` | `Mathlib.Algebra.Field.Defs` | ✅ 已对齐 |
| `TopologicalSpace` | `Mathlib.Topology.Defs` | ✅ 已对齐 |
| `MetricSpace` | `Mathlib.Topology.MetricSpace.Basic` | ✅ 已对齐 |
| `Manifold` | `Mathlib.Geometry.Manifold.ChartedSpace` | ✅ 已对齐 |
| `Category` | `Mathlib.CategoryTheory.Category.Basic` | ✅ 已对齐 |
| `Functor` | `Mathlib.CategoryTheory.Functor.Basic` | ✅ 已对齐 |

## 使用说明

FormalMath中的概念与Mathlib4保持对齐，便于：

1. **学习参考**: 可对照Mathlib4源码学习实现细节
2. **代码复用**: 可直接引用Mathlib4中的相关定理
3. **社区贡献**: 方便向Mathlib4贡献代码