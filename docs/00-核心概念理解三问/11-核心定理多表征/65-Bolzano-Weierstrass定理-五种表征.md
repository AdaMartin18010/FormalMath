# Bolzano-Weierstrass定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 实分析
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Bolzano-Weierstrass定理 |
| **领域** | 实分析 |
| **发现者** | Bolzano, Weierstrass (19世纪) |
| **前置知识** | 有界序列、收敛子列 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Bolzano-Weierstrass定理**：ℝⁿ中每个有界序列有收敛子列。

$$\{x_n\} \subset \mathbb{R}^n \text{ 有界} \Rightarrow \exists \{x_{n_k}\} \text{ 收敛}$$

---

## 二、几何表征（可视化）

```text
有界序列在有限区域内：

    ┌─────────────┐
    │ ∙ ∙∙  ∙    │
    │   ∙  ∙ ∙∙  │
    │  ∙∙   ∙→ * │  (聚点)
    └─────────────┘

必有收敛子列
```

---

## 三、直觉表征（类比）

> **Bolzano-Weierstrass**：有界空间中"无穷多点必有聚集"

---

## 四、计算表征（算法）

```python
def find_convergent_subsequence(seq, tol=1e-6):
    # 二分法找聚点
    lo, hi = min(seq), max(seq)
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if sum(1 for x in seq if lo <= x <= mid) == float('inf'):
            hi = mid
        else:
            lo = mid
    return lo
```

---

## 五、范畴表征（抽象）

Bolzano-Weierstrass等价于ℝⁿ中紧致性，是Heine-Borel定理的序列版本。

---

**状态**: ✅ 完成
