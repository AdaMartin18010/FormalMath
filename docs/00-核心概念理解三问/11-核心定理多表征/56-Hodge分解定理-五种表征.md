# Hodge分解定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分几何/复几何
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Hodge分解定理 |
| **领域** | 微分几何 |
| **发现者** | W.V.D. Hodge (1930s) |
| **前置知识** | 微分形式、Laplacian、调和形式 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Hodge分解**：设M是紧致定向Riemann流形，则：

$$\Omega^k(M) = \mathcal{H}^k(M) \oplus d\Omega^{k-1}(M) \oplus d^*\Omega^{k+1}(M)$$

每个k-形式唯一分解为调和+恰当+余恰当。

---

## 二、几何表征（可视化）

```text
k-形式空间 Ω^k
    │
    ├── ℋ^k (调和：Δω=0)
    ├── dΩ^{k-1} (恰当：ω=dη)
    └── d*Ω^{k+1} (余恰当：ω=d*ξ)

正交直和分解
```

---

## 三、直觉表征（类比）

> **Hodge**：每个微分形式可以分解为"静止部分"（调和）和"流动部分"（恰当+余恰当）

---

## 四、计算表征（算法）

```python
def hodge_decomposition(omega, laplacian, d, d_star):
    # 调和部分: ker(Δ)
    harmonic = project_kernel(omega, laplacian)
    # 恰当部分: im(d)
    exact = project_image(omega - harmonic, d)
    # 余恰当部分
    coexact = omega - harmonic - exact
    return harmonic, exact, coexact
```

---

## 五、范畴表征（抽象）

Hodge分解给出de Rham上同调的调和代表：H^k(M) ≅ ℋ^k(M)。

---

**状态**: ✅ 完成
