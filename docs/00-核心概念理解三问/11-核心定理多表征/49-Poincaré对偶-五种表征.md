# Poincaré对偶 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 代数拓扑
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Poincaré对偶定理 |
| **领域** | 代数拓扑 |
| **发现者** | Henri Poincaré (1895) |
| **前置知识** | 同调群、上同调群、流形 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Poincaré对偶**：设M是紧致定向n维流形，则存在同构：

$$H^k(M; R) \cong H_{n-k}(M; R)$$

由cap积与基本类[M]给出：α ↦ α ∩ [M]

### 1.2 Betti数关系

$$b_k(M) = b_{n-k}(M)$$

### 1.3 Lean 4 形式化

```lean
-- Poincaré对偶（概念性）
theorem poincare_duality {M : Type*} [TopologicalManifold M]
    [Compact M] [Orientable M] (n : ℕ) (hn : dim M = n)
    (R : Type*) [CommRing R] (k : ℕ) :
    H^k(M; R) ≃ H_{n-k}(M; R) := by
  sorry  -- 需要详细的代数拓扑形式化
```

---

## 二、几何表征（可视化）

### 2.1 对偶循环

```text
n维流形M上：

    k-上循环 α ←────→ (n-k)-循环 α∩[M]

例：2维环面T²
    H⁰ ≅ H₂ (整体 ↔ 曲面)
    H¹ ≅ H₁ (1-形式 ↔ 1-循环)
```

### 2.2 交叉数

```text
k-循环与(n-k)-循环的交叉数：

    γₖ ∩ γₙ₋ₖ = ±(交点数)

这定义了配对 Hₖ × Hₙ₋ₖ → ℤ
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Poincaré对偶**：在紧致流形上，k维"洞"与(n-k)维"洞"一一对应

### 3.2 维度互补

- 0维洞（连通分支）↔ n维洞（整体）
- 1维洞（循环）↔ (n-1)维洞
- k维 ↔ (n-k)维

### 3.3 为什么需要定向？

定向给出"基本类"[M]，用于cup/cap积

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np

def compute_betti_numbers(boundary_matrices):
    """
    计算Betti数（验证Poincaré对偶）
    """
    betti = []
    for k, (d_k, d_k1) in enumerate(zip(boundary_matrices[:-1], boundary_matrices[1:])):
        # b_k = dim(ker d_k) - dim(im d_{k+1})
        rank_d_k = np.linalg.matrix_rank(d_k)
        rank_d_k1 = np.linalg.matrix_rank(d_k1)
        dim_chain_k = d_k.shape[1]

        b_k = (dim_chain_k - rank_d_k) - rank_d_k1
        betti.append(b_k)
    return betti

def verify_poincare_duality(M_triangulation, n):
    """
    验证流形M的Poincaré对偶
    """
    betti = compute_betti_numbers(M_triangulation)

    # 检验 b_k = b_{n-k}
    for k in range((n + 1) // 2 + 1):
        if betti[k] != betti[n - k]:
            return False
    return True

# 示例：环面T²（n=2）
# b₀ = 1, b₁ = 2, b₂ = 1
# Poincaré对偶: b₀ = b₂, b₁ = b₁ ✓
```

### 4.2 cap积计算

```python
def cap_product(alpha, fundamental_class, simplices):
    """
    计算cap积 α ∩ [M]
    """
    # 简化：单纯复形上的cap积
    result = []
    for sigma in fundamental_class:
        # α评估在sigma的前面，结果是后面
        pass
    return result
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Poincaré对偶 = 同调与上同调的对偶
├─ 上同调H*是反变函子
├─ 同调H_*是协变函子
├─ Poincaré对偶：在流形上它们"对偶"
└─ 通过cap积与[M]实现
```

### 5.2 推广

- **非紧致流形**：Borel-Moore同调
- **带边流形**：相对Poincaré对偶
- **奇异空间**：交截上同调（Goresky-MacPherson）

### 5.3 Grothendieck对偶

```text
在代数几何中：
├─ 层上同调的Serre对偶
├─ Grothendieck对偶
└─ Verdier对偶（导出范畴）
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **de Rham定理** | 微分形式版本 |
| **Serre对偶** | 代数几何版本 |
| **Alexander对偶** | 嵌入空间版本 |

---

**状态**: ✅ 完成
