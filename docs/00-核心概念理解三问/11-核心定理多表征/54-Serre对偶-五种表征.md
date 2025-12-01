# Serre对偶定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 代数几何
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Serre对偶定理 |
| **领域** | 代数几何 |
| **发现者** | Jean-Pierre Serre (1955) |
| **前置知识** | 层上同调、凝聚层、典范丛 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Serre对偶**：设X是n维光滑射影簇，ℱ是X上的凝聚层，ωₓ是典范丛，则：

$$H^i(X, \mathcal{F}) \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)^\vee$$

---

## 二、几何表征（可视化）

```text
H^i(X, ℱ) ←──对偶──→ H^{n-i}(X, ℱ^∨⊗ω)
    │                      │
  低阶上同调          高阶上同调
```

---

## 三、直觉表征（类比）

> **Serre对偶**：代数簇的"洞"在低维和高维之间对称

---

## 四、计算表征（算法）

```python
def serre_duality_check(cohomology_i, cohomology_n_minus_i):
    # 维数应该相等
    return dim(cohomology_i) == dim(cohomology_n_minus_i)
```

---

## 五、范畴表征（抽象）

Serre对偶是导出范畴中的Verdier对偶的代数几何版本。

---

**状态**: ✅ 完成
