# Schur正交性关系 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 表示论
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Schur正交性关系 |
| **领域** | 表示论 |
| **发现者** | Issai Schur (1905) |
| **前置知识** | 有限群表示、特征标 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Schur正交性（第一类）**：设G是有限群，ρᵢ和ρⱼ是不可约表示，则：

$$\frac{1}{|G|} \sum_{g \in G} \rho_i(g)_{ab} \overline{\rho_j(g)_{cd}} = \frac{\delta_{ij}\delta_{ac}\delta_{bd}}{\dim \rho_i}$$

**Schur正交性（第二类/特征标）**：
$$\frac{1}{|G|} \sum_{g \in G} \chi_i(g) \overline{\chi_j(g)} = \delta_{ij}$$

---

## 二、几何表征（可视化）

```text
不可约特征标构成正交归一基：
⟨χᵢ, χⱼ⟩ = δᵢⱼ
```

---

## 三、直觉表征（类比）

> **Schur正交**：不可约表示的"指纹"（特征标）相互正交

---

## 四、计算表征（算法）

```python
def schur_orthogonality(G, chi_i, chi_j):
    inner = sum(chi_i(g) * chi_j(g).conjugate() for g in G)
    return inner / len(G)  # = 1 if i==j else 0
```

---

## 五、范畴表征（抽象）

Schur正交性反映群代数ℂ[G]的半单分解。

---

**状态**: ✅ 完成
