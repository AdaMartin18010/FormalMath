# Gram-Schmidt正交化 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 线性代数
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Gram-Schmidt正交化过程 |
| **领域** | 线性代数 |
| **发现者** | Gram, Schmidt |
| **前置知识** | 内积空间、正交性 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Gram-Schmidt**：给定线性无关向量{v₁,...,vₙ}，可构造正交归一向量{e₁,...,eₙ}：

$$e_k = \frac{v_k - \sum_{j=1}^{k-1} \langle v_k, e_j \rangle e_j}{\|v_k - \sum_{j=1}^{k-1} \langle v_k, e_j \rangle e_j\|}$$

---

## 二、几何表征（可视化）

```text
v₁,v₂,v₃ (非正交)
    │
    Gram-Schmidt
    ↓
e₁,e₂,e₃ (正交归一)
```

---

## 三、直觉表征（类比）

> **Gram-Schmidt**：逐步"纠正"向量，使其相互垂直

---

## 四、计算表征（算法）

```python
def gram_schmidt(V):
    n = V.shape[1]
    E = np.zeros_like(V, dtype=float)
    for k in range(n):
        e = V[:, k].copy()
        for j in range(k):
            e -= np.dot(V[:, k], E[:, j]) * E[:, j]
        E[:, k] = e / np.linalg.norm(e)
    return E
```

---

## 五、范畴表征（抽象）

Gram-Schmidt是QR分解的构造方法，反映内积空间的正交结构。

---

**状态**: ✅ 完成
