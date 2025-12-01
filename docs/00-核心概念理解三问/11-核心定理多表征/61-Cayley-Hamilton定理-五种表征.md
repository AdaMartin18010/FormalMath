# Cayley-Hamilton定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 线性代数
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Cayley-Hamilton定理 |
| **领域** | 线性代数 |
| **发现者** | Cayley (1858), Hamilton |
| **前置知识** | 特征多项式、矩阵 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Cayley-Hamilton定理**：设A是n×n矩阵，p(λ) = det(λI - A)是其特征多项式，则p(A) = 0。

$$p(A) = A^n - (\mathrm{tr}A)A^{n-1} + \cdots + (-1)^n\det(A) \cdot I = 0$$

---

## 二、几何表征（可视化）

```text
A满足自己的特征方程：
p(λ) = 0 定义特征值
p(A) = 0 矩阵本身满足
```

---

## 三、直觉表征（类比）

> **Cayley-Hamilton**：矩阵A"知道"自己的特征多项式，并满足它

---

## 四、计算表征（算法）

```python
import numpy as np

def verify_cayley_hamilton(A):
    n = A.shape[0]
    coeffs = np.poly(A)  # 特征多项式系数
    result = sum(coeffs[i] * np.linalg.matrix_power(A, n-i)
                for i in range(n+1))
    return np.allclose(result, 0)
```

---

## 五、范畴表征（抽象）

Cayley-Hamilton说明每个矩阵在其特征多项式上零化，是代数结构的内蕴性质。

---

**状态**: ✅ 完成
