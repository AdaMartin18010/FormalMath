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

**Gram-Schmidt正交化过程**：设 $\{v_1, \ldots, v_n\}$ 是内积空间 $V$ 中的线性无关向量组，则存在正交归一向量组 $\{e_1, \ldots, e_n\}$ 使得：

$$\operatorname{span}\{e_1, \ldots, e_k\} = \operatorname{span}\{v_1, \ldots, v_k\}, \quad k = 1, \ldots, n$$

**递推公式**：

$$u_k = v_k - \sum_{j=1}^{k-1} \langle v_k, e_j \rangle e_j$$

$$e_k = \frac{u_k}{\|u_k\|}$$

### 1.2 矩阵形式

如果 $V = [v_1, \ldots, v_n]$ 是列向量矩阵，则：

$$V = QR$$

其中 $Q = [e_1, \ldots, e_n]$ 是正交矩阵，$R$ 是上三角矩阵。这就是**QR分解**。

### 1.3 形式化表述

$$\leqft[ \{v_1, \ldots, v_n\} \text{ 线性无关 } \right] \Rightarrow \exists \{e_1, \ldots, e_n\} \text{ 正交归一}: \operatorname{span}\{e_i\} = \operatorname{span}\{v_i\}$$

---

## 二、几何表征（可视化）

### 2.1 正交化过程

```text
逐步"纠正"向量：

    v₁,v₂,v₃ (非正交)
        │
        │ Gram-Schmidt
        ↓
    e₁ = v₁/||v₁||
        │
        ↓
    u₂ = v₂ - <v₂,e₁>e₁
    e₂ = u₂/||u₂||
        │
        ↓
    u₃ = v₃ - <v₃,e₁>e₁ - <v₃,e₂>e₂
    e₃ = u₃/||u₃||
        │
        ↓
    e₁,e₂,e₃ (正交归一)
```

### 2.2 投影理解

```text
每一步都是投影：

    v₂
     │
     │ 投影到 e₁
     ↓
    u₂ = v₂ - proj_{e₁}(v₂)
    
    去除 v₂ 在 e₁ 方向的分量
    得到与 e₁ 垂直的分量
```

### 2.3 几何直观

```text
在2D中：

    v₂
    ╱│
   ╱ │ u₂ (垂直分量)
  ╱  │
 ╱   │
●────┴──→ e₁

u₂ = v₂ - <v₂,e₁>e₁
```

---

## 三、直觉表征（类比）

### 3.1 物理类比

> **Gram-Schmidt**：逐步"纠正"向量，使其相互垂直

**类比1：建筑**

- 原始向量 = 不垂直的柱子
- Gram-Schmidt = 逐步调整，使柱子垂直
- 最终结果 = 垂直的柱子

**类比2：导航**

- 原始方向 = 不垂直的方向
- Gram-Schmidt = 逐步调整，使方向垂直
- 最终结果 = 正交坐标系

### 3.2 计算类比

**类比**：Gram-Schmidt类似于：
- **逐步修正**：每次修正一个向量
- **保持生成空间**：不改变线性生成空间
- **正交化**：使向量相互垂直

---

## 四、计算表征（算法）

### 4.1 基本算法

```python
import numpy as np

def gram_schmidt(V):
    """
    Gram-Schmidt正交化
    
    参数:
        V: 列向量矩阵 (m×n)
    
    返回:
        Q: 正交矩阵 (m×n)
        R: 上三角矩阵 (n×n)
    """
    m, n = V.shape
    Q = np.zeros_like(V, dtype=float)
    R = np.zeros((n, n), dtype=float)
    
    for k in range(n):
        # u_k = v_k
        u = V[:, k].copy().astype(float)
        
        # 减去在已正交化向量上的投影
        for j in range(k):
            R[j, k] = np.dot(Q[:, j], V[:, k])
            u -= R[j, k] * Q[:, j]
        
        # 归一化
        R[k, k] = np.linalg.norm(u)
        if R[k, k] > 1e-10:  # 避免除零
            Q[:, k] = u / R[k, k]
        else:
            raise ValueError("向量线性相关")
    
    return Q, R

# 例子
V = np.array([[1, 1, 0], [1, 0, 1], [0, 1, 1]], dtype=float).T
Q, R = gram_schmidt(V)
print("Q (正交):")
print(Q)
print("\nR (上三角):")
print(R)
print("\n验证: V = Q @ R")
print(V - Q @ R)  # 应该接近零
```

### 4.2 改进算法（数值稳定）

```python
def gram_schmidt_modified(V):
    """
    改进的Gram-Schmidt（数值更稳定）
    
    参数:
        V: 列向量矩阵
    
    返回:
        Q: 正交矩阵
        R: 上三角矩阵
    """
    m, n = V.shape
    Q = V.copy().astype(float)
    R = np.zeros((n, n), dtype=float)
    
    for k in range(n):
        # 归一化当前向量
        R[k, k] = np.linalg.norm(Q[:, k])
        if R[k, k] < 1e-10:
            raise ValueError("向量线性相关")
        Q[:, k] /= R[k, k]
        
        # 从后续向量中减去当前向量的投影
        for j in range(k + 1, n):
            R[k, j] = np.dot(Q[:, k], Q[:, j])
            Q[:, j] -= R[k, j] * Q[:, k]
    
    return Q, R

# 比较两种方法
V = np.random.randn(10, 5)
Q1, R1 = gram_schmidt(V)
Q2, R2 = gram_schmidt_modified(V)

# 检查正交性
orthogonality1 = np.linalg.norm(Q1.T @ Q1 - np.eye(5))
orthogonality2 = np.linalg.norm(Q2.T @ Q2 - np.eye(5))
print(f"标准方法正交性误差: {orthogonality1:.2e}")
print(f"改进方法正交性误差: {orthogonality2:.2e}")
```

### 4.3 QR分解

```python
def qr_decomposition(A):
    """
    使用Gram-Schmidt计算QR分解
    
    参数:
        A: 矩阵
    
    返回:
        Q: 正交矩阵
        R: 上三角矩阵
    """
    return gram_schmidt(A)

# 应用：求解线性方程组 Ax = b
def solve_via_qr(A, b):
    """
    使用QR分解求解 Ax = b
    
    参数:
        A: 系数矩阵
        b: 右端向量
    
    返回:
        x: 解
    """
    Q, R = qr_decomposition(A)
    
    # Ax = b ⟹ QRx = b ⟹ Rx = Q^T b
    y = Q.T @ b
    
    # 回代求解 Rx = y
    n = R.shape[0]
    x = np.zeros(n)
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - np.dot(R[i, i+1:], x[i+1:])) / R[i, i]
    
    return x

# 例子
A = np.array([[1, 1], [1, 2], [1, 3]], dtype=float)
b = np.array([1, 2, 3], dtype=float)
x = solve_via_qr(A, b)
print(f"解: {x}")
print(f"残差: {np.linalg.norm(A @ x - b):.2e}")
```

---

## 五、范畴表征（抽象）

### 5.1 内积空间结构

**Gram-Schmidt正交化**反映了**内积空间**的结构：

- **正交基**：每个内积空间都有正交基
- **标准正交基**：可以进一步归一化
- **唯一性**：在给定顺序下，标准正交基唯一（up to符号）

### 5.2 QR分解

**Gram-Schmidt**等价于**QR分解**：

- **存在性**：每个可逆矩阵有QR分解
- **唯一性**：如果 $R$ 的对角元为正，则唯一
- **应用**：求解线性方程组、特征值问题

### 5.3 正交群作用

在**正交群**作用下：

- Gram-Schmidt给出标准形
- 这是矩阵分解的基础

---

## 六、应用实例

### 6.1 经典例子

**例子1**：$\mathbb{R}^3$ 中，$v_1 = (1, 1, 0)$，$v_2 = (1, 0, 1)$，$v_3 = (0, 1, 1)$

- $e_1 = \frac{1}{\sqrt{2}}(1, 1, 0)$
- $u_2 = (1, 0, 1) - \frac{1}{2}(1, 1, 0) = (\frac{1}{2}, -\frac{1}{2}, 1)$
- $e_2 = \frac{1}{\sqrt{6}}(1, -1, 2)$
- 继续得到 $e_3$

**例子2**：Legendre多项式

- 在 $L^2[-1, 1]$ 上，$\{1, x, x^2, \ldots\}$ 的Gram-Schmidt正交化
- 得到Legendre多项式

**例子3**：Fourier级数

- 在 $L^2[0, 2\pi]$ 上，$\{1, \sin x, \cos x, \sin 2x, \cos 2x, \ldots\}$ 已经正交
- Gram-Schmidt给出标准正交基

### 6.2 数值计算

**例子4**：求解最小二乘

- $Ax = b$ 的最小二乘解
- 使用QR分解：$x = R^{-1} Q^T b$
- 数值稳定

**例子5**：特征值计算

- QR算法计算特征值
- 基于QR分解的迭代

---

## 七、历史背景

### 7.1 发现历史

- **19世纪**：Gram 和 Schmidt 独立提出
- **现代**：成为数值线性代数的基础
- **应用**：广泛用于科学计算

### 7.2 现代意义

Gram-Schmidt正交化是：
- 数值线性代数的基础算法
- QR分解的构造方法
- 正交基的标准构造

---

## 八、证明思路

### 8.1 构造性证明

**证明**（归纳法）：

1. **基础**：$e_1 = \frac{v_1}{\|v_1\|}$

2. **归纳**：假设已构造 $e_1, \ldots, e_{k-1}$，定义：
   $$u_k = v_k - \sum_{j=1}^{k-1} \langle v_k, e_j \rangle e_j$$
   $$e_k = \frac{u_k}{\|u_k\|}$$

3. **验证**：
   - $e_k$ 与 $e_1, \ldots, e_{k-1}$ 正交
   - $\operatorname{span}\{e_1, \ldots, e_k\} = \operatorname{span}\{v_1, \ldots, v_k\}$

### 8.2 唯一性

**证明**（在给定顺序下）：

- 如果要求 $R$ 的对角元为正，则QR分解唯一
- 这对应Gram-Schmidt的唯一性

---

## 九、推广与变体

### 9.1 无限维

在Hilbert空间中，有类似的Gram-Schmidt过程。

### 9.2 加权内积

对于加权内积，有加权Gram-Schmidt。

### 9.3 数值改进

有Householder变换和Givens旋转等数值更稳定的方法。

---

**状态**: ✅ 完成（已深化）
**字数**: 约2,300字
**数学公式数**: 8个
**例子数**: 6个
**最后更新**: 2026年01月02日
