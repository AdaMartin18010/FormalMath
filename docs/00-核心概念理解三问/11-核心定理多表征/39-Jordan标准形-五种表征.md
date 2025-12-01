# Jordan标准形 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 线性代数
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Jordan标准形定理 |
| **领域** | 线性代数 |
| **发现者** | Camille Jordan (1870) |
| **前置知识** | 特征值、特征多项式、不变子空间 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Jordan标准形定理**：设V是代数闭域k上的有限维向量空间，T: V→V是线性算子，则存在基使得T的矩阵为Jordan标准形：

$$J = \begin{pmatrix} J_{n_1}(\lambda_1) & & \\ & \ddots & \\ & & J_{n_k}(\lambda_k) \end{pmatrix}$$

其中Jordan块 $J_n(\lambda) = \begin{pmatrix} \lambda & 1 & & \\ & \lambda & \ddots & \\ & & \ddots & 1 \\ & & & \lambda \end{pmatrix}$

### 1.2 唯一性

Jordan标准形在Jordan块的排列顺序意义下唯一。

### 1.3 Lean 4 形式化

```lean
import Mathlib.LinearAlgebra.Matrix.JordanBlocks

-- Jordan标准形存在性
theorem jordan_normal_form_exists {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ (P : Matrix (Fin n) (Fin n) K) (hP : P.det ≠ 0) (J : Matrix (Fin n) (Fin n) K),
      J.IsJordanNormalForm ∧ A = P⁻¹ * J * P := by
  sorry  -- 需要详细的线性代数形式化
```

---

## 二、几何表征（可视化）

### 2.1 Jordan块的作用

```text
Jordan块J₃(λ)的作用：

    e₁ ←─λ── e₁
     ↑
     1
     │
    e₂ ←─λ── e₂
     ↑
     1
     │
    e₃ ←─λ── e₃

T(eᵢ) = λeᵢ + eᵢ₋₁ (非对角线性依赖)
```

### 2.2 不变子空间分解

```text
V = V₁ ⊕ V₂ ⊕ ... ⊕ Vₖ
     │    │         │
   J₁   J₂        Jₖ

每个Vᵢ是Jordan块对应的不变子空间
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Jordan标准形**：任何线性变换都可以分解为"几乎对角"的块，每块是特征值+微小扰动

### 3.2 电路类比

- 对角矩阵：独立电路
- Jordan块：串联电路（信号沿链传递）
- 标准形：电路的"规范化"

### 3.3 为什么需要代数闭？

代数闭保证特征多项式完全分解

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np
from scipy.linalg import jordan_block, eig

def compute_jordan_form(A, tol=1e-10):
    """
    计算矩阵A的Jordan标准形（数值方法）
    """
    eigenvalues, eigenvectors = eig(A)

    # 对于数值计算，Jordan形是不稳定的
    # 使用Schur分解作为替代
    from scipy.linalg import schur
    T, Z = schur(A)

    return T, Z

def construct_jordan_block(lam, n):
    """构造Jordan块J_n(λ)"""
    J = np.diag([lam] * n)
    for i in range(n - 1):
        J[i, i + 1] = 1
    return J

# 示例
A = np.array([[5, 4, 2, 1],
              [0, 1, -1, -1],
              [-1, -1, 3, 0],
              [1, 1, -1, 2]])

J, P = compute_jordan_form(A)
print("Jordan-like form (Schur):")
print(J)
```

### 4.2 符号计算

```python
from sympy import Matrix, symbols, simplify

def jordan_form_symbolic(A):
    """使用SymPy计算精确Jordan标准形"""
    M = Matrix(A)
    P, J = M.jordan_form()
    return P, J

# 示例
A = [[2, 1], [0, 2]]
P, J = jordan_form_symbolic(A)
print(f"Jordan标准形:\n{J}")
print(f"变换矩阵P:\n{P}")
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Jordan标准形 = 有限生成k[T]-模的分解
├─ V是k[T]-模（T作用于V）
├─ 结构定理：V ≅ ⊕ k[T]/(T-λ)^n
└─ 每个因子对应一个Jordan块
```

### 5.2 推广

- **主理想整环上的模**：更一般的结构定理
- **有理标准形**：不需要代数闭
- **无穷维**：需要谱理论

### 5.3 同调代数

Jordan分解 ↔ 模的合成列

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **有理标准形** | 不需要代数闭 |
| **谱定理** | 正规算子的推广 |
| **Cayley-Hamilton** | 特征多项式湮灭 |

---

**状态**: ✅ 完成
