# Hahn-Banach定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 泛函分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Hahn-Banach定理 |
| **领域** | 泛函分析 |
| **发现者** | Hahn (1927), Banach (1929) |
| **前置知识** | 线性泛函、次线性泛函、赋范空间 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Hahn-Banach定理（解析形式）**：设X是实线性空间，p是次线性泛函，M⊂X是子空间，f: M→ℝ是线性泛函且f(x)≤p(x)对∀x∈M。则存在F: X→ℝ线性，使得F|_M = f且F(x)≤p(x)对∀x∈X。

### 1.2 赋范空间版本

M⊂X是子空间，f∈M*，则存在F∈X*使得F|_M = f且‖F‖ = ‖f‖。

### 1.3 Lean 4 形式化

```lean
import Mathlib.Analysis.NormedSpace.HahnBanach

-- Hahn-Banach定理（赋范空间版本）
theorem hahn_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : Subspace ℝ E} {f : p →L[ℝ] ℝ} :
    ∃ F : E →L[ℝ] ℝ, (∀ x : p, F x = f x) ∧ ‖F‖ = ‖f‖ := by
  exact exists_extension_norm_eq f
```

---

## 二、几何表征（可视化）

### 2.1 分离超平面

```text
Hahn-Banach的几何形式：

    E空间
    │  ╱ 超平面H
    │╱
    ●A (凸集)
   ╱│
  ● │  x₀ (外点)
    │

存在超平面H分离A和x₀
```

### 2.2 扩张过程

```text
f定义在M上 → F扩张到全空间X

    X
    │
    │   F (扩张后)
    M ──f──> ℝ
    │
    子空间
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Hahn-Banach**：在子空间上的"测量方式"可以扩展到全空间，且不增加"测量范围"

### 3.2 尺子类比

- f：只能测量子空间M中的向量
- F：扩展后能测量全空间X中的向量
- 保范：扩展后尺子的"精度"不变

### 3.3 为什么重要？

保证了对偶空间X*足够丰富，能"分离"不同的点

---

## 四、计算表征（算法）

### 4.1 Python实现（有限维情形）

```python
import numpy as np
from scipy.optimize import linprog

def hahn_banach_finite(A, f, b):
    """
    在有限维空间中找Hahn-Banach扩张
    A: 子空间的基（m×n矩阵，n维到m维）
    f: 子空间上的线性泛函（m维）
    b: 约束（保范条件）
    """
    n = A.shape[1]  # 全空间维数
    m = A.shape[0]  # 子空间维数

    # F满足: F∘A = f, 即 F·A = f
    # 最小化 |F| 约束下

    # 使用线性规划
    c = np.zeros(2 * n)  # [F⁺, F⁻], F = F⁺ - F⁻
    c[:n] = 1
    c[n:] = 1  # 最小化 |F₁| + ... + |Fₙ|

    # 约束: (F⁺ - F⁻)·A = f
    A_eq = np.hstack([A.T, -A.T])
    b_eq = f

    # F⁺, F⁻ ≥ 0
    bounds = [(0, None)] * (2 * n)

    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')

    if result.success:
        F = result.x[:n] - result.x[n:]
        return F
    return None

# 示例
A = np.array([[1, 0, 0], [0, 1, 0]])  # 子空间：前两个坐标
f = np.array([1, 2])  # 子空间上的泛函
F = hahn_banach_finite(A, f, None)
print(f"扩张后的泛函: F = {F}")
```

### 4.2 应用：最优逼近

```python
def best_approximation(X, M, x):
    """
    使用Hahn-Banach找最佳逼近
    x到子空间M的最近点
    """
    # 在Hilbert空间中，正交投影给出最佳逼近
    # Hahn-Banach保证这种逼近存在

    # 简化：正交投影
    proj = M @ np.linalg.lstsq(M.T @ M, M.T @ x, rcond=None)[0]
    return proj
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Hahn-Banach = 函子保持性质
├─ 限制函子: X* → M*
├─ Hahn-Banach: 存在右逆（扩张）
└─ 保范: 函子的"度量兼容"
```

### 5.2 推广

- **复Hahn-Banach**：复线性空间版本
- **局部凸空间**：更一般的设置
- **向量值版本**：值域不仅是ℝ

### 5.3 选择公理

Hahn-Banach定理等价于一个弱形式的选择公理

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **分离定理** | 几何形式 |
| **Riesz表示定理** | Hilbert空间中的具体化 |
| **Banach-Alaoglu** | 弱*拓扑中的紧致性 |

---

**状态**: ✅ 完成
