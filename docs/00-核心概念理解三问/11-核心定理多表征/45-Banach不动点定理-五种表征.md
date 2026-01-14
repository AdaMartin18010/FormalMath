# Banach不动点定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 泛函分析/度量空间
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Banach不动点定理（压缩映射原理） |
| **领域** | 泛函分析/度量空间 |
| **发现者** | Stefan Banach (1922) |
| **前置知识** | 完备度量空间、压缩映射 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Banach不动点定理**：设(X,d)是完备度量空间，T: X→X是压缩映射（存在0≤k<1使得d(Tx,Ty)≤k·d(x,y)），则：
1. T有唯一不动点x*
2. 对任意x₀∈X，序列xₙ = T(xₙ₋₁)收敛到x*

### 1.2 收敛速度

$$d(x_n, x^*) \leqqq \frac{k^n}{1-k} d(x_0, x_1)$$

### 1.3 Lean 4 形式化

```lean
import Mathlib.Topology.MetricSpace.Contracting

-- Banach不动点定理
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X]
    {T : X → X} (hT : ContractingWith k T) (hk : k < 1) :
    ∃! x : X, T x = x := by
  exact hT.exists_unique_fixedPoint hk
```

---

## 二、几何表征（可视化）

### 2.1 迭代收敛

```text
压缩映射的迭代：

    x₀ → x₁ → x₂ → ... → x*
     │    │    │
     T    T    T

每次迭代距离缩小k倍
```

### 2.2 图形解释

```text
    y
    ↑
    │    ╱ y=x
    │  ╱
    │╱ y=T(x)
    ├──•──•──•──•── x*
    │
    └──────────────→ x

斜率<1的曲线与y=x的唯一交点
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Banach不动点**：如果每次操作都让距离缩小，反复操作后必定趋于稳定

### 3.2 调焦类比

- 相机对焦：每次调整缩小误差
- 压缩映射：每次迭代缩小距离
- 不动点：完美对焦位置

### 3.3 为什么需要完备？

完备性保证Cauchy序列收敛，否则极限可能"不存在"

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np

def banach_iteration(T, x0, tol=1e-10, max_iter=1000):
    """
    Banach迭代求不动点
    """
    x = x0
    for i in range(max_iter):
        x_new = T(x)
        if np.linalg.norm(x_new - x) < tol:
            print(f"收敛于第{i+1}次迭代")
            return x_new
        x = x_new
    print("未收敛")
    return x

# 示例：求√2（x² = 2的解）
# T(x) = (x + 2/x) / 2 是压缩映射
T = lambda x: (x + 2/x) / 2
x_star = banach_iteration(T, 1.0)
print(f"√2 ≈ {x_star}, 误差 = {abs(x_star - np.sqrt(2))}")
```

### 4.2 误差估计

```python
def error_bound(x0, x1, k, n):
    """
    计算第n次迭代的误差上界
    d(xₙ, x*) ≤ kⁿ/(1-k) × d(x₀, x₁)
    """
    d01 = abs(x1 - x0)
    return (k ** n / (1 - k)) * d01

# 示例
k = 0.5  # 压缩系数
for n in [1, 5, 10, 20]:
    bound = error_bound(1.0, 1.5, k, n)
    print(f"n={n}: 误差上界 = {bound:.2e}")
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Banach不动点 = 函子的不动点
├─ T: X → X 是自函子
├─ 不动点x*: T(x*) = x*
├─ 压缩性保证唯一性和存在性
└─ 完备性保证收敛
```

### 5.2 推广

- **非扩张映射**：不动点存在但不一定唯一
- **Brouwer不动点**：连续映射的不动点（存在性）
- **Schauder不动点**：紧算子版本

### 5.3 应用领域

```text
Banach不动点的应用：
├─ 微分方程：Picard存在性定理
├─ 积分方程：Fredholm方程
├─ 数值分析：迭代法收敛性
└─ 博弈论：Nash均衡
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Brouwer不动点** | 连续映射版本 |
| **Schauder不动点** | 紧算子版本 |
| **Picard-Lindelöf** | 应用 |

---

**状态**: ✅ 完成
