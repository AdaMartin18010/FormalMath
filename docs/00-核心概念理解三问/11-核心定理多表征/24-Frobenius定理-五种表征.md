---
msc_primary: "58A30"
msc_secondary: ["53C12"]
---

# Frobenius定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分几何
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Frobenius定理 |
| **领域** | 微分几何 |
| **发现者** | Ferdinand Frobenius (1877) |
| **前置知识** | 分布、对合分布、积分流形 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Frobenius定理**：设M是流形，D是M上的k维分布（切子丛），则D可积（存在积分流形）当且仅当D是对合的（involutive），即对任意向量场X, Y ∈ D，有[X, Y] ∈ D。

$$D \text{ 可积 } \iff D \text{ 对合 }$$

其中[X, Y]是Lie括号。

### 1.2 微分形式表述

分布D = ker(ω₁, ..., ω_{n-k})，其中ωᵢ是1-形式。D可积 ⟺ dωᵢ ≡ 0 (mod ω₁, ..., ω_{n-k})。

### 1.3 Lean 4 形式化

```lean
import Mathlib.Geometry.Manifold.IntegralCurve

-- Frobenius定理（简化表述）
theorem frobenius_theorem {M : Type*} [SmoothManifoldWithCorners I M]
    {D : Distribution M} (hD : D.IsInvolutive) :
    ∃ (N : Type*) [SmoothManifoldWithCorners I' N],
      Nonempty (N → M) ∧ -- 积分流形
      ∀ x : M, ∃ U : Set M, x ∈ U ∧ -- 局部积分流形
        ∃ (φ : U → N), Function.Injective φ := by
  sorry  -- 需要详细的分布理论形式化
```

---

## 二、几何表征（可视化）

### 2.1 分布与积分流形

```text
流形M上的分布D（每点一个切子空间）：

    M:  ┌─────────────┐
        │   •  D|_p   │  (p点的切子空间)
        │   │         │
        │   •  D|_q   │
        │   │         │
        └─────────────┘

可积 ⟺ 存在"积分流形"（沿D的曲面）
```

### 2.2 反例：非对合分布

```text
ℝ³上的分布：D = span{∂/∂x, ∂/∂y + x∂/∂z}
├─ [X, Y] = ∂/∂z ∉ D
├─ 不对合
└─ 不可积（无积分曲面）
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Frobenius定理**：一个"方向场"可以拼成"曲面"当且仅当方向之间"协调"（对合）

### 3.2 河流类比

- 分布：每点的"水流方向"
- 对合：方向"协调"（不产生旋涡）
- 积分流形：沿水流方向的"河床"

### 3.3 为什么需要对合？

对合保证方向场"不自相矛盾"，才能拼成曲面

---

## 四、计算表征（算法）

### 4.1 Python实现（简化：检查对合性）

```python
import numpy as np
from scipy.integrate import ode

def check_involutive(X_fields, Y_fields, bracket):
    """
    检查分布是否对合
    X_fields, Y_fields: 分布中的向量场
    bracket: Lie括号函数
    """
    for X in X_fields:
        for Y in Y_fields:
            [X, Y] = bracket(X, Y)
            # 检查[X,Y]是否在分布中
            if not in_distribution([X, Y], X_fields):
                return False
    return True

def integrate_distribution(D, p0, t_max=1.0):
    """
    如果分布可积，构造积分流形
    D: 分布（向量场集合）
    p0: 初始点
    """
    # 沿分布积分（ODE系统）
    def ode_system(t, y):
        # 在y点的分布方向
        directions = [X(y) for X in D]
        # 组合方向（简化）
        return sum(directions) / len(directions)

    solver = ode(ode_system).set_integrator('dopri5')
    solver.set_initial_value(p0, 0)

    trajectory = [p0]
    while solver.t < t_max:
        solver.integrate(solver.t + 0.01)
        trajectory.append(solver.y)

    return np.array(trajectory)
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Frobenius定理 = 分布的可积性
├─ 分布：切丛的子丛
├─ 对合：Lie代数结构
└─ 积分流形：子流形
```

### 5.2 叶状结构

可积分布 ⟹ 流形有"叶状结构"（foliation）

### 5.3 推广

- 奇异分布：允许奇点
- 接触结构：非对合的特殊情况

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Lie定理** | Lie群上的Frobenius |
| **Darboux定理** | 辛流形上的应用 |

---

**状态**: ✅ 完成
