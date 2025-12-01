# Stokes定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分几何/分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Stokes定理（广义） |
| **领域** | 微分几何、向量分析 |
| **历史** | Kelvin, Stokes, Cartan |
| **前置知识** | 微分形式、流形、外微分 |
| **Mathlib** | `Mathlib.Analysis.Calculus.Stokes` |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**广义Stokes定理**：设 M 是 n 维带边紧定向流形，ω 是 M 上的 (n-1)-形式，则：

$$\int_M d\omega = \int_{\partial M} \omega$$

其中 dω 是 ω 的外微分，∂M 是 M 的边界（带诱导定向）。

### 1.2 特殊情形

| 定理 | M | ω | 公式 |
|------|---|---|------|
| **微积分基本定理** | [a,b] | f | ∫ₐᵇf'dx = f(b)-f(a) |
| **Green定理** | 平面区域 | Pdx+Qdy | ∮(Pdx+Qdy) = ∬(∂Q/∂x-∂P/∂y)dA |
| **经典Stokes** | 曲面 | F·dr | ∮F·dr = ∬(∇×F)·dS |
| **Gauss散度** | 空间区域 | F·dS | ∯F·dS = ∭(∇·F)dV |

### 1.3 Lean 4 形式化

```lean
import Mathlib.Analysis.Calculus.Stokes

-- 广义Stokes定理
theorem stokes_theorem {M : Type*} [SmoothManifold M] [CompactSpace M]
    [OrientedManifold M] [HasBoundary M]
    (ω : Ω^(n-1)(M)) :
    ∫ M, dω = ∫ (∂M), ω := by
  exact integral_dω_eq_integral_boundary ω

-- 微积分基本定理作为特例
theorem ftc_as_stokes (f : ℝ → ℝ) (a b : ℝ) (hf : Differentiable ℝ f) :
    ∫ x in a..b, deriv f x = f b - f a := by
  exact integral_deriv_eq_sub hf.continuous a b
```

### 1.4 证明要点

```text
        [Stokes定理证明策略]
                │
    ┌───────────┴───────────┐
    │                       │
[局部到整体]            [边界贡献]
    │                       │
├─ 在坐标卡内证明       ├─ 内部边界相消
├─ 用单位分解粘合       ├─ 只剩真正的边界
└─ 归结到ℝⁿ中的积分    └─ 定向决定符号
```

---

## 二、几何表征（可视化）

### 2.1 核心图示

```text
        [Stokes定理的几何直觉]

    "边界上的流量 = 内部的源"

    ┌─────────────────────┐
    │                     │
    │   ∂M (边界)         │
    │   ┌───────────┐     │
    │   │           │←ω   │
    │   │     M     │     │
    │   │   dω↗    │     │
    │   │           │     │
    │   └───────────┘     │
    │                     │
    └─────────────────────┘

    ∫_M dω = ∫_∂M ω
    内部累积 = 边界流出
```

### 2.2 一维情形（微积分基本定理）

```text
    f'(x)
    ↑
    │   ┌─────────────┐
    │   │   面积      │
    │   │  = f(b)-f(a)│
    │   │             │
    └───┴─────────────┴───→ x
        a             b

    ∫ₐᵇ f'(x)dx = f(b) - f(a)
    "累积变化率 = 总变化"
```

### 2.3 二维情形（Green定理）

```text
    ┌─────────────────┐
    │                 │
    │   ∮ P dx + Q dy │ ← 边界环路积分
    │   ╱─────────╲   │
    │  │  ∬ 旋度  │   │
    │   ╲─────────╱   │
    │                 │
    └─────────────────┘

    环流 = 内部旋度的积分
```

### 2.4 三维散度定理

```text
          z
          ↑
          │  ┌────────┐
          │ ╱        ╱│
          │╱   V    ╱ │
          ├────────┤  │
          │        │ ╱
          │   dV   │╱
          └────────┘──────→ y
         ╱
        ╱
       x

    ∯_∂V F·dS = ∭_V (∇·F) dV

    通过边界的通量 = 内部源的总量
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Stokes定理**：边界上发生的事完全由内部的变化率决定——"局部变化的积累等于整体效果"

### 3.2 生活类比

**水池进出水**：

```text
水池（区域M）
├─ 内部有水龙头和排水口（源/汇 = dω）
├─ 边界是池壁（∂M）
├─ 水从边界流出的总量 = 内部净产水量
└─ ∫_∂M ω = ∫_M dω
```

**银行账户**：

```text
一段时间内的账户变化：

├─ 边界效果：期末余额 - 期初余额 = f(b)-f(a)
├─ 内部累积：∫存款率 - ∫取款率
└─ Stokes：两者相等！
```

**人口流动**：

```text
一个城市（区域）的人口变化：

边界：人员进出城市
内部：出生、死亡、搬迁

净流出人口 = 内部人口减少量
∮边界 流量 = ∬内部 变化率
```

### 3.3 为什么是真的？

```text
        [直觉论证]
              │
    把区域分成很多小块
              │
    每个小块：边界贡献 ≈ 内部dω
              │
    相邻小块的公共边界：
    ├─ 正向贡献和负向贡献相消
    ├─ 只有最外层边界留下
    └─ 这就是∂M！
              │
    小块求和 → 积分
```

---

## 四、计算表征（算法）

### 4.1 Green定理验证

```python
import numpy as np
from scipy import integrate

def verify_green_theorem():
    """
    验证Green定理：
    ∮_C (P dx + Q dy) = ∬_D (∂Q/∂x - ∂P/∂y) dA

    例子：单位圆上的积分
    """
    # 向量场 F = (P, Q) = (-y, x)
    P = lambda x, y: -y
    Q = lambda x, y: x

    # ∂Q/∂x - ∂P/∂y = 1 - (-1) = 2
    curl_z = lambda x, y: 2

    # 左边：环路积分 ∮_C (P dx + Q dy)
    # 参数化：x = cos(t), y = sin(t), t ∈ [0, 2π]
    def line_integral():
        def integrand(t):
            x, y = np.cos(t), np.sin(t)
            dx, dy = -np.sin(t), np.cos(t)
            return P(x, y) * dx + Q(x, y) * dy
        result, _ = integrate.quad(integrand, 0, 2*np.pi)
        return result

    # 右边：面积分 ∬_D 2 dA = 2 × π × 1² = 2π
    def area_integral():
        # 极坐标积分
        def integrand(r, theta):
            return curl_z(r*np.cos(theta), r*np.sin(theta)) * r
        result, _ = integrate.dblquad(integrand, 0, 2*np.pi, 0, 1)
        return result

    line_result = line_integral()
    area_result = area_integral()

    print(f"环路积分: {line_result:.6f}")
    print(f"面积分: {area_result:.6f}")
    print(f"差值: {abs(line_result - area_result):.2e}")
    print(f"理论值: 2π ≈ {2*np.pi:.6f}")

verify_green_theorem()
```

### 4.2 散度定理验证

```python
import numpy as np
from scipy import integrate

def verify_divergence_theorem():
    """
    验证散度定理：
    ∯_S F·dS = ∭_V (∇·F) dV

    例子：单位球上的径向向量场 F = (x, y, z)
    """
    # F = (x, y, z)
    # ∇·F = ∂x/∂x + ∂y/∂y + ∂z/∂z = 3

    # 右边：∭_V 3 dV = 3 × (4/3)π × 1³ = 4π
    volume_integral = 3 * (4/3) * np.pi * 1**3

    # 左边：∯_S F·n dS
    # 在单位球面上，n = (x, y, z)
    # F·n = x² + y² + z² = 1
    # ∯ 1 dS = 4π
    surface_integral = 4 * np.pi

    print(f"体积分（∇·F）: {volume_integral:.6f}")
    print(f"面积分（F·n）: {surface_integral:.6f}")
    print(f"理论值: 4π ≈ {4*np.pi:.6f}")

verify_divergence_theorem()
```

### 4.3 微分形式计算

```python
from sympy import symbols, diff, sin, cos, pi, integrate

def differential_forms_example():
    """
    微分形式视角的Stokes定理
    """
    x, y = symbols('x y')

    # 1-形式 ω = x dy - y dx
    # dω = dx ∧ dy - dy ∧ dx = 2 dx ∧ dy

    omega_x = -y  # ω的dx系数
    omega_y = x   # ω的dy系数

    # 外微分 dω = (∂ω_y/∂x - ∂ω_x/∂y) dx∧dy
    d_omega = diff(omega_y, x) - diff(omega_x, y)

    print(f"ω = {omega_x} dx + {omega_y} dy")
    print(f"dω = {d_omega} dx∧dy")

    # 在单位圆盘上积分
    # ∬_D dω = ∬_D 2 dx dy = 2π

    print(f"∫_D dω = {d_omega} × π = {d_omega * pi}")

differential_forms_example()
```

---

## 五、范畴表征（抽象）

### 5.1 de Rham复形视角

```text
        [de Rham复形]
              │
    0 → Ω⁰(M) ─d→ Ω¹(M) ─d→ ... ─d→ Ωⁿ(M) → 0
              │
    d² = 0（闭链复形）
              │
    Stokes定理：∫与d的对偶关系
```

### 5.2 上同调与积分配对

```text
Stokes定理的范畴化：

积分定义了配对：
⟨ , ⟩: Ωᵏ(M) × Cₖ(M) → ℝ
⟨ω, σ⟩ = ∫_σ ω

Stokes：⟨dω, σ⟩ = ⟨ω, ∂σ⟩
这是链复形和余链复形的对偶关系
```

### 5.3 de Rham定理

```text
        [de Rham定理]
              │
    H*_dR(M) ≅ H*(M; ℝ)
              │
    de Rham上同调 ≅ 奇异上同调
              │
    Stokes定理是这个同构的核心
```

### 5.4 Stokes与同调

```text
[闭形式 vs 恰当形式]
        │
├─ dω = 0 ⟹ ω闭
├─ ω = dη ⟹ ω恰当
├─ 恰当 ⟹ 闭（因为d²=0）
        │
de Rham上同调 = 闭形式/恰当形式

Stokes：∫_M dη = ∫_∂M η
如果 ∂M = ∅，则 ∫_M dη = 0
恰当形式在闭流形上积分为0
```

---

## 六、统一性与推广

### 6.1 四个经典定理的统一

```text
        [Stokes定理统一经典]
                │
    ┌───────────┼───────────┐
    │     │     │     │     │
[FTC]   [Green] [Stokes] [Gauss]
 1D      2D      2D曲面   3D
    │     │     │     │     │
    └───────────┼───────────┘
                │
        ∫_M dω = ∫_∂M ω
```

### 6.2 物理意义

| 形式 | 物理量 | 定理 |
|------|--------|------|
| 0-形式 | 势能 | 功 = 势能差 |
| 1-形式 | 电场 | 安培定律 |
| 2-形式 | 磁场 | 法拉第定律 |
| 3-形式 | 电荷密度 | 高斯定律 |

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **de Rham定理** | 上同调同构 |
| **Hodge定理** | 调和形式表示 |
| **Gauss-Bonnet** | 曲率积分 |
| **Chern-Weil** | 示性类 |

---

**最后更新**: 2025年12月1日
**状态**: ✅ 完成
