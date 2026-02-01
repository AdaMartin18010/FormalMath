---
msc_primary: "55M20"
msc_secondary: ["54H25"]
---

# Brouwer不动点定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 代数拓扑
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Brouwer不动点定理 |
| **领域** | 代数拓扑 |
| **发现者** | L.E.J. Brouwer (1911) |
| **前置知识** | 连续映射、同调/同伦 |
| **Mathlib** | 需要高级拓扑库 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**定理（Brouwer不动点定理）**：设 Dⁿ = {x ∈ ℝⁿ : ‖x‖ ≤ 1} 是n维闭球（闭盘），f: Dⁿ → Dⁿ 是连续映射，则存在 x*∈ Dⁿ 使得 f(x*) = x*。

**等价表述**：不存在从 Dⁿ 到其边界 Sⁿ⁻¹ 的连续收缩。

### 1.2 特殊情形

| n | 空间 | 定理 |
|---|------|------|
| 1 | [0,1] | 介值定理推论 |
| 2 | 闭圆盘 | 任何连续自映射有不动点 |
| n | n维闭球 | 一般情形 |

### 1.3 Lean形式化（概念性）

```lean
-- Brouwer不动点定理（概念性表述）
-- 实际形式化需要同调论或其他高级工具

theorem brouwer_fixed_point {n : ℕ} (f : ClosedBall n → ClosedBall n)
    (hf : Continuous f) :
    ∃ x : ClosedBall n, f x = x := by
  sorry -- 证明需要同调论

-- 等价表述：不存在收缩
theorem no_retraction {n : ℕ} :
    ¬∃ (r : ClosedBall n → Sphere n), Continuous r ∧
      ∀ x : Sphere n, r (inclusion x) = x := by
  sorry -- 同调论证明
```

### 1.4 证明策略

```text
        [Brouwer定理证明路线]
                │
    ┌───────────┼───────────┐
    │           │           │
[同调论]    [同伦论]    [组合论]
    │           │           │
H_n(Sⁿ)≠0  π_{n-1}(Sⁿ⁻¹)  Sperner引理
    │           │           │
无收缩     无收缩      三角剖分
    │           │           │
    └───────────┼───────────┘
                │
        不存在无不动点的映射
```

---

## 二、几何表征（可视化）

### 2.1 一维情形（介值定理）

```text
    y
    ↑
   1├─────────────●
    │           ╱
    │         ╱
    │       ╱ ← y = x
    │     ●
    │   ╱
   0├─●─────────────→ x
    0           1

f: [0,1] → [0,1] 连续
f的图像从 (0,f(0)) 到 (1,f(1))
必与对角线 y=x 相交！
```

### 2.2 二维情形

```text
    [闭圆盘 → 闭圆盘的连续映射]

         ┌─────────┐
        ╱   ╲     ╱
       ╱  ●  ╲   ╱   ← 不动点
      │   │   │ │
       ╲  │  ╱   ╲
        ╲ ↓ ╱     ╲
         └─────────┘

    无论怎么"揉"这个圆盘
    总有一个点不动！
```

### 2.3 不存在收缩

```text
    [为什么圆盘不能收缩到边界？]

    假设存在收缩 r: D² → S¹

         ┌─────────┐
        ╱           ╲
       ╱    圆盘     ╲
      │      ↓       │ ← 收缩
       ╲    边界    ╱
        ╲         ╱
         └───────┘

    但这会导致 S¹ ≃ 点（可缩）
    矛盾！（S¹ 有非平凡基本群）
```

### 2.4 咖啡杯比喻

```text
搅拌咖啡时：

    ┌─────────────┐
    │  ~~~~~~~~   │
    │ ～～～～～  │ ← 咖啡表面
    │  ~~~~~~~~   │
    │     ●       │ ← 总有一点
    │  液体       │    不移动！
    └─────────────┘

    假设搅拌是连续的
    由Brouwer定理，必有不动点
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Brouwer不动点定理**：在有限范围内连续移动物体，至少有一个点回到原位

### 3.2 生活类比

**地图类比**：

```text
把一张地图放在它所描绘的区域上方

    ┌──────────────┐
    │    地图      │
    │   ┌─────┐    │
    │   │实际 │    │
    │   │区域 │    │
    │   └─────┘    │
    └──────────────┘

    有一个点同时在"地图上"和"实际位置"重合
    这就是不动点！
```

**揉面团类比**：

```text
揉面团（连续变形）：

    ●  ← 原始位置
    ↓
    ○  ← 变形后

无论怎么揉，总有一点
在变形前后位置相同！
（除非把面团撕开——不连续）
```

### 3.3 为什么是真的？

**直觉论证（反证法）**：

```text
假设 f: Dⁿ → Dⁿ 没有不动点
则对每个 x，f(x) ≠ x

可以构造"收缩"：
从 x 出发，经过 f(x)，延长到边界

    x ────→ f(x) ────→ 边界上的点

这定义了 r: Dⁿ → Sⁿ⁻¹
但这样的收缩不存在！（拓扑阻碍）
```

---

## 四、计算表征（算法）

### 4.1 一维情形

```python
def fixed_point_1d(f, a=0, b=1, tol=1e-10):
    """
    找 f: [a,b] → [a,b] 的不动点
    使用二分法找 g(x) = f(x) - x 的零点
    """
    g = lambda x: f(x) - x

    # 边界情况
    if abs(g(a)) < tol:
        return a
    if abs(g(b)) < tol:
        return b

    # 二分法
    while b - a > tol:
        c = (a + b) / 2
        if g(a) * g(c) <= 0:
            b = c
        else:
            a = c

    return (a + b) / 2

# 例：f(x) = cos(x)
import math
fp = fixed_point_1d(math.cos, 0, 1)
print(f"cos(x) = x 的解：{fp:.10f}")
```

### 4.2 二维情形（数值方法）

```python
import numpy as np
from scipy.optimize import fsolve

def fixed_point_2d(f, x0):
    """
    找 f: D² → D² 的不动点
    f 应该返回 numpy array
    """
    g = lambda x: f(x) - x
    solution = fsolve(g, x0)
    return solution

# 例：旋转+收缩
def rotation_contraction(x, theta=0.5, k=0.8):
    """旋转 theta 并缩放 k"""
    c, s = np.cos(theta), np.sin(theta)
    R = np.array([[c, -s], [s, c]])
    return k * R @ x

fp = fixed_point_2d(rotation_contraction, np.array([0.5, 0.5]))
print(f"不动点: {fp}")  # 应该接近原点
```

### 4.3 Sperner引理验证

```python
def sperner_lemma_demo(n_divisions=8):
    """
    演示Sperner引理：
    三角形的组合版Brouwer定理
    """
    # 三角形顶点标记
    # 顶点 A(0), B(1), C(2)
    # 每个小三角形的顶点标记遵循Sperner条件

    # 构造标记函数（满足边界条件）
    def label(i, j):
        # i, j 是重心坐标的分子
        # 返回 0, 1, 或 2
        k = n_divisions - i - j

        # 边界条件
        if j == 0:  # AB边
            return 0 if i < n_divisions // 2 else 1
        if i == 0:  # AC边
            return 0 if j < n_divisions // 2 else 2
        if k == 0:  # BC边
            return 1 if i > 0 else 2

        # 内部点：简单规则
        return (i + j) % 3

    # 找完全标记的小三角形（包含0,1,2）
    complete = []
    for i in range(n_divisions):
        for j in range(n_divisions - i):
            # 向上的三角形
            labels = {label(i, j), label(i+1, j), label(i, j+1)}
            if labels == {0, 1, 2}:
                complete.append((i, j, 'up'))

            # 向下的三角形（如果存在）
            if i + j + 1 < n_divisions:
                labels = {label(i+1, j), label(i, j+1), label(i+1, j+1)}
                if labels == {0, 1, 2}:
                    complete.append((i, j, 'down'))

    print(f"分割数: {n_divisions}")
    print(f"完全标记三角形数: {len(complete)}")
    print(f"Sperner引理保证至少有1个（实际是奇数个）")
    return complete

sperner_lemma_demo(16)
```

---

## 五、范畴表征（抽象）

### 5.1 同调论视角

```text
        [同调证明思路]
              │
    Hₙ(Dⁿ) = 0（球是可缩的）
    Hₙ(Sⁿ⁻¹) = ℤ（球面非平凡）
              │
    如果存在收缩 r: Dⁿ → Sⁿ⁻¹
    则 r*: Hₙ(Sⁿ⁻¹) → Hₙ(Dⁿ)
              │
    但 ℤ → 0 不能是单射
    矛盾！
```

### 5.2 同伦论视角

```text
        [同伦证明思路]
              │
    πₙ₋₁(Sⁿ⁻¹) ≅ ℤ（球面的同伦群）
    πₙ₋₁(Dⁿ) = 0（球可缩）
              │
    包含映射 i: Sⁿ⁻¹ ↪ Dⁿ
    不能有左逆（收缩）
              │
    因为 ℤ → 0 → ℤ 不能是恒等
```

### 5.3 Lefschetz不动点定理

```text
        [推广：Lefschetz定理]
              │
    Lefschetz数 L(f) = Σ(-1)ⁱ tr(f*: Hᵢ → Hᵢ)
              │
    L(f) ≠ 0 ⟹ f有不动点
              │
    对于 f: Dⁿ → Dⁿ：
    L(f) = 1（因为 Dⁿ 可缩）
    ⟹ f 有不动点
```

### 5.4 不动点指数

```text
在范畴 Top* （带点拓扑空间）中：

不动点 ↔ 某个函子的零点
不动点指数 ↔ 代数计数

这是代数拓扑方法的核心思想
```

---

## 六、应用与推广

### 6.1 经典应用

| 应用 | 领域 |
|------|------|
| Nash均衡存在性 | 博弈论 |
| Arrow不可能定理 | 社会选择 |
| 微分方程解的存在 | 分析 |
| 数值方法收敛 | 计算数学 |

### 6.2 推广

| 推广 | 内容 |
|------|------|
| **Schauder** | Banach空间中的凸紧集 |
| **Kakutani** | 集值映射 |
| **Lefschetz** | 一般紧流形 |
| **Atiyah-Bott** | 椭圆复形 |

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **介值定理** | 一维特例 |
| **Borsuk-Ulam** | 球面的对径点 |
| **Ham sandwich** | 测度分割 |
| **Jordan曲线** | 平面分离 |

---

**最后更新**: 2025年12月1日
**状态**: ✅ 完成
