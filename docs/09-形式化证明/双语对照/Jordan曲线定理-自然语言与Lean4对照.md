---
title: "Jordan 曲线定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.100A / 拓扑学"
---

## 定理陈述

**自然语言**：平面上任意一条简单闭曲线（Jordan 曲线）将平面恰好分成两个连通分支：一个有界的内部（interior）和一个无界的外部（exterior）。

形式化表述：对于任何连续单射 \(f : S^1 \to \mathbb{R}^2\)，补集 \(\mathbb{R}^2 \setminus f(S^1)\) 恰好有两个连通分支。

**Lean4**：

```lean
import Mathlib

open Topology TopologicalSpace Filter

-- Jordan 曲线：S¹ 到平面的连续嵌入
def JordanCurve : Type := {f : Circle → ℝ² // Continuous f ∧ Function.Injective f}

def JordanCurve.image (c : JordanCurve) : Set ℝ² := Set.range c.val
def JordanCurve.complement (c : JordanCurve) : Set ℝ² := (image c)ᶜ

-- 连通分支数（占位定义）
def connectedComponentsCount (s : Set ℝ²) : ℕ :=
  sorry

-- Jordan 曲线定理主定理（axiom 占位）
axiom jordan_curve_theorem (c : JordanCurve) :
    connectedComponentsCount (JordanCurve.complement c) = 2

-- 进一步细化：一个有界，一个无界
axiom jordan_curve_bounded_unbounded (c : JordanCurve) :
    ∃ U V : Set ℝ²,
    JordanCurve.complement c = U ∪ V ∧
    U ∩ V = ∅ ∧
    IsConnected U ∧ IsConnected V ∧
    Bornology.IsBounded U ∧ ¬Bornology.IsBounded V
```

## 证明思路

**自然语言**：Jordan 曲线定理的证明在历史上被认为极其困难。现代常见的证明路线有两条：

1. **组合/图论路线**（Hales, 2005, Mizar）：将曲线多边形近似，利用图论的平面嵌入理论。
2. **代数拓扑路线**：利用 Alexander 对偶计算补集的同调群 \(\tilde{H}_0(\mathbb{R}^2 \setminus C) \cong \mathbb{Z}\)，从而得到两个连通分支。

**Lean4**：由于完整证明的极端复杂性，当前版本使用 `axiom` 标记核心命题，并提供详细的证明思路和非形式化证明概要。以下展示环绕数方法的框架：

```lean
-- 环绕数定义（框架）
def WindingNumber (c : JordanCurve) (p : ℝ²) (hp : p ∉ JordanCurve.image c) : ℤ :=
  sorry  -- 可用积分 (1/2πi) ∮_C dz/(z-p) 定义

-- 环绕数刻画内部与外部
axiom winding_number_interior (c : JordanCurve) (p : ℝ²) (hp : p ∉ JordanCurve.image c) :
    WindingNumber c p hp ≠ 0 ↔
    Bornology.IsBounded (connectedComponentIn (JordanCurve.complement c) {p})
```

## 关键 tactic 教学

- `def ... := sorry`：在形式化中，`sorry` 表示“此处留待后续填充”。它是构建大型证明框架时的重要工具。
- `axiom`：声明一个不加证明的基本命题。常用于标记当前库尚未实现、但数学上已知的定理。
- `ext x` / `constructor`：集合相等和存在量词证明中的常用 tactic，分别对应“外延法”和“分向证明”。

## 练习

1. 为什么 Jordan 曲线定理在 \(\mathbb{R}^2\) 中成立，而在 \(\mathbb{R}^3\) 中没有直接类比？
2. 尝试用环绕数的语言解释：为什么曲线内部的点环绕数为 \(\pm 1\)，而外部为 \(0\)？
3. 查找 Hales (2005) 的 Mizar 形式化，了解组合证明的大致代码规模。
