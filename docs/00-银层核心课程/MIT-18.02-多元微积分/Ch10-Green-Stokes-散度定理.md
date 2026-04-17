---
title: "Ch10 Green定理、Stokes定理与散度定理"
level: silver
course: MIT 18.02 多元微积分
msc_primary: "26B20"
target_courses:
  - MIT 18.02
status: completed
created_at: 2026-04-18
---

# Ch10 Green定理、Stokes定理与散度定理

## 1. Green定理

**定理 1.1（Green定理）**。设 $C$ 为平面正向简单闭曲线，$D$ 为 $C$ 围成的区域，$P, Q$ 在 $D$ 上具有连续偏导数，则：

$$\oint_C P \, dx + Q \, dy = \iint_D \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dA$$

*证明概要*：分别证明 $\oint_C P \, dx = -\iint_D P_y \, dA$ 和 $\oint_C Q \, dy = \iint_D Q_x \, dA$。

对第一部分：设 $D = \{(x,y) \mid a \leq x \leq b, g_1(x) \leq y \leq g_2(x)\}$，则：

$$\iint_D P_y \, dA = \int_a^b \int_{g_1(x)}^{g_2(x)} P_y \, dy \, dx = \int_a^b [P(x, g_2(x)) - P(x, g_1(x))] \, dx$$

而 $\oint_C P \, dx = \int_{C_1} P \, dx + \int_{C_2} P \, dx$，其中 $C_1$ 为下边界（从左到右），$C_2$ 为上边界（从右到左）。所以：

$$\oint_C P \, dx = \int_a^b P(x, g_1(x)) \, dx - \int_a^b P(x, g_2(x)) \, dx = -\iint_D P_y \, dA$$

同理证明第二部分。$\square$

**推论 1.2（面积公式）**。区域 $D$ 的面积：

$$A = \frac{1}{2}\oint_C x \, dy - y \, dx = \oint_C x \, dy = -\oint_C y \, dx$$

## 2. Stokes定理

**定理 2.1（Stokes定理）**。设 $S$ 为光滑定向曲面，$C = \partial S$ 为其边界（正向），$\mathbf{F}$ 为光滑向量场，则：

$$\oint_C \mathbf{F} \cdot d\mathbf{r} = \iint_S (\nabla \times \mathbf{F}) \cdot d\mathbf{S}$$

其中 $d\mathbf{S} = \mathbf{n} \, dS$，$\mathbf{n}$ 为 $S$ 的单位法向量。

## 3. 散度定理（Gauss定理）

**定理 3.1（散度定理）**。设 $E$ 为空间有界闭区域，$S = \partial E$ 为其闭曲面（外侧），$\mathbf{F}$ 为光滑向量场，则：

$$\iint_S \mathbf{F} \cdot d\mathbf{S} = \iiint_E \nabla \cdot \mathbf{F} \, dV$$

## 4. 三大定理的统一性

Green、Stokes、散度定理都是**广义Stokes定理**的特例：

$$\int_{\partial M} \omega = \int_M d\omega$$

其中 $M$ 为带边定向流形，$\omega$ 为微分形式，$d\omega$ 为其外微分。

| 定理 | 维数 | $M$ | $\omega$ | $d\omega$ |
|------|------|-----|----------|----------|
| Newton-Leibniz | 1 | 区间 | $f$ | $df$ |
| Green | 2 | 平面区域 | $Pdx + Qdy$ | $(Q_x - P_y)dA$ |
| Stokes | 2 | 曲面 | $\mathbf{F} \cdot d\mathbf{r}$ | $(\nabla \times \mathbf{F}) \cdot d\mathbf{S}$ |
| 散度 | 3 | 立体区域 | $\mathbf{F} \cdot d\mathbf{S}$ | $(\nabla \cdot \mathbf{F}) dV$ |

## 5. 典型例题

**例题 5.1**。用 Green 定理计算 $\oint_C (x^2 - y) \, dx + (y^2 + x) \, dy$，$C$ 为圆 $x^2 + y^2 = 1$ 逆时针。

*解答*：$P = x^2 - y$，$Q = y^2 + x$。$Q_x - P_y = 1 - (-1) = 2$。

$$\oint_C = \iint_D 2 \, dA = 2 \cdot \pi \cdot 1^2 = 2\pi$$

**例题 5.2**。用散度定理求 $\iint_S \mathbf{F} \cdot d\mathbf{S}$，$\mathbf{F} = (x, y, z)$，$S$ 为单位球面。

*解答*：$\nabla \cdot \mathbf{F} = 1 + 1 + 1 = 3$。

$$\iint_S \mathbf{F} \cdot d\mathbf{S} = \iiint_E 3 \, dV = 3 \cdot \frac{4\pi}{3} = 4\pi$$

**例题 5.3**。求星形线 $x = a\cos^3 t$，$y = a\sin^3 t$ 围成的面积。

*解答*：利用面积公式：

$$A = \frac{1}{2}\oint_C x \, dy - y \, dx = \frac{1}{2}\int_0^{2\pi} [a\cos^3 t \cdot 3a\sin^2 t \cos t + a\sin^3 t \cdot 3a\cos^2 t \sin t] \, dt$$

$$= \frac{3a^2}{2}\int_0^{2\pi} \cos^2 t \sin^2 t \, dt = \frac{3\pi a^2}{8}$$

## 6. 练习题

1. 用 Green 定理计算 $\oint_C (x^3 - y^3) \, dx + (x^3 + y^3) \, dy$，$C$ 为 $x^2 + y^2 = 1$ 逆时针。
2. 验证 $\mathbf{F} = (x^2, y^2, z^2)$ 通过球面 $x^2 + y^2 + z^2 = R^2$ 的通量。
3. 解释为什么散度定理要求闭曲面。
4. 用 Stokes 定理计算 $\oint_C \mathbf{F} \cdot d\mathbf{r}$，$\mathbf{F} = (y, z, x)$，$C$ 为平面 $x + y + z = 1$ 在第一卦限的边界（逆时针从上方看）。

## 7. Lean4 形式化对照

```lean4
import Mathlib

-- Green 定理的二维形式（概念性）
example (P Q : ℝ → ℝ → ℝ) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (C : Path (ℝ × ℝ)) (hC : C.frontier = D) :
    ∮ C (P dx + Q dy) = ∫∫ D (deriv (Q x) x - deriv (P y) y) := by
  sorry

-- 散度定理（概念性）
example (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E) :
    ∫∫ (frontier E) (F · n) = ∫∫∫ E (divergence F) := by
  sorry
```

## 8. 应用

### 8.1 电磁学中的Maxwell方程

散度定理和Stokes定理是Maxwell方程的数学基础：

- $\nabla \cdot \mathbf{E} = \frac{\rho}{\varepsilon_0}$（高斯定律）
- $\nabla \times \mathbf{E} = -\frac{\partial \mathbf{B}}{\partial t}$（法拉第定律）

### 8.2 流体力学

散度定理描述了流体通过闭合曲面的净流量与内部源汇的关系：

$$\iint_S \mathbf{v} \cdot d\mathbf{S} = \iiint_E \nabla \cdot \mathbf{v} \, dV$$

若 $\nabla \cdot \mathbf{v} = 0$，则流体不可压缩。

### 8.3 热传导

散度定理在热方程的推导中起关键作用，将表面积分转化为体积分。

---

**参考文献**

1. Stewart, J. *Multivariable Calculus*. Cengage Learning, 2015.
2. Marsden, J. E. & Tromba, A. J. *Vector Calculus*. W. H. Freeman, 2011.
3. Spivak, M. *Calculus on Manifolds*. W. A. Benjamin, 1965.
