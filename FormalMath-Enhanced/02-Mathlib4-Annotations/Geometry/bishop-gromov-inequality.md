---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Bishop-Gromov不等式 (Bishop-Gromov Inequality)
---
# Bishop-Gromov不等式 (Bishop-Gromov Inequality)

## Mathlib4 引用

```lean
import Mathlib.Geometry.RiemannianManifold.BishopGromov
import Mathlib.Geometry.RiemannianManifold.Volume

namespace BishopGromov

variable {M : Type*} [RiemannianMetric M] [CompleteSpace M]
  (hRic : ∀ x : M, RicciCurvature x ≥ (n-1) * k)

/-- Bishop-Gromov体积比较定理 -/
theorem bishop_gromov (x : M) (r R : ℝ) (hr : 0 < r) (hR : r ≤ R) :
    volume (ball x R) / volume (ball x r) ≤ volume (ball_{S_k} R) / volume (ball_{S_k} r) := by
  -- 体积元的Laplace比较
  sorry

/-- 体积增长的有界性 -/
theorem volume_growth_bounded (x : M) :
    Tendsto (fun r => volume (ball x r) / r^n) atTop (𝓝 (0 : ℝ)) := by
  sorry

end BishopGromov
```

## 数学背景

Bishop-Gromov不等式由Richard Bishop和Mikhail Gromov发展，是黎曼几何中关于体积比较的基本结果。它表明Ricci曲率有下界的流形的体积增长不超过常曲率空间形式（space form）的体积增长。这一定理是Gromov紧致性定理、Alexandrov极限空间理论以及许多几何分析结果的基础，在Perelman证明Poincare猜想的Ricci流理论中扮演了重要角色。

### Ricci曲率

**定义（Ricci曲率）**：设 $(M, g)$ 是 $n$ 维Riemann流形，$p \in M$，$v \in T_p M$ 是单位向量。选择 $T_p M$ 的标准正交基 $\{e_1, \ldots, e_n\}$ 使得 $e_1 = v$。则**Ricci曲率**在方向 $v$ 上的值为：

$$\text{Ric}(v, v) = \sum_{i=2}^{n} K(e_1, e_i)$$

其中 $K(e_1, e_i)$ 是由 $e_1$ 和 $e_i$ 张成的二维截面的截面曲率。

Ricci曲率测量了流形在某方向上的"平均"曲率。例如：
- 球面 $S^n$（半径 $R$）：$\text{Ric} = (n-1)/R^2 \cdot g$；
- 欧氏空间 $\mathbb{R}^n$：$\text{Ric} = 0$；
- 双曲空间 $H^n$（曲率 $-1$）：$\text{Ric} = -(n-1)g$。

### 空间形式

**定义（空间形式）**：常曲率 $k$ 的**空间形式**（space form）$S_k^n$ 是完备、单连通的 $n$ 维Riemann流形，截面曲率恒为 $k$。

- $k > 0$：半径 $1/\sqrt{k}$ 的球面 $S^n(1/\sqrt{k})$；
- $k = 0$：欧氏空间 $\mathbb{R}^n$；
- $k < 0$：曲率为 $k$ 的双曲空间 $H^n(k)$。

## Bishop-Gromov不等式的陈述

**定理（Bishop-Gromov体积比较）**：设 $(M, g)$ 是完备的 $n$ 维Riemann流形，且Ricci曲率满足：

$$\text{Ric} \geq (n-1)k \cdot g$$

对某个常数 $k$（即对每点 $x$ 和每个单位向量 $v$，$\text{Ric}_x(v,v) \geq (n-1)k$）。

则对任意 $x \in M$ 和 $0 < r \leq R$：

$$\frac{\text{Vol}(B(x, R))}{\text{Vol}(B(x, r))} \leq \frac{\text{Vol}(B_{S_k}(R))}{\text{Vol}(B_{S_k}(r))}$$

其中 $B(x, R)$ 是 $M$ 中以 $x$ 为中心、半径 $R$ 的测地球，$B_{S_k}(R)$ 是空间形式 $S_k^n$ 中半径 $R$ 的球。

**等价形式**：函数：

$$f(r) = \frac{\text{Vol}(B(x, r))}{\text{Vol}(B_{S_k}(r))}$$

是单调不增的。

### Bishop不等式（体积上界）

取 $r \to 0^+$，由于 $\text{Vol}(B(x, r)) / \text{Vol}(B_{S_k}(r)) \to 1$（小球的体积渐近相同），由单调性：

$$\text{Vol}(B(x, R)) \leq \text{Vol}(B_{S_k}(R))$$

这称为**Bishop不等式**，给出了体积的上界比较。

## 证明概要

Bishop-Gromov不等式的证明依赖于Laplace比较定理和体积元的分析。

### 第一步：指数映射与体积元

在 $x$ 点，指数映射 $\exp_x: T_x M \to M$ 将切空间中的球映为流形中的测地球。在极坐标 $(t, \theta)$ 下（$t > 0$，$\theta \in S^{n-1}$），体积元可写为：

$$d\text{Vol} = J(t, \theta) \, dt \, d\theta$$

其中 $J(t, \theta)$ 是Jacobi行列式。

### 第二步：Laplace比较

**定理（Laplace比较）**：设 $\text{Ric} \geq (n-1)k$，$\rho(y) = d(x, y)$ 是距离函数。则在 $\rho$ 的正则点：

$$\Delta \rho \leq \Delta_{S_k} \rho_k$$

其中 $\rho_k$ 是空间形式 $S_k^n$ 中对应的距离函数。

等价地，Jacobi行列式满足：

$$\frac{J'(t, \theta)}{J(t, \theta)} \leq \frac{J'_k(t)}{J_k(t)}$$

其中 $J_k(t)$ 是空间形式中的径向体积元。

### 第三步：单调性

由微分不等式，$\frac{J(t, \theta)}{J_k(t)}$ 关于 $t$ 单调不增。积分后得到球体积比的单调性：

$$\frac{\text{Vol}(B(x, r))}{\text{Vol}_k(B(r))}$$

单调不增。由此推出Bishop-Gromov不等式。 $\square$

## 例子

### 例子1：欧氏空间

设 $M = \mathbb{R}^n$，$\text{Ric} = 0 = (n-1) \cdot 0$，故 $k = 0$。空间形式是 $\mathbb{R}^n$ 本身。

$$\text{Vol}(B(x, R)) = \omega_n R^n$$

其中 $\omega_n$ 是单位球的体积。Bishop-Gromov不等式变为：

$$\frac{R^n}{r^n} \leq \frac{R^n}{r^n}$$

等号成立。

### 例子2：球面

设 $M = S^n$（单位球面），$\text{Ric} = (n-1)g$，故 $k = 1$。空间形式就是 $S^n$ 本身。

$\text{Vol}(B(x, R)) = \text{Vol}_{S^n}(B(R))$ 对 $R \leq \pi$。不等式取等号。

对 $R > \pi$，球面中的测地球就是整个球面（因为直径为 $\pi$），体积不再增长。

### 例子3：圆柱面

考虑 $M = S^1 \times \mathbb{R}$（无限圆柱）。这是平坦的（乘积度量），$\text{Ric} = 0$，$k = 0$。

大球的体积：$\text{Vol}(B(x, R)) \sim 2\pi \cdot 2R \cdot (2R \text{ 的某个修正})$（基本上是底面圆周长乘以高度）。Bishop-Gromov不等式断言这个体积增长不超过欧氏空间中的 $\omega_2 R^2 = \pi R^2$。

实际上圆柱的体积增长是线性的（对大 $R$），远小于二次增长，不等式成立。

### 例子4：双曲空间

双曲空间 $H^n$（曲率 $-1$）有 $k = -1$，$\text{Ric} = -(n-1)g = (n-1)(-1)g$。

双曲球的体积随半径指数增长：

$$\text{Vol}(B(R)) \sim c_n e^{(n-1)R}$$

Bishop-Gromov不等式给出了体积增长的上界（与 $H^n$ 自身的体积公式比较）。由于 $k < 0$，空间形式 $S_k^n$ 就是 $H^n$，故不等式取等。

## 应用

### 1. Gromov紧致性定理

**定理（Gromov紧致性）**：设 $\{(M_i, g_i)\}$ 是一列 $n$ 维Riemann流形，满足：
- 一致下界：$\text{Ric}_{g_i} \geq (n-1)k$；
- 一致上界：$\text{diam}(M_i) \leq D$；
- 一致下界：$\text{Vol}(M_i) \geq v > 0$。

则存在子列在Gromov-Hausdorff意义下收敛到度量空间 $(X, d)$。

Bishop-Gromov不等式是关键工具：体积比较给出了球的个数的控制，从而保证了序列的"预紧性"。

### 2. 极限空间理论（Alexandrov空间）

在Gromov-Hausdorff极限下，Riemann流形可能"塌缩"到更低维的空间。当Ricci曲率有下界时，极限空间具有许多良好性质（如Hausdorff维数不超过 $n$）。Bishop-Gromov不等式保证了极限测度的存在（归一化体积测度的弱极限）。

### 3. Perelman的Ricci流理论

在Perelman证明Poincare猜想和几何化猜想的工作中，Ricci流：

$$\frac{\partial g}{\partial t} = -2\text{Ric}(g)$$

沿流演化时，Ricci曲率下界可能变化。Perelman引入了Perelman熵和约化体积（reduced volume），其单调性本质上是Bishop-Gromov不等式在Ricci流背景下的推广。约化体积的单调性是非塌缩定理的核心，而非塌缩定理是处理Ricci流奇点的关键。

### 4. 特征值估计

Bishop-Gromov不等式结合Courant极小极大原理，可以给出Laplace算子特征值的下界估计。Cheng的特征值比较定理断言：若 $\text{Ric} \geq (n-1)k$，则Laplace算子的第一非零特征值 $\lambda_1$ 满足：

$$\lambda_1(M) \leq \lambda_1(S_k^n)$$

这推广了Lichnerowicz-Obata定理（$\text{Ric} \geq (n-1)g$ 时 $\lambda_1 \leq n$）。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
