---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: de Rham定理 (de Rham's Theorem)
---
# de Rham定理 (de Rham's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.deRhamCohomology
import Mathlib.AlgebraicTopology.SingularCohomology

namespace DeRhamTheorem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (𝓡 n) M] [SmoothM M]

/-- de Rham定理：de Rham上同调与奇异上同调同构 -/
theorem de_rham_theorem (k : ℕ) :
    H^k_dR M ≅ H^k(X; ℝ) := by
  -- 积分映射给出同构
  sorry

/-- 积分映射的链映射性质 -/
theorem integration_chain_map (ω : Ω^k(M)) (c : C_k(M)) :
    ∫_c dω = ∫_{∂c} ω := by
  -- Stokes定理
  sorry

end DeRhamTheorem
```

## 数学背景

de Rham定理由瑞士数学家Georges de Rham于1931年在他的博士论文中证明，是微分拓扑和代数几何中最深刻、最重要的结果之一。它建立了光滑流形上的微分形式上同调（de Rham上同调）与拓扑上同调（奇异上同调）之间的典范同构，架起了分析学与拓扑学之间的桥梁。这一结果表明：流形的"洞"既可以用微分形式（分析对象）来探测，也可以用单纯形（拓扑对象）来探测，两种方式等价。这一定理是指标理论（Atiyah-Singer指标定理）和Hodge理论的出发点，在现代数学物理中也有广泛应用。

### 微分形式与外微分

**定义（微分形式）**：设 $M$ 是 $n$ 维光滑流形。$M$ 上的**光滑 $k$-形式**（differential $k$-form）是光滑截面 $\omega \in \Gamma(\Lambda^k T^* M)$。在局部坐标 $(x_1, \ldots, x_n)$ 下，$k$-形式可以写成：

$$\omega = \sum_{1 \leq i_1 < \cdots < i_k \leq n} f_{i_1 \cdots i_k}(x) \, dx_{i_1} \wedge \cdots \wedge dx_{i_k}$$

其中 $f_{i_1 \cdots i_k}$ 是光滑函数。

**定义（外微分）**：外微分 $d: \Omega^k(M) \to \Omega^{k+1}(M)$ 由以下性质唯一确定：
1. $d(f) = df$ 对 $0$-形式（函数）成立；
2. $d(\omega \wedge \eta) = d\omega \wedge \eta + (-1)^k \omega \wedge d\eta$（Leibniz法则）；
3. $d^2 = 0$（即 $d(d\omega) = 0$ 对所有 $\omega$）。

局部地，若 $\omega = f_I dx_I$，则 $d\omega = df_I \wedge dx_I = \sum_j \frac{\partial f_I}{\partial x_j} dx_j \wedge dx_I$。

### de Rham上同调

由于 $d^2 = 0$，序列 $(\Omega^*(M), d)$ 构成上链复形（cochain complex）：

$$0 \to \Omega^0(M) \xrightarrow{d} \Omega^1(M) \xrightarrow{d} \Omega^2(M) \xrightarrow{d} \cdots \xrightarrow{d} \Omega^n(M) \to 0$$

**定义（de Rham上同调）**：$M$ 的**$k$维de Rham上同调群**定义为：

$$H^k_{dR}(M) = \frac{\ker(d: \Omega^k(M) \to \Omega^{k+1}(M))}{\text{im}(d: \Omega^{k-1}(M) \to \Omega^k(M))} = \frac{\{\text{闭 } k\text{-形式}\}}{\{\text{恰当 } k\text{-形式}\}}$$

其中闭形式（closed form）满足 $d\omega = 0$，恰当形式（exact form）满足 $\omega = d\eta$ 对某个 $\eta$。

### 奇异上同调

**定义（奇异上同调）**：设 $C_k(M)$ 是 $M$ 上的奇异 $k$-链群，$\partial: C_k(M) \to C_{k-1}(M)$ 是边界算子。定义 $k$ 维奇异上链群 $C^k(M; \mathbb{R}) = \text{Hom}(C_k(M), \mathbb{R})$，上边缘算子 $\delta: C^k(M; \mathbb{R}) \to C^{k+1}(M; \mathbb{R})$ 为 $\delta(\phi) = \phi \circ \partial$。

**$k$维奇异上同调群**为：

$$H^k(M; \mathbb{R}) = \frac{\ker(\delta: C^k(M; \mathbb{R}) \to C^{k+1}(M; \mathbb{R}))}{\text{im}(\delta: C^{k-1}(M; \mathbb{R}) \to C^k(M; \mathbb{R}))}$$

## de Rham定理的陈述

**定理（de Rham）**：设 $M$ 是光滑流形。对每个 $k \geq 0$，存在典范同构：

$$H^k_{dR}(M) \cong H^k(M; \mathbb{R})$$

**同构的构造**：同构由**积分映射**给出。对闭 $k$-形式 $\omega$ 和奇异 $k$-链 $c = \sum_i a_i \sigma_i$（$\sigma_i: \Delta^k \to M$ 是奇异单形），定义：

$$I(\omega)(c) = \int_c \omega = \sum_i a_i \int_{\Delta^k} \sigma_i^* \omega$$

**Stokes定理**保证 $I$ 是链映射：

$$\int_c d\omega = \int_{\partial c} \omega$$

这意味着 $I$ 将闭形式映为上闭链，将恰当形式映为上边缘链，从而在商群上诱导出良定义的映射 $I_*: H^k_{dR}(M) \to H^k(M; \mathbb{R})$。de Rham定理断言 $I_*$ 是同构。

## 证明概要

de Rham定理的证明通常采用层论方法或Mayer-Vietoris归纳法。

### 证明一：Mayer-Vietoris归纳法

**步骤1：Poincaré引理**

对可缩开集 $U \subseteq M$（如开球），Poincaré引理断言：

$$H^k_{dR}(U) = \begin{cases} \mathbb{R} & k = 0 \\ 0 & k > 0 \end{cases}$$

这与可缩空间的奇异上同调一致，验证了de Rham定理在局部成立。

**步骤2：Mayer-Vietoris序列**

对开集 $U, V \subseteq M$，$M = U \cup V$，de Rham上同调和奇异上同调都有Mayer-Vietoris长正合列，且积分映射在这些序列之间诱导交换图。

**步骤3：归纳**

对可以表示为有限个可缩开集的并的流形（如紧流形），通过对覆盖中开集个数归纳，利用五项引理（five lemma）证明积分映射是同构。

**步骤4：一般情形**

对一般流形，利用紧支集上同调和余极限（colimit）论证，将结果从紧子集推广到整个流形。 $\square$

### 证明二：层论方法

**步骤1：de Rham复形作为层的分解**

考虑常数层 $\underline{\mathbb{R}}$（每茎为 $\mathbb{R}$ 的局部常值函数层）。de Rham复形 $(\Omega^*_M, d)$ 是 $\underline{\mathbb{R}}$ 的一个**解析分解**（resolution）：

$$0 \to \underline{\mathbb{R}} \to \Omega^0_M \xrightarrow{d} \Omega^1_M \xrightarrow{d} \cdots$$

Poincaré引理保证这是正合列（在 $\Omega^k_M$ 处正合对 $k > 0$）。

**步骤2：超上同调**

由超上同调理论，常数层的上同调等于其解析分解的全局截面的上同调：

$$H^k(M, \underline{\mathbb{R}}) \cong H^k(\Gamma(M, \Omega^*_M)) = H^k_{dR}(M)$$

**步骤3：层上同调与奇异上同调的等价**

层上同调 $H^k(M, \underline{\mathbb{R}})$ 与奇异上同调 $H^k(M; \mathbb{R})$ 的等价性是代数拓扑的标准结果（可以通过Čech上同调作为中介建立）。 $\square$

## 例子

### 例子1：圆周 $S^1$

$H^1_{dR}(S^1)$：闭1-形式是满足局部 $d\omega = 0$ 的形式，即局部恰当的1-形式。由于 $S^1$ 不是单连通的，存在全局闭但不恰当的1-形式，最著名的是 $d\theta$（角度形式）。

$$\omega = \frac{-y \, dx + x \, dy}{x^2 + y^2}$$

在 $S^1$ 上参数化为 $\omega = d\theta$。积分：

$$\int_{S^1} d\theta = 2\pi \neq 0$$

若 $d\theta = df$，则 $\int_{S^1} df = f(2\pi) - f(0) = 0$，矛盾。因此 $[d\theta]$ 生成 $H^1_{dR}(S^1) \cong \mathbb{R}$，与 $H^1(S^1; \mathbb{R}) \cong \mathbb{R}$ 一致。

### 例子2：球面 $S^n$（$n \geq 2$）

$H^n_{dR}(S^n) \cong \mathbb{R}$，生成元由体积形式给出。在 $S^2$ 上：

$$\omega = \sin\theta \, d\theta \wedge d\phi$$

是标准的面积元，$\int_{S^2} \omega = 4\pi$。这个闭2-形式不是恰当的（否则由Stokes定理其积分为0）。

### 例子3：环面 $T^2 = S^1 \times S^1$

$H^1_{dR}(T^2) \cong \mathbb{R}^2$，由 $d\theta_1$ 和 $d\theta_2$ 生成。$H^2_{dR}(T^2) \cong \mathbb{R}$，由 $d\theta_1 \wedge d\theta_2$ 生成。

这些对应于环面上两个非平凡的一维闭路和二维"面包圈表面"本身。

### 例子4：亏格 $g$ 的曲面

对紧定向曲面 $\Sigma_g$（亏格 $g$，有 $g$ 个"洞"）：

- $H^0_{dR}(\Sigma_g) \cong \mathbb{R}$（连通）
- $H^1_{dR}(\Sigma_g) \cong \mathbb{R}^{2g}$（$g$ 个经圈和 $g$ 个纬圈对应的形式）
- $H^2_{dR}(\Sigma_g) \cong \mathbb{R}$（面积形式）

## 应用

### 1. Hodge理论

在紧定向Riemann流形上，Hodge理论利用de Rham上同调与Laplace算子的核（调和形式）建立同构：

$$H^k_{dR}(M) \cong \{\text{调和 } k\text{-形式}\}$$

这为每个上同调类提供了唯一的"最佳代表"（调和代表），在Kähler几何和代数几何中极为重要。

### 2. 特征类（Chern类、Pontryagin类）

de Rham定理使得可以用微分形式来定义和计算示性类。例如，复向量丛的Chern类可以用曲率形式表示：

$$c(E) = \det\left(I + \frac{i}{2\pi} F\right)$$

其中 $F$ 是联络的曲率形式。de Rham定理保证这些形式类对应于拓扑的示性类。

### 3. 数学物理（规范场论）

在杨-Mills理论中，规范场是主丛上的联络，场强是曲率形式。BFV量子化、反常（anomaly）等概念都依赖于de Rham上同调。拓扑量子场论（TQFT）中的配分函数经常由de Rham上同调类决定。

### 4. 不动点定理与指标定理

Atiyah-Singer指标定理建立了椭圆算子的解析指标与拓扑指标之间的联系。de Rham定理是这一宏大图景的基础特例——它本质上就是de Rham算子 $d + d^*$ 的指标定理。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
