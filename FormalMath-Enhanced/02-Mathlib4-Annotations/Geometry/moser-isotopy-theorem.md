---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Moser同痕定理 (Moser Isotopy Theorem)
---
# Moser同痕定理 (Moser Isotopy Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Symplectic.Basic
import Mathlib.Geometry.Manifold.Isotopy

namespace MoserIsotopy

variable {M : Type*} [SmoothManifoldWithCorners (𝓡 (2n)) M]

/-- Moser同痕定理：同调辛形式间的同痕 -/
theorem moser_isotopy {ω₀ ω₁ : SymplecticForm M} (hcohom : ∃ α, d α = ω₁ - ω₀)
    (hcompact : IsCompact M) :
    ∃ φ : Isotopy (Diffeomorphism M M) 0 1,
      φ 0 = id ∧ ∀ t, (φ t)* ω₀ = (1-t) • ω₀ + t • ω₁ := by
  -- Moser技巧：构造向量场
  sorry

/-- Darboux定理的Moser证明 -/
theorem darboux_via_moser (ω : SymplecticForm M) (x : M) :
    ∃ (U : OpenNhds x) (φ : U ≃ᵐ OpenBall 0 1), φ* ω = ω_std := by
  -- 应用Moser技巧
  sorry

end MoserIsotopy
```

## 数学背景

Moser同痕定理由德国-美国数学家Jurgen Moser于1965年证明，是辛几何（symplectic geometry）中关于辛形式形变的基本结果。它表明同调的两个辛形式可以通过微分同胚同痕联系起来，揭示了辛结构的"刚性"特征：辛形式不是可以随意变形的几何对象，其同调类在很大程度上决定了辛几何的局部和全局性质。这一定理是证明Darboux定理和理解辛拓扑"柔性"（flexibility）与"刚性"（rigidity）之间微妙平衡的关键工具。

### 辛流形与辛形式

**定义（辛形式）**：设 $M$ 是 $2n$ 维光滑流形。$M$ 上的**辛形式**（symplectic form）是闭的（$d\omega = 0$）、非退化的（non-degenerate）2-形式 $\omega \in \Omega^2(M)$。

**非退化性**：在每点 $p \in M$，映射 $T_p M \to T_p^* M$，$v \mapsto \omega_p(v, \cdot)$ 是线性同构。等价地，$\omega^n = \omega \wedge \cdots \wedge \omega$（$n$ 次）是处处非零的体积形式。

**例子**：在 $\mathbb{R}^{2n}$ 上，标准辛形式为：

$$\omega_{\text{std}} = \sum_{i=1}^{n} dx_i \wedge dy_i = dx_1 \wedge dy_1 + \cdots + dx_n \wedge dy_n$$

用矩阵表示，若将坐标排列为 $(x_1, y_1, \ldots, x_n, y_n)$，则：

$$\omega_{\text{std}}(v, w) = v^T J w, \quad J = \begin{pmatrix} 0 & I_n \\ -I_n & 0 \end{pmatrix}$$

### 辛同胚与同痕

**定义（辛同胚）**：微分同胚 $\phi: M \to M$ 称为**辛同胚**（symplectomorphism），如果 $\phi^* \omega = \omega$（保持辛形式）。

**定义（同痕）**：两个微分同胚 $\phi_0, \phi_1: M \to M$ 之间的**同痕**（isotopy）是光滑映射 $\Phi: M \times [0,1] \to M$，使得对每个 $t \in [0,1]$，$\phi_t = \Phi(\cdot, t)$ 是微分同胚，且 $\phi_0 = \text{id}$，$\phi_1 = \phi$。

## Moser同痕定理的陈述

**定理（Moser同痕定理）**：设 $M$ 是紧光滑流形，$\omega_0$ 和 $\omega_1$ 是 $M$ 上的辛形式。若 $[\omega_0] = [\omega_1] \in H^2_{dR}(M)$（即 $\omega_0$ 和 $\omega_1$ 在de Rham上同调中表示同一个类），则存在微分同胚同痕 $\phi_t: M \to M$（$t \in [0,1]$），使得：

$$\phi_0 = \text{id}, \quad \phi_1^* \omega_0 = \omega_1$$

事实上，可以要求 $\phi_t^* \omega_0 = \omega_t$，其中 $\omega_t = (1-t)\omega_0 + t\omega_1$。

**注**：$\omega_t$ 对小的 $t$ 自动是辛形式（非退化性是开条件），由同调假设 $d(\omega_1 - \omega_0) = 0$ 和 $[\omega_0] = [\omega_1]$，存在1-形式 $\alpha$ 使得 $\omega_1 - \omega_0 = d\alpha$，故 $\omega_t$ 对所有 $t$ 都是闭的。

## 证明：Moser技巧

Moser的证明采用了一个天才的**同伦方法**，现在被称为**Moser技巧**（Moser's trick）。

### 证明

**第一步：构造同伦辛形式**

设 $\omega_t = (1-t)\omega_0 + t\omega_1$，$t \in [0,1]$。由于 $[\omega_0] = [\omega_1]$，有 $d\omega_t = 0$。由于非退化性是开条件且 $M$ 紧，存在 $\epsilon > 0$ 使得 $\omega_t$ 对所有 $t \in [0, \epsilon]$ 是辛形式。实际上，若 $[\omega_0] = [\omega_1]$，则 $\omega_t$ 对所有 $t$ 都是辛形式（这利用了紧性和 $d\alpha = \omega_1 - \omega_0$）。

更准确地说，设 $\omega_1 - \omega_0 = d\alpha$（由de Rham上同调假设）。定义：

$$\omega_t = \omega_0 + t \, d\alpha$$

由于 $\frac{d\omega_t}{dt} = d\alpha$，且对小的 $t$，$\omega_t$ 接近 $\omega_0$ 因而非退化。

**第二步：寻找由向量场生成的同痕**

我们希望找到同痕 $\phi_t$ 使得 $\phi_t^* \omega_t = \omega_0$。对 $t$ 求导（使用Lie导数的Cartan公式）：

$$0 = \frac{d}{dt}(\phi_t^* \omega_t) = \phi_t^*\left(\mathcal{L}_{X_t} \omega_t + \frac{d\omega_t}{dt}\right)$$

其中 $X_t$ 是生成 $\phi_t$ 的向量场（$\frac{d\phi_t}{dt} = X_t \circ \phi_t$）。

利用Cartan公式 $\mathcal{L}_X = d \circ i_X + i_X \circ d$，以及 $d\omega_t = 0$：

$$\mathcal{L}_{X_t} \omega_t = d(i_{X_t} \omega_t)$$

我们需要：

$$d(i_{X_t} \omega_t) + d\alpha = 0$$

即：

$$d(i_{X_t} \omega_t + \alpha) = 0$$

**第三步：求解向量场**

由于 $\omega_t$ 非退化，映射 $X \mapsto i_X \omega_t$ 是从向量场到1-形式的同构。因此，存在唯一的向量场 $X_t$ 使得：

$$i_{X_t} \omega_t = -\alpha$$

（这里我们选择特定的原像；严格来说，需要 $i_{X_t} \omega_t + \alpha$ 是闭的，但由于 $H^1_{dR}(M)$ 可能非零，更精细的论证需要调整。标准处理是选择 $\alpha$ 使得方程可解。）

实际上，标准Moser技巧设 $\omega_t = \omega_0 + t(\omega_1 - \omega_0)$，$\frac{d\omega_t}{dt} = \omega_1 - \omega_0 = d\alpha$。需要 $i_{X_t} \omega_t = -\alpha$，由 $\omega_t$ 的非退化性，$X_t$ 唯一确定。

**第四步：积分向量场**

由于 $M$ 紧，$X_t$ 生成全局流 $\phi_t$。由构造：

$$\frac{d}{dt}(\phi_t^* \omega_t) = 0$$

因此 $\phi_t^* \omega_t = \phi_0^* \omega_0 = \omega_0$。特别地，$\phi_1^* \omega_1 = \omega_0$，即 $\phi_1^* \omega_0 = \omega_1$（调整记号）。 $\square$

## 例子

### 例子1：圆环上的辛形式

考虑 $M = S^1 \times S^1 = T^2$（二维环面）。设 $\theta_1, \theta_2$ 是角坐标。任何辛形式都正比于 $d\theta_1 \wedge d\theta_2$（因为 $\dim H^2_{dR}(T^2) = 1$）。

若 $\omega_0 = c_0 \, d\theta_1 \wedge d\theta_2$，$\omega_1 = c_1 \, d\theta_1 \wedge d\theta_2$，且 $[\omega_0] = [\omega_1]$，则 $c_0 = c_1$，两形式相同，无需变形。

若仅要求同调类相同（在 $T^2$ 上这意味着 $c_0 = c_1$），结论平凡。对更一般的流形，不同代表元可以给出不同的"形状"。

### 例子2：常曲率曲面上的面积元

设 $M$ 是紧定向曲面（2维，从而自动是辛的）。辛形式就是面积形式。若 $\omega_0$ 和 $\omega_1$ 是两个面积形式，$[\omega_0] = [\omega_1] \in H^2_{dR}(M) \cong \mathbb{R}$ 意味着：

$$\int_M \omega_0 = \int_M \omega_1$$

即两个面积形式给出相同的总体积。Moser定理断言：两个具有相同总体积的面积形式通过面积保持微分同胚同痕联系。

### 例子3：Darboux定理的证明

Darboux定理断言：对任意辛流形 $(M, \omega)$ 和点 $x \in M$，存在邻域坐标 $(x_1, y_1, \ldots, x_n, y_n)$ 使得：

$$\omega = \sum_{i=1}^n dx_i \wedge dy_i$$

Moser技巧给出了Darboux定理的一个优美证明：
1. 在 $x$ 附近取任意坐标，将 $\omega$ 与 $\omega_{\text{std}}$ 比较；
2. 利用线性代数（Darboux线性代数）使它们在 $x$ 点相等；
3. 应用Moser技巧的一个局部版本，找到保持 $x$ 不动的微分同胚将 $\omega$ 变为 $\omega_{\text{std}}$。

## 应用

### 1. Darboux定理的证明

如上所述，Moser技巧提供了Darboux定理最简洁的证明之一。Darboux定理表明辛几何没有局部不变量（与Riemann几何形成鲜明对比，后者有曲率等局部不变量），这是辛几何"刚性"与"柔性"并存特征的体现。

### 2. 辛结构的稳定性

Moser定理表明辛结构在同调类内是"稳定"的：小的形变不改变辛结构的等价类。这与Kontsevich的形变量子化、Fukaya范畴等现代辛拓扑工具密切相关。

### 3. 辛拓扑的形变理论

在辛拓扑中，研究辛形式的形变空间是核心问题。Moser定理说明de Rham上同调类是辛形式形变的一个基本不变量。对于非紧流形或带边流形，Moser定理有重要的推广（如相对Moser定理）。

### 4. Hamiltonian力学

在经典力学中，辛形式描述了相空间的结构。Moser定理意味着在适当条件下，两个力学系统的相空间结构可以通过正则变换联系起来，这在可积系统和KAM理论中有应用。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
