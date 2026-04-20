---
msc_primary: 00A99
习题编号: TOP-111
学科: 拓扑
知识点: 拓扑-Ricci流
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
---

# Ricci 流

## 题目

**(a)** 证明 Ricci 流的短时间存在性。

**(b)** 讨论 Hamilton 的3维球定理。

**(c)** 概述 Perelman 对 Poincaré 猜想的证明。

## 解答

### (a) Ricci 流的短时间存在性

**定义**：在 $n$ 维流形 $M$ 上，Ricci 流是度量 $g(t)$ 满足以下偏微分方程的演化：
$$\frac{\partial g_{ij}}{\partial t} = -2R_{ij}$$
其中 $R_{ij}$ 是 Ricci 张量。等价地，$\frac{\partial g}{\partial t} = -2\text{Ric}(g)$。

**Hamilton 存在性定理（1982）**：对任意光滑闭流形 $(M, g_0)$，存在 $T > 0$ 和唯一的 Ricci 流 $g(t) \in C^\infty(M \times [0, T))$，$g(0) = g_0$。

**证明的关键问题与解决**：

Ricci 流在坐标下展开为：
$$\frac{\partial g_{ij}}{\partial t} = g^{kl}\partial_k\partial_l g_{ij} + \text{低阶项}$$

但其主象征（principal symbol）并非椭圆：由微分同胚不变性，方程在切方向退化。具体计算主象征：
$$\sigma(D)(\xi)(h)_{ij} = |\xi|^2 h_{ij} + \xi_i\xi_j \text{tr}(h) - \xi_i\xi^k h_{jk} - \xi_j\xi^k h_{ik}$$

这对应于在 $Diff(M)$ 轨道方向的退化。

**DeTurck 技巧（1983）**：引入向量场 $V^k = g^{ij}(\Gamma^k_{ij} - \tilde{\Gamma}^k_{ij})$，其中 $\tilde{\Gamma}$ 是某个固定背景度量 $\tilde{g}$ 的 Christoffel 符号。定义 **DeTurck-Ricci 流**：
$$\frac{\partial g_{ij}}{\partial t} = -2R_{ij} + \nabla_i V_j + \nabla_j V_i$$

**定理**：DeTurck-Ricci 流是严格抛物型方程。

*证明*：在 DeTurck 流中，主象征变为：
$$\tilde{\sigma}(D)(\xi)(h)_{ij} = |\xi|^2 h_{ij}$$
这是完全椭圆（totally elliptic）的。由标准抛物型 PDE 理论（如 Hamilton 的 Nash-Moser 隐函数定理或更现代的解析半群理论），对光滑初值存在唯一的短时间光滑解。

**从 DeTurck 流回到 Ricci 流**：设 $g(t)$ 是 DeTurck-Ricci 流的解。构造一族微分同胚 $\varphi_t$ 满足：
$$\frac{\partial \varphi_t}{\partial t} = -V \circ \varphi_t, \quad \varphi_0 = \text{id}$$

则 $\bar{g}(t) = \varphi_t^* g(t)$ 满足标准 Ricci 流方程。这是因为 Lie 导数 $L_V g = \nabla_i V_j + \nabla_j V_i$ 恰好抵消了 DeTurck 修正项。

### (b) Hamilton 的 3 维球定理

**定理（Hamilton, 1982）**：设 $(M^3, g_0)$ 是闭 3 维流形，若 $g_0$ 的 Ricci 曲率正定（$\text{Ric} > 0$），则 Ricci 流 $g(t)$ 对所有 $t > 0$ 存在，并在适当规范化后收敛到常正截面曲率度量。特别地，$M \cong S^3 / \Gamma$ 其中 $\Gamma$ 是有限自由作用子群。

**证明的主要步骤**：

**步骤 1：曲率保持正性**。设 $Rm$ 是 Riemann 曲率张量。Hamilton 证明若 $g_0$ 有正 Ricci 曲率，则 $g(t)$ 保持正 Ricci 曲率。这由张量的极值原理（maximum principle）保证：Ricci 曲率满足的反应-扩散方程使其正性集保持。

**步骤 2：曲率 pinching**。定义尺度归一化 Ricci 流：
$$\frac{\partial g}{\partial t} = -2\text{Ric} + \frac{2}{3}\bar{R}g$$
其中 $\bar{R} = \int R \, d\mu / \int d\mu$ 是平均标量曲率。Hamilton 证明量：
$$|Rm|^2 - \frac{1}{3}R^2 = |Rm - \frac{R}{6}g \odot g|^2$$
按指数衰减，即曲率趋向于常曲率。

**步骤 3：收敛性**。由 Cheeger-Gromov 紧性定理和曲率的一致有界性，存在子列收敛到 Einstein 度量。在 3 维，Einstein 意味着常截面曲率。

### (c) Perelman 对 Poincaré 猜想的证明概述

Perelman（2002-2003）通过引入新工具，将 Ricci 流发展为证明几何化猜想（从而推出 Poincaré 猜想）的完整方法。

**核心创新**：

**1. $\mathcal{F}$-泛函与熵**
$$\mathcal{F}(g, f) = \int_M (R + |\nabla f|^2) e^{-f} d\mu$$
Perelman 证明 Ricci 流是 $\mathcal{F}$ 的梯度流。固定体积约束 $\int e^{-f} d\mu = 1$，定义：
$$\lambda(g) = \inf_f \mathcal{F}(g, f)$$
$\lambda(g)$ 在 Ricci 流下单调递增。

**2. $\mathcal{W}$-泛函（缩放的熵）**
$$\mathcal{W}(g, f, \tau) = \int_M [\tau(R + |\nabla f|^2) + f - n](4\pi\tau)^{-n/2} e^{-f} d\mu$$
定义 $\mu(g, \tau) = \inf_f \mathcal{W}(g, f, \tau)$。关键定理：$\mu$ 在 Ricci 流下单调。

**3. 约化体积（reduced volume）**
对反向 Ricci 流，Perelman 定义 $\ar{V}(\tau)$，证明其单调不减且上有界。若 $\lim_{\tau \to 0} \bar{V}(\tau) = (4\pi)^{n/2}$ 达到最大值，则流形是欧氏空间。

**4. $\kappa$-非塌缩（non-collapsing）**
**定理**：若 $g(t)$ 是 3 维 Ricci 流，$|Rm| \leq r^{-2}$ 在 $B(x, r)$ 上，则 $\text{Vol}(B(x, r)) \geq \kappa r^n$，其中 $\kappa$ 依赖于初值。

这排除了"雪茄"奇点（cigar soliton）作为有限时间奇点的模型。

**5. 手术 Ricci 流**
当曲率在某点爆破时，识别 neck-like 区域（接近 $S^2 \times \mathbb{R}$ 的度量），进行拓扑手术：切除 $S^2 \times I$ 并粘合 3-球。Perelman 证明手术可以进行有限次（在有限时间区间内），并保持几何化结构。

**推论（Poincaré 猜想）**：设 $M$ 是单连通闭 3 维流形。从任意度量出发，手术 Ricci 流最终消没（在有限时间内体积趋于零），这意味着 $M$ 微分同胚于 $S^3$。

**参考文献**：
- R. Hamilton, "Three-manifolds with positive Ricci curvature", *J. Diff. Geom.* 1982
- D. DeTurck, "Deforming metrics in the direction of their Ricci tensors", *J. Diff. Geom.* 1983
- G. Perelman, "The entropy formula for the Ricci flow and its geometric applications", 2002
- G. Perelman, "Ricci flow with surgery on three-manifolds", 2003
- B. Kleiner, J. Lott, "Notes on Perelman's papers", *Geom. Topol.* 2008
