---
msc_primary: 46E35
msc_secondary:
  - 35Jxx
  - 46Fxx
processed_at: '2026-04-20'
title: Sobolev空间
---

# Sobolev空间

## 1. 引言

Sobolev空间是以苏联数学家Sergei Sobolev命名的一类函数空间，其元素是 $L^p$ 函数且其分布意义下的导数（直至某阶）也属于 $L^p$。这类空间在现代偏微分方程理论中占据了核心地位：椭圆型方程的弱解自然存在于Sobolev空间中；变分法的直接法需要在适当的Sobolev空间中寻求能量泛函的极小元；Sobolev嵌入定理建立了不同函数空间之间的包含关系，为解的正则性研究提供了关键工具。本文系统阐述Sobolev空间的定义、基本性质、嵌入定理和迹定理。

## 2. $W^{k,p}$ 空间的定义

### 2.1 整数阶Sobolev空间

设 $\Omega \subseteq \mathbb{R}^n$ 为开集，$k \in \mathbb{N}_0 = \{0, 1, 2, \ldots\}$，$1 \leq p \leq \infty$。

**定义 2.1**。
$$W^{k,p}(\Omega) = \{ u \in L^p(\Omega) : \partial^\alpha u \in L^p(\Omega), \, \forall |\alpha| \leq k \},$$
其中 $\partial^\alpha u$ 为分布意义下的弱导数。装备范数
$$\|u\|_{W^{k,p}(\Omega)} = \begin{cases} \left( \sum_{|\alpha| \leq k} \|\partial^\alpha u\|_{L^p(\Omega)}^p \right)^{1/p}, & 1 \leq p < \infty, \\ \max_{|\alpha| \leq k} \|\partial^\alpha u\|_{L^\infty(\Omega)}, & p = \infty. \end{cases}$$

**定理 2.2**。$(W^{k,p}(\Omega), \|\cdot\|_{W^{k,p}})$ 是Banach空间。

*证明*。设 $(u_m)$ 为 $W^{k,p}$ 中的Cauchy列。则对每个 $|\alpha| \leq k$，$(\partial^\alpha u_m)$ 为 $L^p$ 中的Cauchy列。由 $L^p$ 完备性，$\partial^\alpha u_m \to u^{(\alpha)}$ 于 $L^p$。特别地，$u_m \to u^{(0)} =: u$。需验证 $\partial^\alpha u = u^{(\alpha)}$。对任意 $\varphi \in \mathcal{D}(\Omega)$，
$$\int_\Omega u_m \partial^\alpha \varphi = (-1)^{|\alpha|} \int_\Omega \partial^\alpha u_m \varphi.$$
令 $m \to \infty$，左边 $\to \int_\Omega u \partial^\alpha \varphi$，右边 $\to (-1)^{|\alpha|} \int_\Omega u^{(\alpha)} \varphi$。故 $u^{(\alpha)} = \partial^\alpha u$。$\square$

### 2.2 $W_0^{k,p}$ 空间

**定义 2.3**。$W_0^{k,p}(\Omega)$ 定义为 $C_c^\infty(\Omega)$ 在 $W^{k,p}(\Omega)$ 中的闭包。其元可理解为"在边界上取零值"的Sobolev函数（对 $k = 1$）。

**命题 2.4**。若 $\Omega$ 有界且 $1 \leq p < \infty$，则 $W_0^{1,p}(\Omega) \neq W^{1,p}(\Omega)$。常数函数属于 $W^{1,p}$ 但不属于 $W_0^{1,p}$（当 $\Omega$ 连通时）。

## 3. $H^s$ 空间与Fourier刻画

### 3.1 实指数Sobolev空间

**定义 3.1**。对 $s \in \mathbb{R}$，定义
$$H^s(\mathbb{R}^n) = \{ u \in \mathcal{S}'(\mathbb{R}^n) : (1 + |\xi|^2)^{s/2} \hat{u}(\xi) \in L^2(\mathbb{R}^n) \},$$
装备内积
$$\langle u, v \rangle_{H^s} = \int_{\mathbb{R}^n} (1 + |\xi|^2)^s \hat{u}(\xi) \overline{\hat{v}(\xi)} \, d\xi.$$

**定理 3.2**。当 $s = k \in \mathbb{N}$，$H^k(\mathbb{R}^n) = W^{k,2}(\mathbb{R}^n)$，且范数等价。

*证明*。由Plancherel定理，$\|\partial^\alpha u\|_{L^2} = \|(2\pi i \xi)^\alpha \hat{u}\|_{L^2}$。显然 $|\xi^\alpha|^2 \leq (1 + |\xi|^2)^k$，且由多项式展开，$(1 + |\xi|^2)^k \leq C \sum_{|\alpha| \leq k} |\xi^\alpha|^2$。$\square$

### 3.2 Sobolev嵌入

**定理 3.3**（Sobolev嵌入定理）。设 $\Omega \subseteq \mathbb{R}^n$ 有界光滑，$k > l$，$1 \leq p, q < \infty$。

1. 若 $k - \frac{n}{p} \geq l - \frac{n}{q}$，则 $W^{k,p}(\Omega) \hookrightarrow W^{l,q}(\Omega)$（连续嵌入）。
2. 若 $k - \frac{n}{p} > l$，则 $W^{k,p}(\Omega) \hookrightarrow C^{l,\alpha}(\overline{\Omega})$，其中 $\alpha = k - l - \frac{n}{p}$（当非整数时）或任意 $\alpha < 1$（当整数时）。

*注记*。临界情形 $k - n/p = l$ 时，$W^{k,p} \hookrightarrow W^{l,q}$ 对所有 $q < \infty$ 成立，但一般不入 $L^\infty$（除非 $kp > n$）。

**例 3.4**。在 $\mathbb{R}^3$ 中，$H^2 = W^{2,2} \hookrightarrow C^{0,1/2}$（因 $2 - 3/2 = 1/2 > 0$）。$H^1 = W^{1,2}$ 不入 $L^\infty$（因 $1 - 3/2 < 0$），但入 $L^6$（因 $1 - 3/2 = 0 - 3/6$）。

## 4. 紧嵌入定理

**定理 4.1**（Rellich-Kondrachov）。设 $\Omega \subseteq \mathbb{R}^n$ 有界光滑，$k > l$，$1 \leq p, q < \infty$。若 $k - \frac{n}{p} > l - \frac{n}{q}$，则嵌入 $W^{k,p}(\Omega) \hookrightarrow W^{l,q}(\Omega)$ 是**紧的**（将有界集映为相对紧集）。

*证明概要*。由Sobolev嵌入，$W^{k,p} \hookrightarrow W^{l,q}$ 连续。紧性证明利用Arzelà-Ascoli定理或光滑逼近：对 $W^{k,p}$ 中有界集，其 $W^{l,q}$ 像可用 $C^m$ 函数逼近，而 $C^m(\overline{\Omega})$ 到 $W^{l,q}$ 的嵌入在 $m > l$ 时为紧。$\square$

**推论 4.2**。对有界光滑 $\Omega$，$H^1(\Omega) \hookrightarrow L^2(\Omega)$ 紧。这是椭圆方程特征值问题离散性的关键。

## 5. 迹定理

### 5.1 迹算子

对连续函数，边界值 $u|_{\partial\Omega}$ 自然定义。但对一般 $W^{1,p}$ 函数（仅在几乎处处有定义），需要特殊的"迹"理论。

**定理 5.1**（迹定理）。设 $\Omega \subseteq \mathbb{R}^n$ 为有界光滑区域，$1 \leq p < \infty$。存在有界线性算子（**迹算子**）
$$\gamma: W^{1,p}(\Omega) \to L^p(\partial\Omega)$$
使得对 $u \in C^\infty(\overline{\Omega})$，$\gamma(u) = u|_{\partial\Omega}$。且
$$\ker \gamma = W_0^{1,p}(\Omega).$$

*证明概要*。对上半空间 $\mathbb{R}^n_+ = \{x_n > 0\}$，定义
$$\gamma(u)(x') = u(x', 0) = -\int_0^\infty \partial_n u(x', t) \, dt$$
（对光滑 $u$）。由Hölder不等式，$\|\gamma(u)\|_{L^p(\mathbb{R}^{n-1})} \leq C \|\partial_n u\|_{L^p(\mathbb{R}^n_+)}^{1/p'} \|u\|_{L^p}^{1/p}$，经精细估计得 $\|\gamma(u)\|_{L^p} \leq C \|u\|_{W^{1,p}}$。再通过单位分解延拓到一般区域。$\square$

### 5.2 迹空间的刻画

**定理 5.2**。$\gamma: W^{1,p}(\Omega) \to W^{1 - 1/p, p}(\partial\Omega)$ 是满射。即边界值不能任意取，而必须属于分数阶Sobolev空间 $W^{1 - 1/p, p}(\partial\Omega)$。

**例 5.3**。对 $p = 2$，$H^1(\Omega)$ 在边界上的迹空间为 $H^{1/2}(\partial\Omega)$。

## 6. Poincaré不等式

**定理 6.1**（Poincaré不等式）。设 $\Omega$ 有界（至少在一个方向上有界），$1 \leq p < \infty$。则存在 $C = C(\Omega, p)$ 使
$$\|u\|_{L^p(\Omega)} \leq C \|\nabla u\|_{L^p(\Omega)}, \quad \forall u \in W_0^{1,p}(\Omega).$$

*证明*。设 $\Omega \subseteq \{0 < x_1 < d\}$。对 $u \in C_c^\infty(\Omega)$，
$$u(x) = \int_0^{x_1} \partial_1 u(t, x_2, \ldots) \, dt.$$
由Hölder，$|u(x)|^p \leq x_1^{p-1} \int_0^d |\partial_1 u|^p dt$，积分得 $\|u\|_p^p \leq \frac{d^p}{p} \|\partial_1 u\|_p^p$。$\square$

**推论 6.2**。在 $W_0^{1,p}(\Omega)$ 上，$\|\nabla u\|_{L^p}$ 等价于完整 $W^{1,p}$ 范数。

## 7. 与项目其他部分的关联

Sobolev空间是偏微分方程弱解理论的自然框架。椭圆方程 $Lu = f$ 的弱解 $u \in H_0^1$ 的存在性由Lax-Milgram定理保证，正则性则由Sobolev嵌入迭代提升。紧嵌入定理（Rellich-Kondrachov）是紧算子理论（见[05-紧算子](05-紧算子.md)）在函数空间中的重要实例——它保证了Laplace算子等逆算子的紧性，从而特征值离散。迹定理为边值问题的提法提供了严格的数学基础。分布论（见[09-分布论入门](09-分布论入门.md)）是Sobolev空间的理论基石，弱导数的概念完全依赖于分布框架。

## 8. 参考文献

1. S.L. Sobolev, *Some Applications of Functional Analysis in Mathematical Physics*, AMS, 1991.
2. R.A. Adams & J.J.F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003.
3. H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, Springer, 2011.
4. L.C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010.
5. 王术，《Sobolev空间与偏微分方程引论》，科学出版社，2009。
