---
title: Poisson方程-边值问题
description: 系统介绍Poisson方程的Dirichlet问题、Neumann问题、Robin问题、Poincaré不等式、Lax-Milgram定理应用，以及弱解的存在性、唯一性与正则性理论。
msc_primary:
  - 35J05
msc_secondary:
  - 35J25
  - 35A01
  - 35D30
processed_at: '2026-04-20'
references:
  textbooks:
    - id: evans_pde
      type: textbook
      title: Partial Differential Equations
      authors:
        - Lawrence C. Evans
      publisher: American Mathematical Society
      year: 2010
      msc: 35-01
    - id: gilbarg_trudinger
      type: textbook
      title: Elliptic Partial Differential Equations of Second Order
      authors:
        - David Gilbarg
        - Neil S. Trudinger
      publisher: Springer
      year: 2001
      msc: 35-02
---

# Poisson方程-边值问题

## 引言

Poisson方程 $-\Delta u = f$ 是椭圆型偏微分方程的典范，其边值问题的适定性理论——存在性、唯一性与正则性——构成了现代PDE理论的基石。从物理上看，Poisson方程描述了静电势、引力势、稳态温度分布等广泛现象；从数学上看，它是Laplace方程在非齐次情形下的自然推广，其边值问题（Dirichlet、Neumann、Robin）分别对应于不同的物理边界约束。Lax-Milgram定理为弱解的存在唯一性提供了优雅的抽象框架，而椭圆正则性理论则保证了弱解在适当条件下自动提升为经典解。

本教程从三类经典边值问题出发，建立变分表述，证明Lax-Milgram定理并应用于Dirichlet问题，分析Neumann问题的相容性条件，最后阐述内部与边界正则性理论。

---

## 1. 边值问题的分类

设 $\Omega \subset \mathbb{R}^n$ 为具有Lipschitz边界的有界区域，考虑Poisson方程
$$-\Delta u = f \quad \text{在 } \Omega \text{ 内}. \tag{P}$$

### 1.1 Dirichlet问题

**定义 1.1（Dirichlet问题）**。求 $u$ 满足
$$\begin{cases} -\Delta u = f & \text{在 } \Omega \text{ 内}, \\ u = g & \text{在 } \partial\Omega \text{ 上}. \end{cases} \tag{D}$$
边界条件 $u|_{\partial\Omega} = g$ 称为 **第一类边界条件**，物理上对应于给定边界上的温度或电势。

### 1.2 Neumann问题

**定义 1.2（Neumann问题）**。求 $u$ 满足
$$\begin{cases} -\Delta u = f & \text{在 } \Omega \text{ 内}, \\ \frac{\partial u}{\partial\nu} = g & \text{在 } \partial\Omega \text{ 上}. \end{cases} \tag{N}$$
其中 $\nu$ 为 $\partial\Omega$ 的单位外法向量。$\partial u/\partial\nu = g$ 为 **第二类边界条件**，物理上对应于给定边界热流或电通量。

### 1.3 Robin问题

**定义 1.3（Robin问题）**。求 $u$ 满足
$$\begin{cases} -\Delta u = f & \text{在 } \Omega \text{ 内}, \\ \frac{\partial u}{\partial\nu} + \alpha u = g & \text{在 } \partial\Omega \text{ 上}, \end{cases} \tag{R}$$
其中 $\alpha > 0$ 为常数。这是 **第三类边界条件**，描述了边界上的对流换热（Newton冷却定律）。

---

## 2. 变分框架与Sobolev空间

### 2.1 Sobolev空间 $H^1(\Omega)$

**定义 2.1**。Sobolev空间 $H^1(\Omega)$ 定义为
$$H^1(\Omega) := \{u \in L^2(\Omega) : \partial_i u \in L^2(\Omega) \, (i=1,\dots,n)\},$$
其中偏导数理解为弱导数。 equipped with内积
$$(u,v)_{H^1} = \int_\Omega (uv + \nabla u \cdot \nabla v) \, dx.$$

子空间 $H_0^1(\Omega)$ 为 $C_c^\infty(\Omega)$ 在 $H^1$ 范数下的闭包，其元素在迹意义下满足 $u|_{\partial\Omega} = 0$。

### 2.2 Poincaré不等式

**定理 2.1（Poincaré不等式）**。设 $\Omega$ 有界。则存在常数 $C_P = C_P(\Omega) > 0$，使得
$$\|u\|_{L^2(\Omega)} \leq C_P \|\nabla u\|_{L^2(\Omega)} \quad \forall u \in H_0^1(\Omega). \tag{Poincaré}$$

**证明**：对 $u \in C_c^\infty(\Omega)$，设 $\Omega \subset \prod_{i=1}^n [a_i, b_i]$。由Newton-Leibniz公式，
$$u(x) = \int_{a_1}^{x_1} \partial_1 u(t, x_2, \dots) \, dt.$$
由Cauchy-Schwarz，
$$u(x)^2 \leq (x_1 - a_1) \int_{a_1}^{b_1} (\partial_1 u)^2 \, dt \leq (b_1-a_1) \int_{a_1}^{b_1} (\partial_1 u)^2 \, dt.$$
对 $x$ 积分，
$$\int_\Omega u^2 \leq (b_1-a_1)^2 \int_\Omega (\partial_1 u)^2 \leq (b_1-a_1)^2 \int_\Omega |\nabla u|^2.$$
取 $C_P = b_1 - a_1$。对一般 $u \in H_0^1$ 由稠密性得到。∎

**推论 2.1**。在 $H_0^1(\Omega)$ 上，$\|u\|_{H^1}$ 与 $\|\nabla u\|_{L^2}$ 等价。即 $a(u,u) = \int_\Omega |\nabla u|^2$ 定义了一个与 $H^1$ 范数等价的范数。

### 2.3 Poincaré-Wirtinger不等式

对Neumann问题，需在商空间上建立强制性。

**定理 2.2（Poincaré-Wirtinger）**。设 $\Omega$ 连通且有界。则存在 $C_{PW} > 0$ 使
$$\|u - \bar{u}\|_{L^2} \leq C_{PW} \|\nabla u\|_{L^2} \quad \forall u \in H^1(\Omega),$$
其中 $\bar{u} = \frac{1}{|\Omega|}\int_\Omega u$ 为平均值。

---

## 3. Lax-Milgram定理与Dirichlet问题

### 3.1 Lax-Milgram定理

**定理 3.1（Lax-Milgram）**。设 $H$ 为实Hilbert空间，$a: H \times H \to \mathbb{R}$ 为双线性型，满足：
1. **有界性**（连续性）：$|a(u,v)| \leq C\|u\|\|v\|$ 对所有 $u,v \in H$；
2. **强制性**（$V$-椭圆性）：$a(u,u) \geq \alpha\|u\|^2$ 对所有 $u \in H$，其中 $\alpha > 0$。

则对任意有界线性泛函 $L \in H^*$，存在唯一的 $u \in H$ 使得
$$a(u,v) = L(v) \quad \forall v \in H,$$
且 $\|u\| \leq \frac{1}{\alpha}\|L\|_{H^*}$。

**证明**：由Riesz表示定理，对每个 $u \in H$，映射 $v \mapsto a(u,v)$ 是有界线性泛函，故存在唯一的 $Au \in H$ 使 $a(u,v) = (Au, v)$。映射 $A: H \to H$ 线性且有界（$\|Au\| \leq C\|u\|$）。

强制性给出 $(Au, u) \geq \alpha\|u\|^2$，故 $A$ 是单射且有闭值域。若 $w \perp \operatorname{im}A$，则 $0 = (Au, w) = a(u,w)$ 对所有 $u$。取 $u=w$，$\alpha\|w\|^2 \leq a(w,w) = 0$，故 $w=0$。因此 $\operatorname{im}A = H$，$A$ 为双射。令 $u = A^{-1}w_L$（$w_L$ 为 $L$ 的Riesz代表），即得解。唯一性由强制性：若 $a(u_1,v)=a(u_2,v)$ 对所有 $v$，则 $a(u_1-u_2, u_1-u_2)=0$，故 $u_1=u_2$。∎

### 3.2 Dirichlet问题的弱解

**定义 3.1（弱解）**。$u \in H_0^1(\Omega)$ 称为Dirichlet问题 (D)（$g=0$）的 **弱解**，若
$$\int_\Omega \nabla u \cdot \nabla v \, dx = \int_\Omega f v \, dx \quad \forall v \in H_0^1(\Omega). \tag{WD}$$

**定理 3.2**。设 $f \in H^{-1}(\Omega)$（$H_0^1$ 的对偶）。则齐次Dirichlet问题存在唯一弱解 $u \in H_0^1(\Omega)$，且 $\|u\|_{H^1} \leq C\|f\|_{H^{-1}}$。

**证明**：取 $H = H_0^1(\Omega)$，$a(u,v) = \int_\Omega \nabla u \cdot \nabla v$，$L(v) = \langle f, v \rangle$。由Poincaré不等式，$a(u,u) = \|\nabla u\|_{L^2}^2 \geq \alpha\|u\|_{H^1}^2$，满足强制性。应用Lax-Milgram即得。∎

### 3.3 非齐次Dirichlet问题

对 $u|_{\partial\Omega} = g$，设 $g$ 可延拓为 $\tilde{g} \in H^1(\Omega)$（例如 $g \in H^{1/2}(\partial\Omega)$）。令 $w = u - \tilde{g} \in H_0^1(\Omega)$，则 $w$ 满足
$$\int_\Omega \nabla w \cdot \nabla v = \int_\Omega fv - \int_\Omega \nabla\tilde{g} \cdot \nabla v \quad \forall v \in H_0^1.$$
右端为 $H_0^1$ 上的有界线性泛函，由定理3.2存在唯一解 $w$，从而 $u = w + \tilde{g}$。

---

## 4. Neumann问题

### 4.1 相容性条件

**定理 4.1**。Neumann问题 (N) 有解的必要条件是
$$\int_\Omega f \, dx + \int_{\partial\Omega} g \, dS = 0. \tag{Compat}$$

**证明**：由Green第一恒等式，对解 $u$：
$$\int_\Omega f = -\int_\Omega \Delta u = -\int_{\partial\Omega} \frac{\partial u}{\partial\nu} = -\int_{\partial\Omega} g.$$
∎

### 4.2 解的唯一性

若 $u$ 为解，则对任意常数 $C$，$u + C$ 也是解。故解在相差常数意义下唯一。

**定理 4.2**。在相容性条件 (Compat) 下，Neumann问题在商空间 $H^1(\Omega)/\mathbb{R}$ 中存在唯一弱解。

**证明**：在 $V = H^1(\Omega)/\mathbb{R}$ 上，由Poincaré-Wirtinger不等式，$\|\nabla u\|_{L^2}$ 为等价范数。双线性型 $a(u,v) = \int_\Omega \nabla u \cdot \nabla v$ 在 $V$ 上强制。泛函 $L(v) = \int_\Omega fv + \int_{\partial\Omega} gv$ 在 $V$ 上良定（因常数的贡献由相容性条件抵消）。Lax-Milgram给出唯一解。∎

---

## 5. Robin问题

**定理 5.1**。Robin问题 (R) 对任意 $f \in L^2(\Omega)$，$g \in L^2(\partial\Omega)$ 存在唯一弱解 $u \in H^1(\Omega)$。

**证明**：双线性型
$$a(u,v) = \int_\Omega \nabla u \cdot \nabla v + \alpha \int_{\partial\Omega} u v \, dS$$
在 $H^1(\Omega)$ 上连续。强制性：由迹定理和Poincaré不等式的变形，
$$a(u,u) = \|\nabla u\|_{L^2}^2 + \alpha\|u\|_{L^2(\partial\Omega)}^2 \geq \beta\|u\|_{H^1}^2$$
对某 $\beta > 0$。Lax-Milgram直接适用。∎

---

## 6. 正则性理论

### 6.1 Weyl引理（内部正则性）

**定理 6.1（Weyl引理）**。设 $u$ 为 $-\Delta u = f$ 的弱解。若 $f \in H^k(\Omega)$，则 $u \in H^{k+2}_{\mathrm{loc}}(\Omega)$。特别地，若 $f \in C^\infty(\Omega)$，则 $u \in C^\infty(\Omega)$。

**证明概要**：利用差商技术和Fourier分析。对内部球 $B \subset\subset \Omega$，取截断函数 $\eta \in C_c^\infty(B')$（$B \subset\subset B' \subset\subset \Omega$）。对弱解方程取差商 $D_i^h(\eta^2 D_i^{-h}u)$ 作为检验函数，建立一致估计
$$\|D_i^h(\eta u)\|_{H^1} \leq C(\|f\|_{L^2} + \|u\|_{H^1}),$$
令 $h \to 0$ 得 $\eta u \in H^2$，即 $u \in H^2(B)$。对更高阶正则性迭代。∎

### 6.2 边界正则性

**定理 6.2（全局椭圆正则性）**。设 $\Omega$ 为 $C^{k+2}$ 区域。若 $f \in H^k(\Omega)$，$g \in H^{k+3/2}(\partial\Omega)$，则Dirichlet问题的解 $u \in H^{k+2}(\Omega)$。

**推论 6.1**。若 $\partial\Omega \in C^\infty$，$f \in C^\infty(\overline{\Omega})$，$g \in C^\infty(\partial\Omega)$，则 $u \in C^\infty(\overline{\Omega})$。

### 6.3 Schauder估计

对Hölder空间数据，有经典估计：
$$\|u\|_{C^{2,\alpha}(\overline{\Omega})} \leq C\left(\|f\|_{C^\alpha(\overline{\Omega})} + \|g\|_{C^{2,\alpha}(\partial\Omega)}\right).$$

---

## 7. 特征值问题

### 7.1 Laplace算子的谱

**定理 7.1**。$-\Delta$ 在 $H_0^1(\Omega)$ 上具有离散谱：存在标准正交基 $\{\phi_k\}_{k=1}^\infty \subset L^2(\Omega)$ 和
$$0 < \lambda_1 \leq \lambda_2 \leq \cdots \to \infty$$
使 $-\Delta\phi_k = \lambda_k\phi_k$。

**变分刻画（Rayleigh商）**：
$$\lambda_1 = \inf_{u \in H_0^1, u \neq 0} \frac{\int_\Omega |\nabla u|^2}{\int_\Omega u^2}.$$

**例 7.1**：$\Omega = (0,\pi)$，$\lambda_k = k^2$，$\phi_k(x) = \sin(kx)$。

**例 7.2**：$\Omega = B(0,R) \subset \mathbb{R}^2$，$\lambda$ 由Bessel函数 $J_n(\sqrt{\lambda}R) = 0$ 的根给出。

---

## 8. 与已有文档的关联

- [07-Laplace方程-调和函数](07-Laplace方程-调和函数.md)：调和函数的平均值性质与最大值原理。
- [08-Laplace方程-Green函数](08-Laplace方程-Green函数.md)：Green函数表示公式与Poisson核。
- [10-Sobolev空间-弱导数](10-Sobolev空间-弱导数.md)：Sobolev空间的系统理论。
- [12-变分法与弱解](12-变分法与弱解.md)：变分方法在椭圆PDE中的一般框架。
- [13-椭圆方程正则性](13-椭圆方程正则性.md)：更一般的椭圆方程正则性理论。

---

## 参考文献

1. L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010. (Ch. 5, 6)
2. D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer, 2001. (Ch. 8)
3. H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer, 2011. (Ch. 8, 9)
4. G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton Univ. Press, 1995. (Ch. 6, 7)

---

**适用**：docs/16-偏微分方程/
