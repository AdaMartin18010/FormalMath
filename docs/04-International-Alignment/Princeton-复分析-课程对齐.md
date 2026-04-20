---
msc_primary: 30-01
msc_secondary:
  - 30B10
  - 30C35
  - 30E20
---

# Princeton 复分析核心内容

Princeton MAT 330（复分析）是国际顶尖的复分析课程，涵盖复可微性、Cauchy 理论、幂级数、留数计算与共形映射等核心主题。本节提供该课程的严格数学内容，包括核心定义、定理证明与典型例子。

## 1. 复可微性与 Cauchy-Riemann 方程

### 1.1 全纯函数

**定义 1.1（全纯函数）**. 设 $\Omega \subseteq \mathbb{C}$ 为开集。$f: \Omega \to \mathbb{C}$ 在 $z_0$ 全纯，若极限
$$f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$
存在。

若 $f$ 在 $\Omega$ 的每点全纯，则称 $f$ 在 $\Omega$ 上全纯。在 $\mathbb{C}$ 上全纯的函数称为整函数。

**定理 1.2（Cauchy-Riemann）**. 设 $f = u + iv$，$u, v$ 为实值函数。$f$ 在 $z_0 = x_0 + iy_0$ 全纯当且仅当 $u, v$ 在 $(x_0, y_0)$ 可微且满足 Cauchy-Riemann 方程：
$$u_x = v_y, \quad u_y = -v_x.$$

*证明*. 沿实轴方向 $h \to 0$：$f'(z_0) = u_x + iv_x$。沿虚轴方向 $h = ik \to 0$：$f'(z_0) = -iu_y + v_y$。比较实部虚部即得 CR 方程。反之，由 $u, v$ 的可微性，记 $u(x+h_1, y+h_2) = u(x,y) + u_x h_1 + u_y h_2 + o(|h|)$，对 $v$ 同理。利用 CR 方程，
$$f(z+h) - f(z) = (u_x + iv_x)(h_1 + ih_2) + o(|h|),$$
故复差商的极限存在且等于 $u_x + iv_x$。$\square$

**推论 1.3**. 全纯函数的实部与虚部是调和函数：$\Delta u = u_{xx} + u_{yy} = 0$。

## 2. Cauchy 积分理论

### 2.1 Cauchy 积分定理

**定理 2.1（Cauchy 积分定理）**. 设 $f$ 在单连通区域 $\Omega$ 上全纯，$\gamma$ 为 $\Omega$ 中的分段光滑闭曲线，则
$$\oint_\gamma f(z)\,dz = 0.$$

*证明*. 将 $f(z)\,dz$ 写为 $(u\,dx - v\,dy) + i(v\,dx + u\,dy)$。由 Green 定理，
$$\oint_\gamma f(z)\,dz = \iint_D \left(-v_x - u_y\right)dx\,dy + i\iint_D \left(u_x - v_y\right)dx\,dy,$$
其中 $D$ 为 $\gamma$ 围成的区域。由 CR 方程，两部分被积函数均为零。$\square$

**定理 2.2（Cauchy 积分公式）**. 设 $f$ 在 $\overline{D}(z_0, R)$ 上全纯，$|z - z_0| < R$：
$$f(z) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = R} \frac{f(\zeta)}{\zeta - z}\, d\zeta.$$

*证明*. 对固定 $z$，在 $\zeta = z$ 处挖去小圆盘，应用 Cauchy 定理于挖去圆盘的环形区域，令小圆半径趋于零即得。$\square$

**推论 2.3（高阶导数公式）**.
$$f^{(n)}(z) = \frac{n!}{2\pi i} \oint \frac{f(\zeta)}{(\zeta - z)^{n+1}}\, d\zeta.$$

特别地，全纯函数无穷可微——这是复分析与实分析的根本差异。

## 3. 幂级数与 Laurent 级数

**定理 3.1（Taylor 展开）**. 全纯函数可局部展开为幂级数：对 $f$ 在 $D(z_0, R)$ 上全纯，
$$f(z) = \sum_{n=0}^\infty a_n (z-z_0)^n, \quad a_n = \frac{f^{(n)}(z_0)}{n!} = \frac{1}{2\pi i} \oint \frac{f(\zeta)}{(\zeta - z_0)^{n+1}}\, d\zeta.$$

**定理 3.2（Laurent 展开）**. 若 $f$ 在圆环 $r < |z - z_0| < R$ 上全纯，则
$$f(z) = \sum_{n=-\infty}^\infty a_n (z-z_0)^n, \quad a_n = \frac{1}{2\pi i} \oint \frac{f(\zeta)}{(\zeta - z_0)^{n+1}}\, d\zeta.$$

Laurent 展开的负幂部分反映函数在孤立奇点处的性态。

## 4. 留数定理与应用

**定义 4.1（留数）**. $f$ 在孤立奇点 $z_0$ 的留数为 Laurent 展开中 $(z-z_0)^{-1}$ 的系数：
$$\operatorname{Res}(f, z_0) = a_{-1} = \frac{1}{2\pi i} \oint_{|z-z_0|=\varepsilon} f(z)\,dz.$$

**定理 4.2（留数定理）**. $f$ 在 $\Omega$ 内除孤立奇点 $z_1, \dots, z_n$ 外全纯，$\gamma$ 为包围这些奇点的正向简单闭曲线：
$$\oint_\gamma f(z)\,dz = 2\pi i \sum_{k=1}^n \operatorname{Res}(f, z_k).$$

*证明*. 在每个 $z_k$ 周围作小圆 $\gamma_k$，由 Cauchy 定理，$\oint_\gamma f = \sum_k \oint_{\gamma_k} f = 2\pi i \sum_k \operatorname{Res}(f, z_k)$。$\square$

**例子 4.3**. 计算 $I = \int_0^\infty \frac{dx}{1+x^2}$。取 $f(z) = \frac{1}{1+z^2}$，在上半平面有单极点 $z = i$，留数
$$\operatorname{Res}(f, i) = \lim_{z \to i} (z-i)f(z) = \frac{1}{2i}.$$
由半圆围道，$\int_{-\infty}^\infty \frac{dx}{1+x^2} = 2\pi i \cdot \frac{1}{2i} = \pi$，故 $I = \frac{\pi}{2}$。

## 5. Riemann 映射定理

**定理 5.1（Riemann 映射）**. 任何真单连通开子集 $U \subsetneq \mathbb{C}$ 都共形等价于单位圆盘 $\mathbb{D}$，即存在全纯双射 $f: U \to \mathbb{D}$。

*证明概要*.

1. 由单连通性，$U$ 可首先共形等价于有界区域；
2. 考虑族 $\mathcal{F} = \{f: U \to \mathbb{D} \text{ 全纯单射}\}$，证明其非空；
3. 利用正规族与 Montel 定理，构造极值函数使某点的导数模极大；
4. 证明该极值函数必为满射：若 $w_0 \notin f(U)$，构造辅助函数使导数更大，矛盾。$\square$

**推论 5.2**. 任意两个真单连通区域（异于 $\mathbb{C}$）均共形等价。

## 6. Picard 定理

**定理 6.1（Picard 小定理）**. 非常值整函数取遍所有复数值，至多遗漏一个。

**定理 6.2（Picard 大定理）**. 若 $f$ 在穿孔邻域 $D'(z_0, r)$ 上全纯且 $z_0$ 为本性奇点，则 $f$ 在该邻域内取每个复数值无穷多次，至多一个例外。

## 7. 交叉引用

- [复分析基础](docs/03-分析学/02-复分析/01-复分析基础.md) — 系统复分析理论
- [Princeton学习诊断](docs/03-分析学/01-实分析/Princeton-复分析-学习诊断手册.md) — 核心定理与深度习题
- [调和分析](docs/03-分析学/07-调和分析/01-调和分析基础.md) — Fourier 分析与全纯函数
- [代数几何](docs/02-代数结构/02-核心理论/代数几何/01-代数几何基础.md) — Riemann 曲面与复结构
- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 复流形

---

**适用**：docs/04-International-Alignment/
