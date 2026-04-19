---
msc_primary: 97A99
msc_secondary:
  - 00A99
---

# Princeton 复分析核心内容

Princeton MAT 330（复分析）是国际顶尖的复分析课程，涵盖复可微性、Cauchy 理论、幂级数、留数计算与共形映射等核心主题。本节提供该课程的严格数学内容，包括核心定义、定理证明与典型例子。

## 1. 复可微性与 Cauchy-Riemann 方程

**定义 1.1（全纯函数）**. 设 $\Omega \subseteq \mathbb{C}$ 为开集。$f: \Omega \to \mathbb{C}$ 在 $z_0$ 全纯，若极限

$$f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$

存在。

**定理 1.2（Cauchy-Riemann）**. $f = u + iv$ 全纯当且仅当 $u, v$ 可微且 $u_x = v_y$，$u_y = -v_x$。

*证明*. 沿实轴和虚轴求极限，比较即得 CR 方程；反之，由可微性和 CR 方程验证复差商的极限存在。$\square$

## 2. Cauchy 积分理论

**定理 2.1（Cauchy 积分定理）**. $f$ 在单连通区域 $\Omega$ 上全纯，$\gamma$ 为闭曲线，则 $\oint_\gamma f(z)dz = 0$。

*证明*. $f(z)dz = (u dx - v dy) + i(v dx + u dy)$。由 Green 定理和 CR 方程，两部分均为零。$\square$

**定理 2.2（Cauchy 积分公式）**. $f$ 在 $\overline{D}(z_0, R)$ 上全纯，$|z - z_0| < R$：

$$f(z) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = R} \frac{f(\zeta)}{\zeta - z} d\zeta.$$

## 3. 幂级数与 Laurent 级数

**定理 3.1**. 全纯函数可局部展开为幂级数：

$$f(z) = \sum_{n=0}^\infty a_n (z-z_0)^n, \quad a_n = \frac{f^{(n)}(z_0)}{n!}.$$

**定理 3.2（Laurent 展开）**. 若 $f$ 在圆环 $r < |z - z_0| < R$ 上全纯，则

$$f(z) = \sum_{n=-\infty}^\infty a_n (z-z_0)^n, \quad a_n = \frac{1}{2\pi i} \oint \frac{f(\zeta)}{(\zeta - z_0)^{n+1}} d\zeta.$$

## 4. 留数定理与应用

**定理 4.1（留数定理）**. $f$ 在 $\Omega$ 内除孤立奇点 $z_1, \dots, z_n$ 外全纯，$\gamma$ 包围这些奇点：

$$\oint_\gamma f(z)dz = 2\pi i \sum_{k=1}^n \operatorname{Res}(f, z_k).$$

## 5. Riemann 映射定理

**定理 5.1（Riemann 映射）**. 任何真单连通开子集 $U \subsetneq \mathbb{C}$ 都共形等价于单位圆盘 $\mathbb{D}$。

*证明概要*. 利用正规族和 Montel 定理，构造极值函数（使某点的导数极大），证明其为满射。$\square$

## 6. 例子

### 6.1 例子：实积分计算

$I = \int_0^\infty \frac{dx}{1+x^2} = \frac{\pi}{2}$（用半圆围道，$f(z) = 1/(1+z^2)$ 在上半平面有单极点 $z = i$，留数 $= 1/(2i)$）。

### 6.2 例子：整函数分类

**定理 6.1（Picard 小定理）**. 非常值整函数取遍所有复数值，至多遗漏一个。

## 7. 交叉引用

- [复分析基础](docs/03-分析学/02-复分析/01-复分析基础.md) — 系统复分析理论
- [Princeton学习诊断](docs/03-分析学/01-实分析/Princeton-复分析-学习诊断手册.md) — 核心定理与深度习题
- [调和分析](docs/03-分析学/07-调和分析/01-调和分析基础.md) — Fourier 分析与全纯函数
- [代数几何](docs/02-代数结构/02-核心理论/代数几何/01-代数几何基础.md) — Riemann 曲面与复结构

---

**适用**：docs/04-International-Alignment/
