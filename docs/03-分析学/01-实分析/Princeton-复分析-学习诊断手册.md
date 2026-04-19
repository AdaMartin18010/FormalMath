---
msc_primary: 26-XX
msc_secondary:
  - 28-XX
  - 30-XX
---

# Princeton 复分析：核心定理与深度习题

复分析（complex analysis）研究复可微函数（全纯函数）的理论，是分析学中最优美、最完善的数学分支之一。从 Cauchy 的积分理论到 Riemann 映射定理，复分析的工具在数论、代数几何、流体力学与量子场论中都有不可替代的作用。

## 1. 全纯函数与 Cauchy-Riemann 方程

### 1.1 复可微性

**定义 1.1（全纯函数）**. 设 $\Omega \subseteq \mathbb{C}$ 为开集。函数 $f: \Omega \to \mathbb{C}$ 在 $z_0 \in \Omega$ 全纯（holomorphic），若极限

$$f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$

存在。$f$ 在 $\Omega$ 上全纯，若它在 $\Omega$ 的每点全纯。

**定理 1.2（Cauchy-Riemann）**. 设 $f(z) = u(x,y) + iv(x,y)$，$z = x+iy$。$f$ 在 $z_0$ 复可微当且仅当 $u, v$ 在 $z_0$ 可微且满足 Cauchy-Riemann 方程：

$$\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}, \quad \frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}.$$

*证明*. 设 $f$ 复可微，$f'(z_0) = a + ib$。沿实轴方向：$h \to 0$，

$$\frac{f(z_0+h) - f(z_0)}{h} \to a + ib = u_x + iv_x.$$

沿虚轴方向：$h = ik$，$k \to 0$，

$$\frac{f(z_0+ik) - f(z_0)}{ik} \to \frac{v_y - iu_y}{1} = v_y - iu_y.$$

两者相等得 $u_x = v_y$，$v_x = -u_y$。反之，由可微性：

$$f(z_0+h) - f(z_0) = (u_x + i v_x)h_1 + (u_y + iv_y)h_2 + o(|h|).$$

利用 CR 方程，$(u_y + iv_y)h_2 = (-v_x + iu_x)h_2 = i(u_x + iv_x)h_2$，故：

$$f(z_0+h) - f(z_0) = (u_x + iv_x)(h_1 + ih_2) + o(|h|) = f'(z_0)h + o(|h|).$$

$\square$

## 2. Cauchy 积分定理与积分公式

### 2.1 Cauchy 积分定理

**定理 2.1（Cauchy 积分定理）**. 设 $f$ 在单连通区域 $\Omega$ 上全纯，$\gamma$ 为 $\Omega$ 中的分段光滑闭曲线。则：

$$\oint_\gamma f(z) dz = 0.$$

*证明*. 设 $f = u + iv$，$dz = dx + i dy$。则：

$$\oint_\gamma f(z)dz = \oint_\gamma (u dx - v dy) + i \oint_\gamma (v dx + u dy).$$

由 Green 定理和 CR 方程（$u_x = v_y$，$u_y = -v_x$）：

$$\oint_\gamma (u dx - v dy) = \iint_D (-v_x - u_y) dxdy = 0,$$

$$\oint_\gamma (v dx + u dy) = \iint_D (u_x - v_y) dxdy = 0.$$

$\square$

### 2.2 Cauchy 积分公式

**定理 2.2（Cauchy 积分公式）**. 设 $f$ 在圆盘 $\overline{D}(z_0, R)$ 上全纯。则对 $|z - z_0| < R$：

$$f(z) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = R} \frac{f(\zeta)}{\zeta - z} d\zeta.$$

*证明*. 对固定 $z$，函数 $g(\zeta) = \frac{f(\zeta) - f(z)}{\zeta - z}$（$\zeta \neq z$），$g(z) = f'(z)$ 在圆盘上全纯。由 Cauchy 积分定理，$\oint g = 0$。故：

$$\oint \frac{f(\zeta)}{\zeta - z} d\zeta = f(z) \oint \frac{d\zeta}{\zeta - z} = f(z) \cdot 2\pi i.$$

$\square$

### 2.3 幂级数展开

**定理 2.3**. 全纯函数可局部展开为幂级数：若 $f$ 在 $D(z_0, R)$ 上全纯，则

$$f(z) = \sum_{n=0}^\infty a_n (z-z_0)^n, \quad a_n = \frac{f^{(n)}(z_0)}{n!} = \frac{1}{2\pi i} \oint \frac{f(\zeta)}{(\zeta - z_0)^{n+1}} d\zeta.$$

*证明*. 对 $|\zeta - z_0| = r > |z - z_0|$，

$$\frac{1}{\zeta - z} = \frac{1}{\zeta - z_0} \cdot \frac{1}{1 - \frac{z-z_0}{\zeta-z_0}} = \sum_{n=0}^\infty \frac{(z-z_0)^n}{(\zeta-z_0)^{n+1}}.$$

代入 Cauchy 积分公式并逐项积分（一致收敛）。$\square$

## 3. 留数定理与应用

### 3.1 留数

**定义 3.1（留数）**. 设 $f$ 在 $z_0$ 有孤立奇点，Laurent 展开为 $f(z) = \sum_{n=-\infty}^\infty a_n (z-z_0)^n$。留数为 $\operatorname{Res}(f, z_0) = a_{-1}$。

**定理 3.2（留数定理）**. 设 $f$ 在区域 $\Omega$ 内除有限个孤立奇点 $z_1, \dots, z_n$ 外全纯，$\gamma$ 为包围这些奇点的正向简单闭曲线。则：

$$\oint_\gamma f(z) dz = 2\pi i \sum_{k=1}^n \operatorname{Res}(f, z_k).$$

*证明*. 在每个 $z_k$ 周围取小圆 $C_k$。由 Cauchy 定理，$\oint_\gamma f = \sum_k \oint_{C_k} f$。而 $\oint_{C_k} f = 2\pi i a_{-1}^{(k)} = 2\pi i \operatorname{Res}(f, z_k)$。$\square$

## 4. 例子

### 4.1 例子：实积分的计算

计算 $I = \int_0^\infty \frac{dx}{1+x^4}$。

取围道：上半圆 $C_R = \{Re^{i\theta} : 0 \leq \theta \leq \pi\}$ 与实轴 $[-R, R]$。

$f(z) = 1/(1+z^4)$ 的极点为 $e^{i\pi/4}, e^{i3\pi/4}, e^{i5\pi/4}, e^{i7\pi/4}$。上半平面内有 $z_1 = e^{i\pi/4}$，$z_2 = e^{i3\pi/4}$。

留数计算：$1+z^4 = (z-z_1)(z-z_2)(z-z_3)(z-z_4)$。对单极点：

$$\operatorname{Res}(f, z_1) = \frac{1}{4z_1^3} = \frac{z_1}{4z_1^4} = -\frac{z_1}{4} = -\frac{e^{i\pi/4}}{4}.$$

同理 $\operatorname{Res}(f, z_2) = -\frac{e^{i3\pi/4}}{4}$。

$$\oint f = 2\pi i \cdot \left(-\frac{e^{i\pi/4} + e^{i3\pi/4}}{4}\right) = -\frac{\pi i}{2} \cdot 2i \sin(\pi/4) \cdot e^{i\pi/2} = \frac{\pi}{\sqrt{2}}.$$

当 $R \to \infty$，$\int_{C_R} f \to 0$（$|f| \sim R^{-4}$，弧长 $\pi R$）。故 $2I = \frac{\pi}{\sqrt{2}}$，$I = \frac{\pi}{2\sqrt{2}}$。

### 4.2 例子：Riemann ζ 函数的函数方程

利用 Mellin 变换与 Poisson 求和公式可证：

$$\pi^{-s/2} \Gamma(s/2) \zeta(s) = \pi^{-(1-s)/2} \Gamma((1-s)/2) \zeta(1-s).$$

关键步骤：考虑 theta 函数 $\theta(t) = \sum_{n \in \mathbb{Z}} e^{-\pi n^2 t}$，利用 Poisson 求和 $\theta(t) = t^{-1/2}\theta(1/t)$，计算：

$$\pi^{-s/2}\Gamma(s/2)\zeta(s) = \int_0^\infty t^{s/2-1} \frac{\theta(t)-1}{2} dt.$$

将积分拆分为 $(0,1)$ 和 $(1,\infty)$，对 $(0,1)$ 用 $\theta(t) = t^{-1/2}\theta(1/t)$ 作变量替换 $u = 1/t$，得到对称表达式，即函数方程。$\square$

## 5. 交叉引用

- [实分析](docs/03-分析学/01-实分析/01-实分析.md) — Lebesgue 积分与收敛定理
- [调和分析](docs/03-分析学/07-调和分析/01-调和分析基础.md) — Fourier 变换与全纯函数
- [代数几何](docs/02-代数结构/02-核心理论/代数几何/01-代数几何基础.md) — Riemann 曲面与复结构
- [数论](docs/05-数论/解析数论-基础.md) — ζ 函数与 L-函数
- [微分方程](docs/03-分析学/04-偏微分方程/01-偏微分方程基础.md) — 复方法在 PDE 中的应用

---

**适用**：docs/03-分析学/01-实分析/
