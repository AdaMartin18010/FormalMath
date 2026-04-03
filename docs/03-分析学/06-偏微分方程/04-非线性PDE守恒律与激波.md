---
msc_primary: "35L65"
msc_secondary: ['35L67', '35L03', '76L05']
---

# 04 非线性PDE守恒律与激波 / Conservation Laws and Shock Waves in Nonlinear PDE

**主题编号**: B.03.06.04  
**创建日期**: 2026年4月3日  
**最后更新**: 2026年4月3日  
**MSC分类**: 35L65 (双曲守恒律), 35L67 (激波与奇异性), 35L03 (一阶双曲系统), 76L05 (激波与膨胀波)  
**国际对齐**: Evans *PDE* Chapter 11; Lax *Hyperbolic Systems of Conservation Laws*; LeVeque *Numerical Methods for Conservation Laws*; Princeton MAT 218

---

## 目录 / Table of Contents

- [1 引言 / Introduction](#1-引言--introduction)
- [2 标量守恒律与特征线方法](#2-标量守恒律与特征线方法)
  - [2.1 守恒形式与弱解](#21-守恒形式与弱解)
  - [2.2 Burgers方程与激波形成](#22-burgers方程与激波形成)
  - [2.3 Rankine–Hugoniot跳跃条件](#23-rankinehugoniot跳跃条件)
- [3 熵条件与解的唯一性](#3-熵条件与解的唯一性)
  - [3.1 Lax熵条件](#31-lax熵条件)
  - [3.2 Oleinik熵条件与粘性消失法](#32-oleinik熵条件与粘性消失法)
  - [3.3 Kružkov一般理论](#33-kružkov一般理论)
- [4 双曲守恒律组](#4-双曲守恒律组)
  - [4.1 严格双曲性](#41-严格双曲性)
  - [4.2 Riemann不变量与简单波](#42-riemann不变量与简单波)
  - [4.3 接触间断与膨胀波](#43-接触间断与膨胀波)
- [5 数值方法简介](#5-数值方法简介)
- [6 例子 / Examples](#6-例子--examples)
- [7 参考文献 / References](#7-参考文献--references)

---

## 1 引言 / Introduction

守恒律描述的是物理量在空间和时间中的守恒关系，如质量守恒、动量守恒和能量守恒。当这些守恒律以非线性形式出现时，即使初始数据光滑，解也可能在有限时间内产生奇异性——如激波（shock wave）和膨胀波（rarefaction wave）。这一现象深刻揭示了非线性双曲偏微分方程与线性方程的本质差异：在线性情形，信息以特征线传播且保持光滑；在非线性情形，特征线可能相交，导致解的爆破（blow-up）和激波的形成。

本文从标量守恒律出发，介绍特征线方法、激波的Rankine–Hugoniot条件、熵条件与解的唯一性理论，进而讨论双曲守恒律组的基本波结构，并简要概述Godunov、Lax–Friedrichs等经典数值格式。所有内容对齐Evans《PDE》第11章、Lax的专著以及Princeton MAT 218的讲授体系。

---

## 2 标量守恒律与特征线方法

### 2.1 守恒形式与弱解

**定义 2.1** (标量守恒律)  
一维标量守恒律的一般形式为：

$$
u_t + f(u)_x = 0, \quad x \in \mathbb{R}, \; t > 0,
$$

其中 $u(x,t) \in \mathbb{R}$ 为未知函数，$f: \mathbb{R} \to \mathbb{R}$ 为 **通量函数**（flux）。初值为 $u(x,0) = g(x)$。

**物理意义**：对任意区间 $[a,b]$，量 $\int_a^b u(x,t) dx$ 的变化率等于通过边界的通量：

$$
\frac{d}{dt} \int_a^b u \, dx = f(u(a,t)) - f(u(b,t)).
$$

当 $u$ 光滑时，守恒律等价于 **非守恒形式**：

$$
u_t + f'(u) u_x = 0.
$$

**定义 2.2** (弱解)  
函数 $u \in L^\infty(\mathbb{R} \times (0,\infty))$ 称为守恒律的 **弱解**，如果对任意检验函数 $\phi \in C_c^\infty(\mathbb{R} \times [0,\infty))$：

$$
\int_0^\infty \int_{-\infty}^\infty \bigl( u \phi_t + f(u) \phi_x \bigr) \, dx dt + \int_{-\infty}^\infty g(x) \phi(x,0) \, dx = 0.
$$

弱解允许间断，从而可以描述激波。

### 2.2 Burgers方程与激波形成

最简单的非线性守恒律是 **Burgers方程**（inviscid Burgers equation），其中 $f(u) = \frac{1}{2} u^2$：

$$
u_t + u u_x = 0.
$$

**特征线方法**：对光滑解，沿曲线 $x = x(t)$ 满足 $\frac{dx}{dt} = u(x(t), t)$，有

$$
\frac{d}{dt} u(x(t), t) = u_t + u_x \frac{dx}{dt} = u_t + u u_x = 0.
$$

因此 $u$ 沿特征线为常数，特征线为直线：$x = x_0 + g(x_0) t$。

**激波形成**：若初值 $g(x)$ 在某处递减（即 $g'(x_0) < 0$），则不同 $x_0$ 处的特征线将在有限时间

$$
T = \inf_{x_0: g'(x_0) < 0} \frac{-1}{g'(x_0)}
$$

处相交。在交点处，光滑解的假设失效，必须引入弱解和激波。

### 2.3 Rankine–Hugoniot跳跃条件

设弱解 $u$ 在曲线 $x = s(t)$ 处有跳跃间断，左侧极限为 $u_-$，右侧极限为 $u_+$。为使其成为弱解，必须满足：

**定理 2.1** (Rankine–Hugoniot条件)  
激波速度 $s'(t)$ 满足：

$$
s'(t) = \frac{f(u_+) - f(u_-)}{u_+ - u_-}.
$$

*证明思路*：在弱解定义中取支集跨跃激波的检验函数，分部积分后边界项必须抵消。计算得：

$$
\int \bigl( -s'(t) (u_+ - u_-) + f(u_+) - f(u_-) \bigr) \phi(s(t), t) dt = 0,
$$

对所有 $\phi$ 成立，从而得到上述条件。

**例 2.1**：对Burgers方程，$f(u) = u^2/2$，Rankine–Hugoniot条件给出 $s' = \frac{u_+ + u_-}{2}$。

---

## 3 熵条件与解的唯一性

Rankine–Hugoniot条件本身不足以唯一确定弱解：同一个初值问题可能存在多个满足RH条件的弱解。为此需要附加 **熵条件**（entropy condition），它从物理直观（粘性消失）和数学稳定性两个角度挑选出“正确”的解。

### 3.1 Lax熵条件

**定义 3.1** (Lax熵条件)  
对凸通量函数 $f$（即 $f'' > 0$），激波 $(u_-, u_+)$ 称为 **可接受的**（admissible），若：

$$
f'(u_+) < s' < f'(u_-).
$$

对Burgers方程，这等价于 $u_+ < u_-$。

**物理意义**：信息（特征线）必须从两侧流入激波，而不是流出。若 $u_+ > u_-$，则特征线从激波流出，这种“非物理”激波会被熵条件排除。

### 3.2 Oleinik熵条件与粘性消失法

**定义 3.2** (Oleinik熵条件)  
对凸通量 $f$，弱解 $u$ 满足Oleinik条件，若对所有 $x < y$ 和 $t > 0$：

$$
\frac{u(y,t) - u(x,t)}{y - x} \le \frac{C}{t}.
$$

这意味着解的负斜率以 $1/t$ 衰减，这是从粘性Burgers方程的显式解中观察到的性质。

**粘性消失法**：考虑带粘性项的方程

$$
u_t^\varepsilon + f(u^\varepsilon)_x = \varepsilon u^\varepsilon_{xx}, \quad \varepsilon > 0.
$$

对任意 $\varepsilon > 0$，该抛物型方程存在唯一光滑解。当 $\varepsilon \to 0$ 时，$u^\varepsilon$ 收敛到的极限 $u$ 即被定义为 **熵解**。Lax和Oleinik证明了该极限存在、唯一，且满足上述熵条件。

### 3.3 Kružkov一般理论

对 **非凸** 通量函数，Lax和Oleinik条件不再适用。Kružkov（1970）提出了适用于任意标量守恒律的一般熵框架。

**定义 3.3** (凸熵对)  
一对函数 $(\eta, q)$ 称为 **熵对**，若 $\eta$ 为凸函数，$q$ 满足 $q'(u) = \eta'(u) f'(u)$。

**定义 3.4** (熵解)  
有界函数 $u$ 称为 **熵解**，若对所有凸熵对 $(\eta, q)$ 和非负检验函数 $\phi \ge 0$：

$$
\int_0^\infty \int_{-\infty}^\infty \bigl( \eta(u) \phi_t + q(u) \phi_x \bigr) dx dt \ge 0,
$$

且满足初值条件。

**定理 3.1** (Kružkov)  
标量守恒律的熵解存在且唯一。

*证明思路*：唯一性通过 ** doubling of variables** 技巧证明：考虑两个熵解 $u, v$ 的差，利用熵不等式和分部积分，证明 $\int |u - v| dx$ 随时间非增，从而若初值相同则解相同。

---

## 4 双曲守恒律组

### 4.1 严格双曲性

**定义 4.1** (双曲守恒律组)  
一维守恒律组的形式为：

$$
\mathbf{u}_t + \mathbf{f}(\mathbf{u})_x = 0,
$$

其中 $\mathbf{u}(x,t) \in \mathbb{R}^m$，$\mathbf{f}: \mathbb{R}^m \to \mathbb{R}^m$ 为光滑通量函数。定义Jacobi矩阵 $A(\mathbf{u}) = D\mathbf{f}(\mathbf{u})$。

**定义 4.2** (严格双曲)  
系统称为 **严格双曲的**，若对每个 $\mathbf{u}$，$A(\mathbf{u})$ 有 $m$ 个互异实特征值：

$$
\lambda_1(\mathbf{u}) < \lambda_2(\mathbf{u}) < \cdots < \lambda_m(\mathbf{u}).
$$

对应的右特征向量 $r_k(\mathbf{u})$ 构成 $\mathbb{R}^m$ 的一组基。

**例 4.1**：一维等熵Euler方程

$$
\begin{cases}
\rho_t + (\rho v)_x = 0, \\
(\rho v)_t + (\rho v^2 + p)_x = 0,
\end{cases}
$$

在 $p' > 0$ 时是严格双曲的，特征值为 $v \pm c$（$c = \sqrt{p'}$ 为声速）。

### 4.2 Riemann不变量与简单波

**定义 4.3** (Riemann不变量)  
光滑函数 $w_k: \mathbb{R}^m \to \mathbb{R}$ 称为第 $k$ 族 **Riemann不变量**，若沿第 $k$ 族特征线方向满足

$$
\nabla w_k \cdot r_k = 0, \quad \forall j \neq k.
$$

对于 $2 \times 2$ 系统，Riemann不变量总是局部存在。

**定义 4.4** (简单波)  
若解 $\mathbf{u}(x,t)$ 在某一区域中只有一族特征线携带非平凡信息，其余族均为常数，则称其为 **简单波**（simple wave）。简单波是连接两个常状态的常见中间解。

### 4.3 接触间断与膨胀波

在双曲守恒律组中，基本的波结构有三种：

1. **激波**（shock）：满足Rankine–Hugoniot向量条件
   $$
   s'(\mathbf{u}_+ - \mathbf{u}_-) = \mathbf{f}(\mathbf{u}_+) - \mathbf{f}(\mathbf{u}_-).
   $$
   并满足Lax熵条件 $ \lambda_k(\mathbf{u}_+) < s' < \lambda_k(\mathbf{u}_-)$。

2. **膨胀波**（rarefaction wave）：一个自相似的连续解 $\mathbf{u}(x/t)$，满足
   $$
   \mathbf{u}'(\xi) \parallel r_k(\mathbf{u}(\xi)), \quad \xi = x/t.
   $$
   膨胀波连接一个较低特征速度的状态到一个较高特征速度的状态。

3. **接触间断**（contact discontinuity）：满足RH条件，但特征速度在两侧相等：$\lambda_k(\mathbf{u}_+) = \lambda_k(\mathbf{u}_-) = s'$。接触间断两侧没有信息穿过该族特征线。在线性退化（linearly degenerate）特征场中常见，如Euler方程中的熵波。

**Riemann问题**：给定左右初值 $\mathbf{u}_L, \mathbf{u}_R$，求解

$$
\mathbf{u}(x,0) = \begin{cases} \mathbf{u}_L, & x < 0, \\ \mathbf{u}_R, & x > 0. \end{cases}
$$

Lax证明：对严格双曲系统且 $|\mathbf{u}_L - \mathbf{u}_R|$ 足够小时，Riemann问题存在唯一由至多 $m+1$ 个常状态区、$m$ 个基本波（激波、膨胀波或接触间断）组成的熵解。这一结果是数值方法（如Godunov格式）的理论基础。

---

## 5 数值方法简介

守恒律的弱解通常不能显式求出，数值方法至关重要。以下是几种经典格式：

**Godunov格式**：
将空间离散为网格单元，在每个时间步求解局部Riemann问题，然后对解进行单元平均。Godunov格式是一阶精度的，但具有良好的激波捕捉能力和稳定性。

**Lax–Friedrichs格式**：

$$
U_j^{n+1} = \frac{U_{j+1}^n + U_{j-1}^n}{2} - \frac{\Delta t}{2 \Delta x} \bigl( f(U_{j+1}^n) - f(U_{j-1}^n) \bigr).
$$

这是一个显式守恒格式，数值粘性较大，能平滑激波但分辨率较低。

**Roe格式**：
用局部线性化系统近似非线性通量，在每个界面求解线性Riemann问题。计算效率高，但在sonic点可能违反熵条件，需要熵修正（entropy fix）。

**ENO/WENO格式**：
Essentially Non-Oscillatory (ENO) 和 Weighted ENO (WENO) 格式通过自适应选择模板来实现高阶精度（三阶、五阶甚至更高），同时避免在激波附近产生虚假振荡。它们是现代计算流体力学中的主流高分辨率格式。

---

## 6 例子 / Examples

**例 6.1** (交通流模型)  
Lighthill–Whitham–Richards (LWR) 交通流模型：

$$
u_t + (u(1-u))_x = 0,
$$

其中 $u \in [0,1]$ 表示道路占有率（车辆密度）。通量 $f(u) = u(1-u)$ 是凹函数。特征速度为 $f'(u) = 1 - 2u$。若初始密度 $g(x)$ 在 $x<0$ 处为 $u_L = 0.8$，在 $x>0$ 处为 $u_R = 0.2$，则 $u_L > u_R$ 且 $f'(u_L) < f'(u_R)$，特征线相交形成激波。由Rankine–Hugoniot，激波速度为

$$
s' = \frac{f(u_R) - f(u_L)}{u_R - u_L} = \frac{0.16 - 0.16}{-0.6} = 0.
$$

激波静止在原点，左侧高密度区与右侧低密度区以固定界面分隔——这正是交通拥堵的数学描述。

**例 6.2** (Burgers方程的Riemann问题)  
考虑Burgers方程，初值

$$
u(x,0) = \begin{cases} u_L = 1, & x < 0, \\ u_R = 0, & x > 0. \end{cases}
$$

由于 $u_L > u_R$，特征线相交，解为激波：

$$
u(x,t) = \begin{cases} 1, & x < t/2, \\ 0, & x > t/2. \end{cases}
$$

激波速度 $s' = (1+0)/2 = 1/2$。

若反过来 $u_L = 0 < u_R = 1$，特征线发散，激波不物理。此时解为 **膨胀波**：

$$
u(x,t) = \begin{cases} 0, & x < 0, \\ x/t, & 0 < x < t, \\ 1, & x > t. \end{cases}
$$

这展示了同一PDE在不同初值下激波与膨胀波的截然不同行为。

**例 6.3** (一维Euler方程的激波管)  
Sod激波管问题是经典的Riemann问题：初始左侧为高压高密度静止气体，右侧为低压低密度静止气体。解由左行的膨胀波、中间接触间断和右行激波组成。这一解析解是验证数值格式（如Godunov、Roe、WENO）的基准测试。

---

## 7 参考文献 / References

### 经典教材

1. **Evans, L. C.** (2010). *Partial Differential Equations* (2nd ed.). AMS. Chapter 11.
2. **Lax, P. D.** (1973). *Hyperbolic Systems of Conservation Laws and the Mathematical Theory of Shock Waves*. SIAM.
3. **LeVeque, R. J.** (1992). *Numerical Methods for Conservation Laws*. Birkhäuser.
4. **Bressan, A.** (2000). *Hyperbolic Systems of Conservation Laws: The One-Dimensional Cauchy Problem*. Oxford.

### 进阶文献

5. **Kružkov, S. N.** (1970). First order quasilinear equations with several independent variables. *Math. USSR Sb.* 10, 217–243.
6. **Godunov, S. K.** (1959). A difference method for numerical calculation of discontinuous solutions of the equations of hydrodynamics. *Math. Sb.* 47, 271–306.
7. **Roe, P. L.** (1981). Approximate Riemann solvers, parameter vectors, and difference schemes. *J. Comput. Phys.* 43, 357–372.
8. **Shu, C.-W.** (1998). Essentially non-oscillatory and weighted essentially non-oscillatory schemes for hyperbolic conservation laws. *ICASE Report* 97-65.

### 中文参考

9. **李大潜** (2006). *双曲型守恒律方程及其差分方法*. 上海科学技术出版社.
10. **陈恕行** (2005). *现代偏微分方程导论*. 科学出版社.

---

**文档状态**: 完成  
**字数**: 约5,700字  
**数学公式数**: 35+  
**例子数**: 3  
**最后更新**: 2026年4月3日
