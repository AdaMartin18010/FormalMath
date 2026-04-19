---
title: 波动方程-D'Alembert公式
description: 系统介绍一维波动方程的D'Alembert公式推导、初值问题的求解、行波解的叠加、半直线与有界弦问题、能量守恒与唯一性，建立波动方程的基本理论。
msc_primary:
  - 35L05
msc_secondary:
  - 35C05
  - 35L10
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
    - id: strauss_pde
      type: textbook
      title: Partial Differential Equations: An Introduction
      authors:
        - Walter A. Strauss
      publisher: Wiley
      year: 2008
      msc: 35-01
---

# 波动方程-D'Alembert公式

**振动与波的精确解 — 行波的叠加与因果性**

---

## 1. 一维波动方程的推导

### 1.1 物理背景

设 $u(x,t)$ 为均匀弦在位置 $x$、时刻 $t$ 的横向位移。对微元 $[x, x+dx]$，应用Newton第二定律。设张力为 $T$，线密度为 $\rho$，在小振幅假设下，水平分量近似平衡，竖直分量给出
$$\rho \, dx \cdot u_{tt} = T(u_x(x+dx,t) - u_x(x,t))$$
取极限 $dx \to 0$ 得
$$u_{tt} = c^2 u_{xx}, \quad c = \sqrt{T/\rho}$$
$c$ 为**波速**，由弦的材料性质（张力与密度）决定。

### 1.2 初值问题

**Cauchy问题**：求 $u(x,t)$ 满足
$$\begin{cases} u_{tt} = c^2 u_{xx}, & x \in \mathbb{R}, \, t > 0 \\ u(x,0) = g(x), & x \in \mathbb{R} \\ u_t(x,0) = h(x), & x \in \mathbb{R} \end{cases}$$
$g$ 为初始位移，$h$ 为初始速度。

---

## 2. D'Alembert公式

### 2.1 因式分解法

波动算子可因式分解
$$\partial_t^2 - c^2 \partial_x^2 = (\partial_t - c\partial_x)(\partial_t + c\partial_x)$$

引入特征坐标
$$\xi = x + ct, \quad \eta = x - ct$$
则方程变为 $u_{\xi\eta} = 0$。

### 2.2 通解

对 $u_{\xi\eta} = 0$，先对 $\eta$ 积分得 $u_\xi = F'(\xi)$，再对 $\xi$ 积分得
$$u(x,t) = F(x + ct) + G(x - ct)$$
其中 $F, G$ 为任意可微函数。这是**行波解**：$F(x+ct)$ 为向左传播的波（速度 $-c$），$G(x-ct)$ 为向右传播的波（速度 $c$）。

### 2.3 D'Alembert公式

由初值条件
$$\begin{cases} F(x) + G(x) = g(x) \\ cF'(x) - cG'(x) = h(x) \end{cases}$$

积分第二式得 $c(F(x) - G(x)) = \int_0^x h(s)ds + C$。联立解得
$$F(x) = \frac{1}{2}g(x) + \frac{1}{2c}\int_0^x h(s)ds + \frac{C}{2}$$
$$G(x) = \frac{1}{2}g(x) - \frac{1}{2c}\int_0^x h(s)ds - \frac{C}{2}$$

代入通解得**D'Alembert公式**（1746）：
$$u(x,t) = \frac{g(x+ct) + g(x-ct)}{2} + \frac{1}{2c}\int_{x-ct}^{x+ct} h(s)\, ds$$

**定理**：若 $g \in C^2(\mathbb{R})$，$h \in C^1(\mathbb{R})$，则D'Alembert公式给出 $C^2$ 解，且解唯一。

---

## 3. 解的性质

### 3.1 依赖区域与影响区域

$u(x_0, t_0)$ 的值仅依赖于：
- $g$ 在 $x_0 \pm ct_0$ 的值；
- $h$ 在区间 $[x_0 - ct_0, x_0 + ct_0]$ 上的值。

此区间称为**依赖区间**。以 $(x_0,t_0)$ 为顶点的三角形区域（由特征线 $x \pm ct = x_0 \pm ct_0$ 围成）称为**决定区域**。

反之，初值点 $x_0$ 的影响沿特征线 $x \pm ct = x_0$ 传播，形成**影响区域**（向前的特征锥 $|(x-x_0)| \leq c(t-t_0)$）。

### 3.2 因果性

波动方程具有**有限传播速度** $c$：时刻 $t$ 的扰动在 $t + \Delta t$ 时最多传播距离 $c\Delta t$。这与热方程的无穷传播速度形成鲜明对比。

**例1（初值局部扰动）**：设 $g$ 为紧支集（只在 $[a,b]$ 非零），$h = 0$。解为两个半波 $g(x+ct)/2$ 与 $g(x-ct)/2$ 分别向左、右传播，振幅减半。在 $|x| > \max(|a|,|b|) + ct$ 处，$u = 0$。

---

## 4. 半直线上的波动方程

### 4.1 反射法

对 $x > 0$（半直线），边界条件 $u(0,t) = 0$（固定端）。用**奇延拓**将初值 $g, h$ 延拓到全直线：
$$\tilde{g}(x) = \begin{cases} g(x) & x > 0 \\ -g(-x) & x < 0 \end{cases}$$
对 $h$ 类似。

D'Alembert公式应用于延拓初值，当 $x > ct$ 时与全直线解一致；当 $x < ct$ 时，$x-ct < 0$，奇延拓导致反射波：
$$u(x,t) = \frac{g(x+ct) - g(ct-x)}{2} + \frac{1}{2c}\int_{ct-x}^{x+ct} h(s)ds$$

**物理意义**：波在边界 $x=0$ 处**反相反射**（固定端）。入射波 $g(x-ct)$ 与反射波 $-g(ct-x)$ 叠加，在边界处相消为零。

### 4.2 自由端边界条件

若 $u_x(0,t) = 0$（自由端），用**偶延拓**。反射波**同相反射**。在 $x < ct$ 时，
$$u(x,t) = \frac{g(x+ct) + g(ct-x)}{2} + \frac{1}{2c}\left(\int_0^{x+ct} h(s)ds + \int_0^{ct-x} h(s)ds\right)$$

---

## 5. 有界弦的振动

### 5.1 分离变量法

对有界弦 $x \in [0, L]$，固定端 $u(0,t) = u(L,t) = 0$。设 $u(x,t) = X(x)T(t)$，代入波动方程得
$$\frac{T''}{c^2 T} = \frac{X''}{X} = -\lambda$$

$X$ 满足Sturm-Liouville问题
$$X'' + \lambda X = 0, \quad X(0) = X(L) = 0$$
得特征值 $\lambda_n = (n\pi/L)^2$，特征函数 $X_n(x) = \sin(n\pi x/L)$。

$T_n(t) = A_n \cos(\omega_n t) + B_n \sin(\omega_n t)$，其中 $\omega_n = cn\pi/L$ 为**固有频率**。

### 5.2 Fourier级数解

通解为模态叠加
$$u(x,t) = \sum_{n=1}^\infty \sin\frac{n\pi x}{L}\left(A_n \cos\omega_n t + B_n \sin\omega_n t\right)$$
系数由初值确定：
$$A_n = \frac{2}{L}\int_0^L g(x)\sin\frac{n\pi x}{L}dx, \quad B_n = \frac{2}{\omega_n L}\int_0^L h(x)\sin\frac{n\pi x}{L}dx$$

**例2（拨弦）**：$g(x)$ 为三角波（如吉他弦被拨在 $x = L/2$），$h = 0$。解为驻波的叠加，基频为 $\omega_1 = c\pi/L$，泛音为整数倍频 $\omega_n = n\omega_1$。

### 5.3 能量

有界弦的总能量
$$E(t) = \frac{1}{2}\int_0^L (u_t^2 + c^2 u_x^2)dx$$
对固定端，$E(t) = E(0)$（能量守恒）。不同模态之间无能量交换。

---

## 6. 非齐次波动方程

### 6.1 Duhamel原理

对非齐次方程
$$u_{tt} - c^2 u_{xx} = f(x,t), \quad u(x,0) = u_t(x,0) = 0$$
解为
$$u(x,t) = \int_0^t w(x,t;s) ds$$
其中 $w(\cdot, \cdot; s)$ 为初值 $w(\cdot, s; s) = 0$，$w_t(\cdot, s; s) = f(\cdot, s)$ 的齐次波动方程解。

由D'Alembert公式，
$$u(x,t) = \frac{1}{2c}\int_0^t \int_{x-c(t-s)}^{x+c(t-s)} f(y,s) dy ds$$

### 6.2 物理解释

非齐次项 $f$ 可视为外力分布。Duhamel原理将连续外力分解为瞬时脉冲的叠加，每个脉冲产生一个以当时初速度传播的波。

---

## 7. 能量守恒与唯一性

### 7.1 能量积分

定义波动方程的**能量**
$$E(t) = \frac{1}{2}\int_{-\infty}^\infty \left(u_t^2 + c^2 u_x^2\right) dx$$
（对无界域，假设 $u$ 在无穷远处充分衰减）。

**定理**：对波动方程的光滑解，$E(t) = E(0)$（能量守恒）。

*证明*：
$$\frac{dE}{dt} = \int_{-\infty}^\infty (u_t u_{tt} + c^2 u_x u_{xt}) dx = \int_{-\infty}^\infty u_t (u_{tt} - c^2 u_{xx}) dx = 0$$
（分部积分，边界项消失）。$\square$

### 7.2 唯一性

**定理**：波动方程的初值问题在 $C^2$ 中至多有一个解。

*证明*：设 $u_1, u_2$ 均为解，则 $w = u_1 - u_2$ 满足零初值。由能量守恒，$E_w(t) = E_w(0) = 0$，故 $w_t = w_x = 0$，$w = \text{const} = 0$。$\square$

---

## 8. 小结

D'Alembert公式以一维波动方程的行波分解为基础，将初值问题约化为初值的平移与积分。其揭示的有限传播速度、特征线与因果结构是双曲型方程的核心特征。反射法处理边界，能量法证明唯一性，分离变量法则将问题与Fourier分析联系，给出驻波的模态分解。非齐次问题的Duhamel原理展示了线性叠加思想的力量。这些工具共同构成波动方程理论的基石，并直接推广到更高维与更复杂的情形。
