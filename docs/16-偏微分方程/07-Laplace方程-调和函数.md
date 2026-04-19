---
title: Laplace方程-调和函数
description: 系统介绍Laplace方程与调和函数的定义、基本性质、平均值定理、极值原理、Liouville定理、Harnack不等式与收敛定理，建立椭圆型方程的基础理论。
msc_primary:
  - 35J05
msc_secondary:
  - 31A05
  - 31B05
  - 35B50
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

# Laplace方程-调和函数

**稳态的平衡 — 调和函数的优雅理论**

---

## 1. Laplace方程与调和函数

### 1.1 定义

设 $\Omega \subset \mathbb{R}^n$ 为开集。函数 $u \in C^2(\Omega)$ 称为**调和的**（harmonic），若满足**Laplace方程**
$$\Delta u = 0, \quad x \in \Omega$$
其中 $\Delta = \sum_{i=1}^n \frac{\partial^2}{\partial x_i^2}$ 为**Laplace算子**。

若 $\Delta u = f$，称为**Poisson方程**。Laplace方程是Poisson方程在 $f=0$ 时的特例，描述无源稳态场。

### 1.2 物理背景

调和函数描述稳态物理量：
- **热力学**：稳态温度分布（无热源，边界条件固定）；
- **电磁学**：无电荷区域的静电势；
- **流体力学**：不可压缩无旋流的势函数；
- **弹性力学**：某些位移势的均衡状态。

### 1.3 基本例子

**例1**：$\mathbb{R}^n$ 上的线性函数 $u(x) = a \cdot x + b$ 调和（二阶导数为零）。

**例2**：$n=2$ 时，$u(x,y) = e^x \cos y$ 调和，因 $u_{xx} = e^x \cos y = -u_{yy}$。

**例3**：$n \geq 3$ 时，$u(x) = |x|^{2-n}$ 在 $\mathbb{R}^n \setminus \{0\}$ 上调和。验证：$\partial_i u = (2-n)x_i|x|^{-n}$，$\partial_{ii} u = (2-n)|x|^{-n} - n(2-n)x_i^2|x|^{-n-2}$，求和得 $\Delta u = 0$。

---

## 2. 平均值定理

### 2.1 球面平均与体积平均

**定理（平均值性质）**：设 $u$ 在 $\Omega$ 中调和。对任意球 $B(x,r) \subset\subset \Omega$，
$$u(x) = \frac{1}{|\partial B(x,r)|} \int_{\partial B(x,r)} u(y) dS_y = \frac{1}{|B(x,r)|} \int_{B(x,r)} u(y) dy$$

即调和函数在球心的值等于其在球面及球体上的平均值。

*证明*：令 $\phi(r) = \frac{1}{|\partial B_r|} \int_{\partial B_r} u dS$。计算 $\phi'(r)$，利用Green公式及 $\Delta u = 0$，得 $\phi'(r) = 0$。故 $\phi(r) = \phi(0) = u(x)$。对体积平均，积分球面平均即可。$\square$

### 2.2 逆定理

**定理（逆平均值性质）**：若 $u \in C^2(\Omega)$ 满足对任意球 $B(x,r) \subset\subset \Omega$ 的球面平均（或体积平均）等于 $u(x)$，则 $u$ 调和。

*证明*：若 $\Delta u(x_0) > 0$，则在 $x_0$ 的小球内 $\Delta u > 0$。由Green公式，球面平均值大于球心值，矛盾。$\square$

### 2.3 应用

平均值定理是调和函数区别于其他函数的核心特征。它直接推出最大值原理、Harnack不等式等深刻结果。

---

## 3. 最大值原理

### 3.1 强最大值原理

**定理**：设 $u$ 在连通开集 $\Omega$ 中调和。若 $u$ 在某内部点取得全局最大值（或最小值），则 $u$ 在 $\Omega$ 中为常数。

*证明*：设 $u(x_0) = M = \max_{\Omega} u$。令 $S = \{x \in \Omega \mid u(x) = M\}$。$S$ 非空（含 $x_0$）且闭（由连续性）。对 $y \in S$，由平均值性质，若 $u$ 在 $B(y,r)$ 上某点 $< M$，则平均值 $< M$，矛盾。故 $B(y,r) \subset S$，$S$ 开。由连通性，$S = \Omega$。$\square$

### 3.2 弱最大值原理

对有界域 $\Omega$，$u \in C^2(\Omega) \cap C(\overline{\Omega})$ 调和，则
$$\max_{\overline{\Omega}} u = \max_{\partial\Omega} u, \quad \min_{\overline{\Omega}} u = \min_{\partial\Omega} u$$

### 3.3 Hopf边界点引理

若 $u$ 在光滑边界点 $x_0 \in \partial\Omega$ 取得严格极大值，则外法向导数
$$\frac{\partial u}{\partial \nu}(x_0) > 0$$
（除非 $u$ 为常数）。

---

## 4. Liouville定理

### 4.1 有界调和函数

**定理（Liouville）**：在全空间 $\mathbb{R}^n$ 上有界调和函数必为常数。

*证明*：对任意 $x, y \in \mathbb{R}^n$，取大球 $B_R(x)$ 包含 $y$。由平均值性质及有界性，
$$|u(x) - u(y)| = \left|\frac{1}{|B_R|}\int_{B_R(x)} u - \frac{1}{|B_R(y)|}\int_{B_R(y)} u\right|$$
当 $R \to \infty$，重叠区域主导，差趋于零。$\square$

### 4.2 一维情形的推论

$\mathbb{R}$ 上的调和函数满足 $u'' = 0$，即 $u(x) = ax + b$。Liouville定理说明有界性迫使 $a = 0$。

### 4.3 推广

**定理**：$\mathbb{R}^n$ 上下方有界（或上方有界）的调和函数必为常数。

**注**：增长条件不能去掉。$u(x) = x_1$ 在 $\mathbb{R}^n$ 上调和但无界。

---

## 5. Harnack不等式

### 5.1 椭圆Harnack不等式

**定理**：设 $u \geq 0$ 在 $\Omega$ 中调和。对任意连通紧集 $K \subset \Omega$，存在 $C = C(K,\Omega)$ 使得
$$\sup_K u \leq C \inf_K u$$

### 5.2 球上的显式形式

对球 $B_R(0)$，若 $u \geq 0$ 调和，则对 $|x| = r < R$，
$$\frac{R^{n-2}(R-r)}{(R+r)^{n-1}} u(0) \leq u(x) \leq \frac{R^{n-2}(R+r)}{(R-r)^{n-1}} u(0)$$

### 5.3 收敛定理

**Harnack收敛定理**：设 $\{u_k\}$ 为 $\Omega$ 上的单调递增调和函数列，且在某点有界。则 $u_k$ 在紧子集上一致收敛到调和函数。

---

## 6. 基本解与Newton位势

### 6.1 基本解

$\mathbb{R}^n$ 中Laplace方程的**基本解**
$$\Phi(x) = \begin{cases} -\frac{1}{2\pi} \log|x| & n = 2 \\ \frac{1}{n(n-2)\omega_n} |x|^{2-n} & n \geq 3 \end{cases}$$
满足 $-\Delta \Phi = \delta_0$（Dirac测度）。$\omega_n$ 为单位球体积。

### 6.2 Newton位势

对紧支集密度 $f$，Poisson方程 $\Delta u = f$ 的解为**Newton位势**
$$u(x) = \int_{\mathbb{R}^n} \Phi(x-y) f(y) dy$$

---

## 7. 调和多项式与球谐函数

### 7.1 齐次调和多项式

$k$ 次齐次多项式 $P(x)$ 若调和，称为**球谐函数**的径向部分。在球坐标下，$P(x) = r^k Y(\omega)$，$Y$ 为球面上的Laplace-Beltrami算子特征函数。

### 7.2 空间分解

$L^2(S^{n-1})$ 有标准正交基 $\{Y_{k,m}\}$，其中 $Y_{k,m}$ 为 $k$ 阶球谐函数。

**例4（二维）**：$r^k \cos(k\theta)$ 与 $r^k \sin(k\theta)$ 为调和多项式。任意圆盘上的调和函数可展开为Fourier级数
$$u(r,\theta) = a_0 + \sum_{k=1}^\infty r^k (a_k \cos k\theta + b_k \sin k\theta)$$

**例5（三维）**：球谐函数为 $r^l Y_l^m(\theta,\varphi)$，其中 $Y_l^m$ 为连带Legendre函数。

---

## 8. 小结

调和函数论是椭圆型PDE中最经典也最优美的篇章。平均值定理揭示了调和函数与概率论（Brown运动）及几何的深刻联系；最大值原理保证了边值问题解的唯一性与稳定性；Liouville定理说明全空间上调和函数的刚性；Harnack不等式则控制着正调和函数的局部变化。这些性质不仅是Laplace方程的特质，更推广到更一般的椭圆方程，构成了整个椭圆正则性理论的基石。从复分析到几何测度论，从随机过程到最小曲面，调和函数的思想无处不在。
