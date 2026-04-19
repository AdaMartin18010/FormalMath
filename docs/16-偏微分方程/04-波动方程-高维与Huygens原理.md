---
title: 波动方程-高维与Huygens原理
description: 系统介绍高维波动方程的Kirchhoff公式、Poisson公式、降维法、Huygens原理与弥散现象、非齐次方程的Duhamel原理，建立高维波动传播的精确图像。
msc_primary:
  - 35L05
msc_secondary:
  - 35C15
  - 35L15
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
    - id: john_pde
      type: textbook
      title: Partial Differential Equations
      authors:
        - Fritz John
      publisher: Springer
      year: 1982
      msc: 35-01
---

# 波动方程-高维与Huygens原理

**波的传播在空间中 — Kirchhoff公式与维度的奥秘**

---

## 1. 三维波动方程

### 1.1 球面平均法

设 $u(x,t)$ 为 $\mathbb{R}^3 \times (0,\infty)$ 上的波动方程解。对 $x \in \mathbb{R}^3$，定义**球面平均**
$$M_u(x, r, t) = \frac{1}{4\pi r^2} \int_{|y-x|=r} u(y,t) \, dS_y$$

令 $v(r,t) = r M_u(x,r,t)$。计算 $v$ 的各阶导数，利用波动方程与球面积分的性质，可得 $v$ 满足一维波动方程
$$v_{tt} = c^2 v_{rr}$$
（因Laplace算子的径向部分作用在平均上给出 $v_{rr}$，且 $v(0,t) = 0$）。

### 1.2 Kirchhoff公式

对 $v$ 应用D'Alembert公式，并利用 $v(0,t) = 0$ 消去一项，再令 $r \to 0$（此时 $M_u \to u(x,t)$），得**Kirchhoff公式**（1882）：
$$u(x,t) = \frac{\partial}{\partial t}\left(\frac{1}{4\pi c^2 t} \int_{|y-x|=ct} g(y) \, dS_y\right) + \frac{1}{4\pi c^2 t} \int_{|y-x|=ct} h(y) \, dS_y$$

等价地，令 $\sigma = ct$，利用面积分的参数化，
$$u(x,t) = \frac{1}{4\pi c^2 t^2} \int_{|y-x|=ct} \left[g(y) + \nabla g(y) \cdot (y-x) + t \, h(y)\right] dS_y$$

**定理**：$g \in C^3(\mathbb{R}^3)$，$h \in C^2(\mathbb{R}^3)$ 时，Kirchhoff公式给出 $C^2$ 解。

### 1.3 物理解释

三维解仅依赖于以 $x$ 为中心、半径 $ct$ 的**球面**上的初值。这意味着：三维空间中，短暂脉冲（如声音）传播后不留尾迹——波前过后立即恢复平静。

---

## 2. 二维波动方程

### 2.1 降维法（Hadamard）

二维波动方程可视为三维波动方程与 $x_3$ 无关的特解。将三维初值 $g(x_1, x_2, x_3) = g(x_1, x_2)$，$h$ 类似，代入Kirchhoff公式。

球面 $|y-x| = ct$ 与平面 $y_3 = x_3$ 相交为圆盘。将面积分投影到圆盘，得**Poisson公式**（二维）：
$$u(x,t) = \frac{\partial}{\partial t}\left(\frac{1}{2\pi c} \int_{|y-x| \leq ct} \frac{g(y)}{\sqrt{c^2t^2 - |y-x|^2}} dy\right) + \frac{1}{2\pi c} \int_{|y-x| \leq ct} \frac{h(y)}{\sqrt{c^2t^2 - |y-x|^2}} dy$$

### 2.2 与三维的区别

二维解依赖于**圆盘**上的初值，而三维只依赖于**球面**上的初值。这是**Huygens原理**的维度效应的核心体现。

---

## 3. Huygens原理

### 3.1 陈述

**Huygens原理**：对奇数维 $n \geq 3$（$n$ 为奇数），波动方程的解 $u(x,t)$ 仅依赖于以 $x$ 为中心、半径 $ct$ 的**球面**上的初值，而不依赖于球**内部**的初值。

对偶数维或一维，解依赖于**整个球**（或区间）内的初值。

### 3.2 物理解释

- **奇数维**（$n=3$）：波前清晰传播。声音在三维空气中传播时，短促信号（如拍手）到达听众后立刻结束，无"尾音"。
- **偶数维**（$n=2$）：波前有"尾迹"。水面上的波（近似二维）在波前过后仍有残留振动。敲响的鼓声（二维膜）也有类似的持续衰减特性。

### 3.3 数学解释

降维法中，奇数维的球面平均自然给出球面积分；偶数维则需投影到圆盘，引入权重 $(c^2t^2 - r^2)^{-1/2}$，导致内部贡献持续存在。

更深刻地，这与Riesz势的解析性质有关：奇数维时某些分布仅支于球面，偶数维时则支于实心球。

**例1**：三维点源 $g = \delta$，$h = 0$。Kirchhoff公式给出 $u(x,t) = \frac{1}{4\pi c^2 t} \delta_{|x|=ct}$，仅在球壳上非零。

---

## 4. 高维一般公式

### 4.1 一般奇数维

对 $n = 2m + 1$（$m \geq 1$），解由球面积分的 $m$-阶时间导数给出：
$$u(x,t) = c_n \left(\frac{\partial}{\partial t}\right)^{m-1} \left(\frac{1}{t} \frac{\partial}{\partial t}\right)^{m-1} \left(\frac{1}{t} \int_{|y-x|=ct} g(y) dS_y\right) + \text{(}h\text{ 的类似项)}$$

### 4.2 一般偶数维

对 $n = 2m$，解涉及球体内的积分：
$$u(x,t) = c_n \left(\frac{\partial}{\partial t}\right)^{m-1} \left(\frac{1}{t} \frac{\partial}{\partial t}\right)^{m-1} \left(\frac{1}{t} \int_{|y-x| \leq ct} \frac{g(y)}{\sqrt{c^2t^2 - |y-x|^2}} dy\right) + \text{(}h\text{ 的类似项)}$$

**例2**（$n=1$）：D'Alembert公式依赖区间，是Huygens原理失效的最简单例子。

---

## 5. 弥散与衰减

### 5.1 高维衰减估计

对紧支集初值，三维波动方程解满足
$$|u(x,t)| \leq \frac{C}{t}, \quad t \to \infty$$
二维解衰减更慢：$|u(x,t)| \leq C/\sqrt{t}$。

**原因**：三维能量沿球面扩散（面积 $\sim t^2$），振幅 $\sim 1/t$；二维能量在圆盘内扩散（面积 $\sim t^2$），但由于内部持续贡献，有效扩散更慢。

### 5.2 弥散方程的对比

波动方程的解不衰减到零的能量（能量守恒），但振幅在局部点衰减（能量扩散到更大区域）。这与Schrödinger方程的 $L^\infty$ 衰减（$\sim t^{-n/2}$）或热方程的指数衰减不同。

---

## 6. 非齐次波动方程

### 6.1 Duhamel原理

对非齐次方程
$$u_{tt} - c^2 \Delta u = f(x,t), \quad u(x,0) = u_t(x,0) = 0$$
解由**Duhamel原理**给出
$$u(x,t) = \int_0^t w(x,t;s) ds$$
其中 $w(\cdot, \cdot; s)$ 为初值 $w(\cdot, s; s) = 0$，$w_t(\cdot, s; s) = f(\cdot, s)$ 的齐次波动方程解。

在三维，
$$u(x,t) = \int_0^t \frac{1}{4\pi c^2 (t-s)} \int_{|y-x|=c(t-s)} f(y,s) dS_y \, ds$$

### 6.2 推迟势

物理上，$u(x,t)$ 由源 $f$ 在**推迟时间** $t_r = t - |x-y|/c$ 的贡献叠加而成。这体现了相对论因果性：信息以有限速度 $c$ 传播。

---

## 7. 小结

高维波动方程的解揭示了维度对波传播的深刻影响。Kirchhoff公式和Poisson公式分别给出了三维与二维的精确解，Huygens原理阐明了奇数维与偶数维的根本差异：奇数维波前清晰，偶数维波有尾迹。降维法将高维与低维联系起来，而衰减估计则反映了能量在不同维度空间中的扩散方式。Duhamel原理将非齐次问题纳入统一的推迟势框架，是经典场论与电动力学的数学基础。这些现象不仅是数学的精妙之处，也直接对应着物理世界中声波、光波与水波的不同行为。
