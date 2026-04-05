---
msc_primary: 37J35
msc_secondary:
- 37J15
- 70H06
- 53D20
title: 可积系统与Liouville定理
processed_at: '2026-04-05'
---
# 可积系统与Liouville定理

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

可积系统是经典力学中的一类特殊系统，它们拥有足够多的守恒量，使得运动方程可以完全求解。Liouville可积性是判断系统可积性的精确数学标准，而Arnold-Liouville定理则提供了可积系统的几何描述——运动限制在相空间的环面上。

**核心思想**: 可积系统的相空间可纤维化为不变环面，运动是准周期的。

---

## 📝 基础概念

### 1.1 Liouville可积性

**定义 1.1** (可积系统 / Liouville可积)
设 $(M, \omega)$ 是 $2n$ 维辛流形，$H$ 是Hamilton函数。若存在 $n$ 个函数 $F_1 = H, F_2, \ldots, F_n$ 满足：

1. **函数独立**: $dF_1, \ldots, dF_n$ 在 $M$ 上几乎处处线性无关
2. **互相对合**: $\{F_i, F_j\} = 0$ 对所有 $i, j$
3. **完备性**: Hamilton流是完备的（解对所有时间存在）

则称系统为**Liouville可积**（或完全可积）。

**定义 1.2** (水平集)
对 $c = (c_1, \ldots, c_n) \in \mathbb{R}^n$，**水平集**定义为：
$$M_c = \{(q, p) \in M : F_i(q, p) = c_i, i = 1, \ldots, n\}$$

---

### 1.2 作用-角变量

**定义 1.3** (作用-角变量)
**作用-角变量**是正则坐标 $(I_1, \ldots, I_n, \theta^1, \ldots, \theta^n)$ 满足：

1. **作用量** $I_i$ 仅依赖于守恒量 $F_j$
2. **角变量** $\theta^i \in [0, 2\pi)$ 是周期坐标
3. 辛形式保持：$\omega = dI_i \wedge d\theta^i$

**作用量的定义**: 在环面上：
$$I_i = \frac{1}{2\pi}\oint_{\gamma_i} p \, dq$$
其中 $\gamma_i$ 是环面上的基本循环。

---

## 🎯 核心定理

### 2.1 Arnold-Liouville定理

**定理 2.1** (Arnold-Liouville定理)
设 $(M, \omega, H)$ 是Liouville可积系统，$F_1, \ldots, F_n$ 是对合的独立守恒量。考虑水平集 $M_c$：

若 $M_c$ 是紧致且连通的，则：

1. $M_c$ 微分同胚于 $n$ 维环面 $\mathbb{T}^n$
2. 存在**作用-角变量** $(I_1, \ldots, I_n, \theta^1, \ldots, \theta^n)$ 使得 $\omega = dI_i \wedge d\theta^i$
3. Hamilton函数仅依赖于作用量：$H = H(I_1, \ldots, I_n)$
4. 运动方程为：$\dot{I}_i = 0$，$\dot{\theta}^i = \omega^i(I) = \frac{\partial H}{\partial I_i}$

**证明概要**:

1. **环面结构**: 由于 $\{F_i, F_j\} = 0$，$X_{F_i}$ 的流互相对易。这些流生成 $\mathbb{R}^n$ 在 $M_c$ 上的作用。由紧致性和连通性，稳定子是格点，所以 $M_c \cong \mathbb{R}^n/\mathbb{Z}^n = \mathbb{T}^n$。

2. **作用-角变量**: 在环面上定义作用量 $I_i$ 为作用在基本循环上的积分。通过正则变换得到角变量。

3. **运动方程**: 在作用-角变量下，$\{I_i, \theta^j\} = \delta_i^j$，$\{I_i, I_j\} = \{\theta^i, \theta^j\} = 0$。由 $\{H, I_i\} = 0$ 知 $H$ 不依赖于 $\theta$。
$\square$

**物理意义**: 可积系统的运动是准周期的，在环面上沿直线匀速运动。作用量是绝热不变量，角变量随时间线性增长。

---

### 2.2 重要例子

**谐振子**:

$H = \frac{1}{2}(p^2 + \omega^2 q^2)$。作用-角变量为：
$$I = \frac{1}{2\omega}(p^2 + \omega^2 q^2), \quad \theta = \arctan\left(\frac{\omega q}{p}\right)$$

Hamilton函数变为 $H = \omega I$，运动：$\dot{I} = 0$，$\dot{\theta} = \omega$。

**Kepler问题**:

$H = \frac{|p|^2}{2} - \frac{\mu}{|q|}$。除能量外还有角动量 $L$ 和Runge-Lenz向量守恒，系统可积。

---

### 2.3 KAM理论简介

**定理 2.2** (KAM定理，简化形式)
考虑近可积系统 $H = H_0(I) + \epsilon H_1(I, \theta)$，其中 $H_0$ 是非退化的（$\det(\partial^2 H_0/\partial I_i \partial I_j) \neq 0$）。

对足够小的 $\epsilon$，大多数非共振不变环面得以保持，仅稍有变形。

**意义**: KAM理论解释了为什么太阳系是稳定的——尽管行星间有相互作用，大多数准周期轨道在小扰动下保持稳定。

---

## 💡 实战问题

### 问题1：二维谐振子的可积性

**问题**: 证明二维各向异性谐振子 $H = \frac{1}{2}(p_1^2 + p_2^2) + \frac{1}{2}(\omega_1^2 q_1^2 + \omega_2^2 q_2^2)$ 是可积的，并找出作用-角变量。

**解答**:

守恒量：
$$F_1 = H_1 = \frac{1}{2}(p_1^2 + \omega_1^2 q_1^2), \quad F_2 = H_2 = \frac{1}{2}(p_2^2 + \omega_2^2 q_2^2)$$

由于 $\{H_1, H_2\} = 0$ 且独立，系统可积。

作用-角变量：
$$I_1 = \frac{H_1}{\omega_1}, \quad \theta_1 = \arctan\left(\frac{\omega_1 q_1}{p_1}\right)$$
$$I_2 = \frac{H_2}{\omega_2}, \quad \theta_2 = \arctan\left(\frac{\omega_2 q_2}{p_2}\right)$$

Hamilton函数：$H = \omega_1 I_1 + \omega_2 I_2$

运动：
$$I_1, I_2 = \text{常数}, \quad \theta_1(t) = \theta_1(0) + \omega_1 t, \quad \theta_2(t) = \theta_2(0) + \omega_2 t$$

当 $\omega_1/\omega_2$ 为有理数时轨道闭合，为无理数时轨道稠密充满环面。

---

### 问题2：球面摆的可积性

**问题**: 证明球面摆（质量为 $m$ 的粒子约束在球面上，在重力作用下运动）是可积的。

**解答**:

使用球坐标 $(\theta, \phi)$，其中 $\theta$ 是极角，$\phi$ 是方位角。

Lagrange量：
$$L = \frac{1}{2}ml^2(\dot{\theta}^2 + \sin^2\theta \, \dot{\phi}^2) - mgl(1 - \cos\theta)$$

守恒量：

1. **能量**（Hamilton函数）
$$H = \frac{1}{2ml^2}\left(p_\theta^2 + \frac{p_\phi^2}{\sin^2\theta}\right) + mgl(1 - \cos\theta)$$

2. **角动量的z分量**
$$p_\phi = ml^2\sin^2\theta \, \dot{\phi} = \text{常数}$$

由于自由度为2，且有两个独立的互相对合的守恒量，系统Liouville可积。

---

### 问题3：证明Kepler问题的Runge-Lenz向量

**问题**: Kepler问题中，证明Runge-Lenz向量 $A = p \times L - \mu \hat{r}$ 守恒，其中 $L = q \times p$，$\hat{r} = q/|q|$。

**解答**:

需要证明 $\{A, H\} = 0$，其中 $H = \frac{|p|^2}{2} - \frac{\mu}{|q|}$。

利用 $\{L_i, H\} = 0$（旋转对称性），计算：
$$\{A_i, H\} = \{(p \times L)_i, H\} - \mu\left\{\frac{q_i}{|q|}, H\right\}$$

第一项：$\{(p \times L)_i, H\} = \epsilon_{ijk}\{p_j L_k, H\} = \epsilon_{ijk} p_j \{L_k, H\} + \epsilon_{ijk} \{p_j, H\} L_k = \epsilon_{ijk}\{p_j, H\} L_k$

$$\{p_j, H\} = -\frac{\partial H}{\partial q_j} = -\frac{\mu q_j}{|q|^3}$$

第二项：$\left\{\frac{q_i}{|q|}, H\right\} = \sum_j \frac{\partial(q_i/|q|)}{\partial q_j}\frac{\partial H}{\partial p_j} = \sum_j \left(\frac{\delta_{ij}}{|q|} - \frac{q_i q_j}{|q|^3}\right)\frac{p_j}{m}$

经过详细计算，两项相消，得到 $\{A_i, H\} = 0$。$\square$

---

## 📚 相关文献

1. **Arnold, V.I.** (1989). *Mathematical Methods of Classical Mechanics*. Springer.
2. **Arnold, V.I., Kozlov, V.V., & Neishtadt, A.I.** (2006). *Mathematical Aspects of Classical and Celestial Mechanics*. Springer.
3. **Thirring, W.** (1992). *A Course in Mathematical Physics 1: Classical Dynamical Systems*. Springer.

---

**最后更新**: 2026年4月4日
