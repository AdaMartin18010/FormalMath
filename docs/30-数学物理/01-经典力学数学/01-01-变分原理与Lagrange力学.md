---
msc_primary: "70H03"
msc_secondary: ['49S05', '58E30', '37J05']
---

# 变分原理与Lagrange力学

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

变分原理是经典力学最深刻的表述形式之一。与Newton的向量力学不同，Lagrange力学通过作用量的极值原理描述系统的运动规律。这一方法不仅适用于质点力学，还可自然推广到场论和连续介质力学，成为现代理论物理的统一语言。

**核心思想**: 自然界选择使作用量取驻定值的路径。

---

## 📝 基础概念

### 1.1 构型空间与切丛

**定义 1.1** (构型空间)
一个力学系统的**构型空间**是光滑流形 $Q$，其点表示系统的所有可能位形。若系统有 $n$ 个自由度，则 $\dim Q = n$。

**定义 1.2** (切丛)
构型空间 $Q$ 的**切丛** $TQ$ 是所有切空间的并：
$$TQ = \bigcup_{q \in Q} T_q Q$$
其元素为 $(q, v)$，其中 $q \in Q$，$v \in T_q Q$。$TQ$ 是 $2n$ 维光滑流形。

---

### 1.2 Lagrange函数与作用量

**定义 1.3** (Lagrange函数)
**Lagrange函数**（或Lagrange量）是光滑映射 $L: TQ \times \mathbb{R} \to \mathbb{R}$，通常形式为：
$$L(q, \dot{q}, t) = T(q, \dot{q}) - V(q, t)$$
其中 $T$ 是动能，$V$ 是势能。

**定义 1.4** (作用量泛函)
给定曲线 $q: [t_1, t_2] \to Q$，**作用量**定义为：
$$S[q] = \int_{t_1}^{t_2} L(q(t), \dot{q}(t), t) \, dt$$
这是路径空间上的泛函。

---

## 🎯 核心定理

### 2.1 Hamilton原理

**定理 2.1** (Hamilton原理 / Euler-Lagrange方程)
设 $L$ 是正则Lagrange量（Hessian矩阵 $\partial^2 L / \partial \dot{q}^i \partial \dot{q}^j$ 非退化）。曲线 $q(t)$ 使作用量 $S$ 取驻定值当且仅当满足**Euler-Lagrange方程**：
$$\frac{d}{dt}\left(\frac{\partial L}{\partial \dot{q}^i}\right) - \frac{\partial L}{\partial q^i} = 0, \quad i = 1, \ldots, n$$

**证明概要**:

考虑变分 $q_\epsilon(t) = q(t) + \epsilon \eta(t)$，其中 $\eta(t_1) = \eta(t_2) = 0$。

$$\frac{d}{d\epsilon}S[q_\epsilon]\big|_{\epsilon=0} = \int_{t_1}^{t_2} \left(\frac{\partial L}{\partial q^i}\eta^i + \frac{\partial L}{\partial \dot{q}^i}\dot{\eta}^i\right) dt$$

对第二项分部积分：
$$= \int_{t_1}^{t_2} \left(\frac{\partial L}{\partial q^i} - \frac{d}{dt}\frac{\partial L}{\partial \dot{q}^i}\right)\eta^i \, dt$$

由变分 $\eta$ 的任意性，得到Euler-Lagrange方程。$\square$

---

### 2.2 广义动量与能量守恒

**定义 2.1** (广义动量)
**广义动量**（共轭动量）定义为：
$$p_i = \frac{\partial L}{\partial \dot{q}^i}$$

**定理 2.2** (能量守恒)
若Lagrange量不显含时间（$\partial L/\partial t = 0$），则能量函数
$$E = \dot{q}^i \frac{\partial L}{\partial \dot{q}^i} - L = \dot{q}^i p_i - L$$
沿运动轨迹守恒。

**证明**:
$$\frac{dE}{dt} = \ddot{q}^i p_i + \dot{q}^i \dot{p}_i - \frac{\partial L}{\partial q^i}\dot{q}^i - \frac{\partial L}{\partial \dot{q}^i}\ddot{q}^i - \frac{\partial L}{\partial t}$$

利用 $\dot{p}_i = \partial L/\partial q^i$ 和 $\partial L/\partial t = 0$：
$$= \ddot{q}^i p_i + \dot{q}^i \frac{\partial L}{\partial q^i} - \frac{\partial L}{\partial q^i}\dot{q}^i - p_i \ddot{q}^i = 0$$
$\square$

---

### 2.3 Noether定理

**定理 2.3** (Noether定理)
若Lagrange量在单参数变换群 $q^i \mapsto q^i_\epsilon$ 下不变，则对应的**Noether荷**守恒：
$$Q = \frac{\partial L}{\partial \dot{q}^i} \frac{\partial q^i_\epsilon}{\partial \epsilon}\bigg|_{\epsilon=0}$$

**应用示例**:

| 对称性 | 守恒量 |
|--------|--------|
| 时间平移 | 能量 $E$ |
| 空间平移 | 动量 $p$ |
| 空间旋转 | 角动量 $L$ |

---

## 💡 实战问题

### 问题1：谐振子的Lagrange描述

**问题**: 建立一维谐振子 $L = \frac{1}{2}m\dot{q}^2 - \frac{1}{2}kq^2$ 的运动方程，并求解。

**解答**:

Euler-Lagrange方程给出：
$$\frac{d}{dt}(m\dot{q}) - (-kq) = 0 \Rightarrow m\ddot{q} + kq = 0$$

设 $\omega = \sqrt{k/m}$，通解为：
$$q(t) = A\cos(\omega t) + B\sin(\omega t)$$

或由初始条件 $q(0) = q_0$，$\dot{q}(0) = v_0$：
$$q(t) = q_0\cos(\omega t) + \frac{v_0}{\omega}\sin(\omega t)$$

---

### 问题2：中心力场中的运动

**问题**: 质量为 $m$ 的粒子在中心势 $V(r)$ 中运动，用极坐标建立Lagrange方程。

**解答**:

极坐标 $(r, \theta)$ 下，动能 $T = \frac{1}{2}m(\dot{r}^2 + r^2\dot{\theta}^2)$。

Lagrange量：
$$L = \frac{1}{2}m(\dot{r}^2 + r^2\dot{\theta}^2) - V(r)$$

Euler-Lagrange方程：

1. 径向方程：
$$m\ddot{r} - mr\dot{\theta}^2 + \frac{dV}{dr} = 0$$

2. 角向方程（角动量守恒）：
$$\frac{d}{dt}(mr^2\dot{\theta}) = 0 \Rightarrow mr^2\dot{\theta} = \text{常数} = L$$

---

### 问题3：双摆系统

**问题**: 建立双摆系统的Lagrange量并推导运动方程。

**解答**:

设两摆长均为 $l$，质量均为 $m$，角度分别为 $\theta_1, \theta_2$。

位置坐标：
- 第一摆：$x_1 = l\sin\theta_1$，$y_1 = -l\cos\theta_1$
- 第二摆：$x_2 = l(\sin\theta_1 + \sin\theta_2)$，$y_2 = -l(\cos\theta_1 + \cos\theta_2)$

速度：
- $\dot{x}_1 = l\dot{\theta}_1\cos\theta_1$，$\dot{y}_1 = l\dot{\theta}_1\sin\theta_1$
- $\dot{x}_2 = l(\dot{\theta}_1\cos\theta_1 + \dot{\theta}_2\cos\theta_2)$
- $\dot{y}_2 = l(\dot{\theta}_1\sin\theta_1 + \dot{\theta}_2\sin\theta_2)$

动能：
$$T = \frac{1}{2}ml^2[2\dot{\theta}_1^2 + \dot{\theta}_2^2 + 2\dot{\theta}_1\dot{\theta}_2\cos(\theta_1 - \theta_2)]$$

势能：
$$V = -mgl(2\cos\theta_1 + \cos\theta_2)$$

Lagrange量 $L = T - V$，应用Euler-Lagrange方程得到耦合非线性微分方程组。

---

## 📚 相关文献

1. **Arnold, V.I.** (1989). *Mathematical Methods of Classical Mechanics*. Springer.
2. **Goldstein, H., et al.** (2002). *Classical Mechanics* (3rd ed.). Addison-Wesley.
3. **José, J.V., & Saletan, E.J.** (1998). *Classical Dynamics: A Contemporary Approach*. Cambridge.

---

**最后更新**: 2026年4月4日
