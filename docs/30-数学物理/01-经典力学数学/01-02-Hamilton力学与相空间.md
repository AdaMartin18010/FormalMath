---
msc_primary: "70H05"
msc_secondary: ['70H15', '37J05', '53D05']
---

# Hamilton力学与相空间

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

Hamilton力学是经典力学的另一种等价表述，通过Legendre变换将Lagrange力学从切丛 $TQ$ 转换到余切丛 $T^*Q$（相空间）。这一表述揭示了几何结构的丰富性，为量子力学、统计力学和辛几何奠定了基础。

**核心思想**: 相空间是力学系统的自然几何载体，Hamilton流保持辛结构不变。

---

## 📝 基础概念

### 1.1 Legendre变换

**定义 1.1** (Legendre变换)
**Legendre变换**是映射 $\mathbb{F}L: TQ \to T^*Q$，定义为：
$$\mathbb{F}L(q, \dot{q}) = \left(q, \frac{\partial L}{\partial \dot{q}}\right) = (q, p)$$

**定义 1.2** (超正则Lagrange量)
Lagrange量 $L$ 称为**超正则**的，若 $\mathbb{F}L$ 是全局微分同胚。

**定理 1.1** (Legendre变换的等价性)
若Lagrange量 $L$ 是超正则的，则Lagrange力学与Hamilton力学等价。

---

### 1.2 Hamilton函数与方程

**定义 1.3** (Hamilton函数)
**Hamilton函数** $H: T^*Q \times \mathbb{R} \to \mathbb{R}$ 通过Legendre变换定义：
$$H(q, p, t) = p_i \dot{q}^i - L(q, \dot{q}, t)$$
其中 $\dot{q}$ 通过 $p = \partial L / \partial \dot{q}$ 表示为 $(q, p)$ 的函数。

**定义 1.4** (Hamilton方程)
**Hamilton方程**为：
$$\dot{q}^i = \frac{\partial H}{\partial p_i}, \quad \dot{p}_i = -\frac{\partial H}{\partial q^i}$$

**矩阵形式**: 设 $z = (q^1, \ldots, q^n, p_1, \ldots, p_n)^T$，$J = \begin{pmatrix} 0 & I_n \\ -I_n & 0 \end{pmatrix}$，则：
$$\dot{z} = J \nabla H$$

---

### 1.3 相空间

**定义 1.5** (相空间)
**相空间**是构型空间的余切丛 $T^*Q$。它是描述力学系统状态的 $2n$ 维流形，装备有自然的辛结构。

**Liouville 1-形式**:
$$\theta = p_i dq^i$$

**标准辛形式**:
$$\omega = -d\theta = dq^i \wedge dp_i$$

---

## 🎯 核心定理

### 2.1 Hamilton方程的导出

**定理 2.1** (Hamilton原理的相空间形式)
作用量的相空间形式为：
$$S[q, p] = \int_{t_1}^{t_2} (p_i \dot{q}^i - H(q, p, t)) \, dt$$

对 $q$ 和 $p$ 独立变分，得到Hamilton方程。

**证明**:
变分 $\delta S = \int_{t_1}^{t_2} (\delta p_i \dot{q}^i + p_i \delta\dot{q}^i - \frac{\partial H}{\partial q^i}\delta q^i - \frac{\partial H}{\partial p_i}\delta p_i) dt$

对第二项分部积分：
$$= \int_{t_1}^{t_2} \left[\left(\dot{q}^i - \frac{\partial H}{\partial p_i}\right)\delta p_i + \left(-\dot{p}_i - \frac{\partial H}{\partial q^i}\right)\delta q^i\right] dt$$

由变分的任意性，得到Hamilton方程。$\square$

---

### 2.2 正则变换

**定义 2.1** (正则变换)
微分同胚 $\varphi: T^*Q \to T^*Q$ 称为**正则变换**（或辛变换），若保持辛形式：
$$\varphi^*\omega = \omega$$

**定理 2.2** (正则变换保持Hamilton方程)
若 $\varphi$ 是正则变换，则在新坐标下Hamilton方程形式不变。

**生成函数**:

正则变换可由以下四种生成函数生成：

| 类型 | 生成函数 | 变换公式 |
|------|----------|----------|
| $F_1$ | $F_1(q, Q)$ | $p = \frac{\partial F_1}{\partial q}$，$P = -\frac{\partial F_1}{\partial Q}$ |
| $F_2$ | $F_2(q, P)$ | $p = \frac{\partial F_2}{\partial q}$，$Q = \frac{\partial F_2}{\partial P}$ |
| $F_3$ | $F_3(p, Q)$ | $q = -\frac{\partial F_3}{\partial p}$，$P = -\frac{\partial F_3}{\partial Q}$ |
| $F_4$ | $F_4(p, P)$ | $q = -\frac{\partial F_4}{\partial p}$，$Q = \frac{\partial F_4}{\partial P}$ |

---

### 2.3 Hamilton-Jacobi理论

**定义 2.2** (Hamilton-Jacobi方程)
**Hamilton-Jacobi方程**为：
$$\frac{\partial S}{\partial t} + H\left(q, \frac{\partial S}{\partial q}, t\right) = 0$$

其中 $S(q, t)$ 称为**主函数**。

**定理 2.3** (Hamilton-Jacobi方法)
若找到Hamilton-Jacobi方程的完全解 $S(q, \alpha, t)$（含 $n$ 个独立常数 $\alpha$），则通过：
$$p = \frac{\partial S}{\partial q}, \quad \beta = \frac{\partial S}{\partial \alpha}$$
可得到Hamilton方程的解。

---

## 💡 实战问题

### 问题1：谐振子的Hamilton描述

**问题**: 将一维谐振子 $L = \frac{1}{2}m\dot{q}^2 - \frac{1}{2}kq^2$ 转换到Hamilton形式并求解。

**解答**:

广义动量：
$$p = \frac{\partial L}{\partial \dot{q}} = m\dot{q} \Rightarrow \dot{q} = \frac{p}{m}$$

Hamilton函数：
$$H = p\dot{q} - L = \frac{p^2}{2m} + \frac{1}{2}kq^2$$

Hamilton方程：
$$\dot{q} = \frac{\partial H}{\partial p} = \frac{p}{m}, \quad \dot{p} = -\frac{\partial H}{\partial q} = -kq$$

合并得：
$$\ddot{q} = \frac{\dot{p}}{m} = -\frac{k}{m}q = -\omega^2 q$$

与Lagrange形式一致。

---

### 问题2：球坐标系中的中心力场

**问题**: 用球坐标 $(r, \theta, \phi)$ 建立中心力场 $V(r)$ 的Hamilton函数。

**解答**:

球坐标系中动能：
$$T = \frac{1}{2}m(\dot{r}^2 + r^2\dot{\theta}^2 + r^2\sin^2\theta \, \dot{\phi}^2)$$

广义动量：
$$p_r = m\dot{r}, \quad p_\theta = mr^2\dot{\theta}, \quad p_\phi = mr^2\sin^2\theta \, \dot{\phi}$$

Hamilton函数：
$$H = \frac{1}{2m}\left(p_r^2 + \frac{p_\theta^2}{r^2} + \frac{p_\phi^2}{r^2\sin^2\theta}\right) + V(r)$$

注意到 $p_\phi$ 是守恒量（角动量的z分量）。

---

### 问题3：生成函数应用

**问题**: 用生成函数 $F_2(q, P) = qP$ 找出对应的正则变换。

**解答**:

由 $F_2$ 型生成函数的变换公式：
$$p = \frac{\partial F_2}{\partial q} = P, \quad Q = \frac{\partial F_2}{\partial P} = q$$

这是恒等变换 $(q, p) \mapsto (Q, P) = (q, p)$。

**问题**: 用生成函数 $F_1(q, Q) = qQ$ 找出对应的正则变换。

**解答**:

由 $F_1$ 型生成函数的变换公式：
$$p = \frac{\partial F_1}{\partial q} = Q, \quad P = -\frac{\partial F_1}{\partial Q} = -q$$

所以变换为：
$$Q = p, \quad P = -q$$

这是 $(q, p) \mapsto (p, -q)$，是正则无变换（交换坐标和动量，并取负）。

---

## 📚 相关文献

1. **Arnold, V.I.** (1989). *Mathematical Methods of Classical Mechanics*. Springer.
2. **Goldstein, H., et al.** (2002). *Classical Mechanics* (3rd ed.). Addison-Wesley.
3. **Lanczos, C.** (1970). *The Variational Principles of Mechanics* (4th ed.). Dover.

---

**最后更新**: 2026年4月4日
