---
msc_primary: 81Q05
msc_secondary:
- 47D06
- 47N50
- 35Q41
title: 量子动力学与Schrödinger方程
processed_at: '2026-04-05'
---
# 量子动力学与Schrödinger方程

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

量子动力学描述量子态随时间的演化。与经典力学的确定性演化不同，量子演化由Schrödinger方程描述，是幺正演化。Stone定理建立了自伴Hamilton算子与单参数幺正群之间的一一对应，为量子动力学提供了严格的数学基础。

**核心思想**: 孤立量子系统的演化是幺正的，由Hamilton算子生成。

---

## 📝 基础概念

### 1.1 Schrödinger方程

**定义 1.1** (Schrödinger方程)
量子态的时间演化由**Schrödinger方程**描述：
$$i\hbar\frac{d}{dt}|\psi(t)\rangle = \hat{H}|\psi(t)\rangle$$

其中 $\hat{H}$ 是系统的Hamilton算子（能量可观测量）。

**初始值问题**: 给定 $|\psi(0)\rangle = |\psi_0\rangle$，求 $|\psi(t)\rangle$ 对所有 $t \in \mathbb{R}$。

**时间无关Schrödinger方程**:
当Hamilton量不显含时间时，分离变量 $|\psi(t)\rangle = e^{-iEt/\hbar}|\psi_E\rangle$ 得：
$$\hat{H}|\psi_E\rangle = E|\psi_E\rangle$$

---

### 1.2 酉算子与酉群

**定义 1.2** (酉算子)
算子 $U: \mathcal{H} \to \mathcal{H}$ 是**酉**的，若 $U^\dagger U = UU^\dagger = I$。酉算子保持内积和范数不变：
$$\langle U\phi, U\psi\rangle = \langle\phi, \psi\rangle$$

**定义 1.3** (单参数酉群)
**单参数酉群**是酉算子的单参数族 $\{U(t)\}_{t \in \mathbb{R}}$ 满足：
- $U(t+s) = U(t)U(s)$（群性质）
- $U(0) = I$
- $t \mapsto U(t)\psi$ 对每个 $\psi$ 连续（强连续性）

---

### 1.3 不同绘景

**Schrödinger绘景**: 态随时间演化，可观测量固定
$$|\psi(t)\rangle = U(t)|\psi(0)\rangle, \quad A(t) = A$$

**Heisenberg绘景**: 态固定，可观测量随时间演化
$$|\psi\rangle_H = |\psi(0)\rangle, \quad A_H(t) = U^\dagger(t)AU(t)$$

**相互作用绘景**: 分解Hamilton量 $\hat{H} = \hat{H}_0 + \hat{V}$，两者都演化

---

## 🎯 核心定理

### 2.1 Stone定理

**定理 2.1** (Stone定理)
设 $\{U(t)\}_{t \in \mathbb{R}}$ 是强连续的单参数酉群。则存在唯一的自伴算子 $A$ 使得：
$$U(t) = e^{-itA/\hbar}$$

反之，每个自伴算子生成一个强连续的单参数酉群。

算子 $A$ 称为酉群的**无穷小生成元**，满足：
$$A\psi = i\hbar\lim_{t \to 0}\frac{U(t)\psi - \psi}{t}$$

**证明概要**:

1. 定义生成元 $A$ 在适当的定义域上
2. 证明 $A$ 是对称且稠定的
3. 证明 $A$ 是本质自伴的
4. 验证 $U(t) = e^{-itA/\hbar}$$\square$

**量子动力学**: 对Hamilton算子 $\hat{H}$，时间演化算子为：
$$U(t) = e^{-i\hat{H}t/\hbar}$$
Schrödinger方程的形式解为：$|\psi(t)\rangle = U(t)|\psi(0)\rangle$。

---

### 2.2 Heisenberg方程

**定理 2.2** (Heisenberg方程)
在Heisenberg绘景中，可观测量满足：
$$\frac{d}{dt}A_H(t) = \frac{i}{\hbar}[\hat{H}, A_H(t)]$$

**证明**:
$$\frac{d}{dt}A_H(t) = \frac{d}{dt}(U^\dagger(t)AU(t)) = \frac{i}{\hbar}(\hat{H}U^\dagger AU - U^\dagger AU\hat{H}) = \frac{i}{\hbar}[\hat{H}, A_H]$$
$\square$

**等价性**: Schrödinger绘景与Heisenberg绘景给出相同的测量结果：
$$\langle\psi(t)|A|\psi(t)\rangle = \langle\psi(0)|A_H(t)|\psi(0)\rangle$$

---

### 2.3 Ehrenfest定理

**定理 2.3** (Ehrenfest定理)
算子期望值的演化满足：
$$\frac{d}{dt}\langle A\rangle = \frac{i}{\hbar}\langle[\hat{H}, A]\rangle + \left\langle\frac{\partial A}{\partial t}\right\rangle$$

对于位置算子 $\hat{x}$ 和动量算子 $\hat{p}$：
$$\frac{d}{dt}\langle\hat{x}\rangle = \frac{\langle\hat{p}\rangle}{m}, \quad \frac{d}{dt}\langle\hat{p}\rangle = -\left\langle\frac{\partial V}{\partial x}\right\rangle$$

**意义**: 期望值满足经典运动方程，但量子修正是必要的。

---

## 💡 实战问题

### 问题1：自由粒子的演化

**问题**: 自由粒子（$V = 0$）的初态为 $\psi(x, 0) = (\frac{\alpha}{\pi})^{1/4}e^{-\alpha x^2/2}$，求 $\psi(x, t)$。

**解答**:

自由粒子Hamilton量：$\hat{H} = \frac{\hat{p}^2}{2m}$

在动量表象：$\tilde{\psi}(p, t) = e^{-ip^2t/(2m\hbar)}\tilde{\psi}(p, 0)$

初态的Fourier变换：
$$\tilde{\psi}(p, 0) = (\pi\hbar^2\alpha)^{-1/4}e^{-p^2/(2\hbar^2\alpha)}$$

时间演化：
$$\tilde{\psi}(p, t) = (\pi\hbar^2\alpha)^{-1/4}\exp\left(-\frac{p^2}{2\hbar^2\alpha} - \frac{ip^2t}{2m\hbar}\right)$$

反Fourier变换回位置表象：
$$\psi(x, t) = \left(\frac{\alpha}{\pi}\right)^{1/4}\frac{1}{\sqrt{1 + i\frac{\hbar\alpha t}{m}}}\exp\left(-\frac{\alpha x^2}{2(1 + i\frac{\hbar\alpha t}{m})}\right)$$

波包随时间展宽。

---

### 问题2：自旋进动

**问题**: 自旋1/2粒子在恒定磁场 $B$ 中，Hamilton量 $\hat{H} = -\gamma B \cdot \hat{S}$。设初始态 $|\psi(0)\rangle = |\uparrow_z\rangle$，求 $|\psi(t)\rangle$。

**解答**:

设磁场沿z方向：$\hat{H} = -\gamma B S_z = -\frac{\gamma\hbar B}{2}\sigma_z$

时间演化算子：
$$U(t) = e^{-i\hat{H}t/\hbar} = e^{i\omega t \sigma_z/2} = \cos\left(\frac{\omega t}{2}\right)I + i\sin\left(\frac{\omega t}{2}\right)\sigma_z$$

其中 $\omega = \gamma B$。

演化态：
$$|\psi(t)\rangle = U(t)|\uparrow_z\rangle = e^{i\omega t/2}|\uparrow_z\rangle$$

在x方向的自旋期望：
$$\langle S_x\rangle = \frac{\hbar}{2}\cos(\omega t)$$

自旋以频率 $\omega$ 绕z轴进动。

---

### 问题3：谐振子的相干态

**问题**: 谐振子的相干态定义为 $|\alpha\rangle = e^{-|\alpha|^2/2}\sum_{n=0}^\infty \frac{\alpha^n}{\sqrt{n!}}|n\rangle$。证明这是最小不确定态，并求其时间演化。

**解答**:

**最小不确定性**: 相干态满足 $a|\alpha\rangle = \alpha|\alpha\rangle$，其中 $a$ 是湮灭算子。

$$\langle\alpha|\hat{x}|\alpha\rangle = \sqrt{\frac{2\hbar}{m\omega}}\text{Re}(\alpha), \quad \langle\alpha|\hat{p}|\alpha\rangle = \sqrt{2m\hbar\omega}\text{Im}(\alpha)$$

$$\Delta x = \sqrt{\frac{\hbar}{2m\omega}}, \quad \Delta p = \sqrt{\frac{m\hbar\omega}{2}}, \quad \Delta x \cdot \Delta p = \frac{\hbar}{2}$$

达到不确定性原理的下限。

**时间演化**:
$$|\alpha(t)\rangle = e^{-i\hat{H}t/\hbar}|\alpha\rangle = e^{-i\omega t/2}|\alpha e^{-i\omega t}\rangle$$

相干态保持相干态，参数 $\alpha$ 以频率 $\omega$ 在复平面旋转。

---

## 📚 相关文献

1. **Reed, M., & Simon, B.** (1972-1978). *Methods of Modern Mathematical Physics* (Vols. 1-4). Academic Press.
2. **Hall, B.C.** (2013). *Quantum Theory for Mathematicians*. Springer.
3. **Takhtajan, L.A.** (2008). *Quantum Mechanics for Mathematicians*. AMS.

---

**最后更新**: 2026年4月4日
