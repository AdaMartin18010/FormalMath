---
msc_primary: 81

  - 81Q10
  - 46C05
  - 47A70
  - 46N50
title: Hilbert空间与量子态
processed_at: '2026-04-05'
---
# Hilbert空间与量子态

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

量子力学的数学基础建立在Hilbert空间理论之上。与经典力学在相空间中描述系统不同，量子力学使用复Hilbert空间中的向量（波函数）来描述量子态。这一数学框架由von Neumann于1932年系统建立，是20世纪数学物理最重要的成就之一。

**核心思想**: 量子态是Hilbert空间中的射线，物理信息由内积给出。

---

## 📝 基础概念

### 1.1 Hilbert空间的数学定义

**定义 1.1** (内积空间)
复向量空间 $\mathcal{H}$ 上的**内积**是映射 $\langle\cdot, \cdot\rangle: \mathcal{H} \times \mathcal{H} \to \mathbb{C}$，满足：

1. **共轭对称性**: $\langle\phi, \psi\rangle = \overline{\langle\psi, \phi\rangle}$
2. **对第一个变量线性**: $\langle\alpha\phi_1 + \beta\phi_2, \psi\rangle = \alpha\langle\phi_1, \psi\rangle + \beta\langle\phi_2, \psi\rangle$
3. **正定性**: $\langle\psi, \psi\rangle \geq 0$，等号成立当且仅当 $\psi = 0$

**定义 1.2** (Hilbert空间)
**Hilbert空间**是完备的内积空间，即每个Cauchy序列都收敛。范数由内积诱导：$\|\psi\| = \sqrt{\langle\psi, \psi\rangle}$。

---

### 1.2 量子力学的标准Hilbert空间

**位置表象** ($L^2(\mathbb{R}^n)$):
单粒子波函数 $\psi(x)$ 属于 $L^2(\mathbb{R}^n)$：
$$\|\psi\|^2 = \int_{\mathbb{R}^n} |\psi(x)|^2 dx < \infty$$

内积定义为：$\langle\phi, \psi\rangle = \int_{\mathbb{R}^n} \overline{\phi(x)}\psi(x) dx$

**动量表象** ($L^2(\mathbb{R}^n)$):
通过Fourier变换与位置表象联系：
$$\tilde{\psi}(p) = \frac{1}{(2\pi\hbar)^{n/2}}\int_{\mathbb{R}^n} \psi(x)e^{-ip\cdot x/\hbar} dx$$

**离散谱情况** ($\ell^2$):
对于具有离散谱的系统（如谐振子）：
$$\ell^2 = \left\{(c_n)_{n=1}^\infty : \sum_{n=1}^\infty |c_n|^2 < \infty\right\}$$

---

### 1.3 Dirac符号体系

**定义 1.3** (Dirac符号)

- **右矢** (ket): $|\psi\rangle \in \mathcal{H}$
- **左矢** (bra): $\langle\phi| \in \mathcal{H}^*$，满足 $\langle\phi|(|\psi\rangle) = \langle\phi, \psi\rangle$
- **算子表示**: 线性算子 $A$ 作用为 $A|\psi\rangle$，或矩阵元 $\langle\phi|A|\psi\rangle$

**重要恒等式** (单位分解):
对于正交归一基 $\{|n\rangle\}_{n=1}^\infty$：
$$\sum_{n=1}^\infty |n\rangle\langle n| = I$$

任意态可展开为：$|\psi\rangle = \sum_n |n\rangle\langle n|\psi\rangle = \sum_n c_n |n\rangle$

---

## 🎯 核心定理

### 2.1 态的叠加原理

**公理** (叠加原理)
若 $|\psi_1\rangle$ 和 $|\psi_2\rangle$ 是可能的量子态，则它们的线性组合
$$|\psi\rangle = \alpha|\psi_1\rangle + \beta|\psi_2\rangle, \quad |\alpha|^2 + |\beta|^2 = 1$$

也是可能的量子态。

**物理诠释**: 这是量子力学区别于经典力学的本质特征，导致干涉现象。

---

### 2.2 Riesz表示定理

**定理 2.1** (Riesz表示定理)
设 $\mathcal{H}$ 是Hilbert空间，$f: \mathcal{H} \to \mathbb{C}$ 是有界线性泛函。则存在唯一的 $\phi \in \mathcal{H}$ 使得：
$$f(\psi) = \langle\phi, \psi\rangle, \quad \forall \psi \in \mathcal{H}$$
且 $\|f\| = \|\phi\|$。

**意义**: 建立了 $\mathcal{H}^*$ 与 $\mathcal{H}$ 之间的反线性同构，是Dirac bra-ket符号的数学基础。

---

### 2.3 完备性关系

**定理 2.2** (完备性关系)
设 $\{|e_n\rangle\}_{n=1}^\infty$ 是Hilbert空间 $\mathcal{H}$ 的正交归一基。则：

1. 对任意 $|\psi\rangle \in \mathcal{H}$：
$$|\psi\rangle = \sum_{n=1}^\infty \langle e_n|\psi\rangle |e_n\rangle$$

2. 完备性关系：
$$\sum_{n=1}^\infty |e_n\rangle\langle e_n| = I$$

3. Parseval恒等式：
$$\|\psi\|^2 = \sum_{n=1}^\infty |\langle e_n|\psi\rangle|^2$$

---

### 2.4 纯态与混合态

**定义 2.1** (纯态)
**纯态**由Hilbert空间中的射线（一维子空间）表示，对应投影算子 $P_\psi = |\psi\rangle\langle\psi|$，满足 $P_\psi^2 = P_\psi$、$P_\psi^\dagger = P_\psi$、$\text{Tr}(P_\psi) = 1$。

**定义 2.2** (密度算子与混合态)
**密度算子**（或统计算子）是正定的、迹为1的算子 $\rho: \mathcal{H} \to \mathcal{H}$：
$$\rho \geq 0, \quad \text{Tr}(\rho) = 1$$
若 $\rho^2 = \rho$，则为纯态；否则为**混合态**（统计系综）。

**定义 2.3** (系综解释)
混合态描述统计系综：以概率 $p_i$ 处于态 $|\psi_i\rangle$ 的系统，其密度算子为：
$$\rho = \sum_i p_i |\psi_i\rangle\langle\psi_i|$$

---

## 💡 实战问题

### 问题1：自旋1/2系统

**问题**: 描述自旋1/2粒子的Hilbert空间，并表示自旋向上和向下态。

**解答**:

自旋1/2系统的Hilbert空间是 $\mathbb{C}^2$。标准正交基：
$$|\uparrow\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \quad |\downarrow\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix}$$

任意态可表示为：
$$|\psi\rangle = \alpha|\uparrow\rangle + \beta|\downarrow\rangle = \begin{pmatrix} \alpha \\ \beta \end{pmatrix}$$

归一化条件：$|\alpha|^2 + |\beta|^2 = 1$。

Pauli矩阵作为自旋算子：
$$\sigma_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \quad \sigma_y = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}, \quad \sigma_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$

---

### 问题2：谐振子的Fock空间

**问题**: 一维量子谐振子的Hilbert空间是什么？写出能量本征态的显式形式。

**解答**:

Hilbert空间是 $L^2(\mathbb{R})$。

能量本征态（Hermite函数）：
$$\psi_n(x) = \frac{1}{\sqrt{2^n n!}}\left(\frac{m\omega}{\pi\hbar}\right)^{1/4} H_n\left(\sqrt{\frac{m\omega}{\hbar}}x\right) e^{-\frac{m\omega}{2\hbar}x^2}$$

其中 $H_n$ 是Hermite多项式。

能量本征值：$E_n = \hbar\omega(n + \frac{1}{2})$

升降算子表示：
$$|n\rangle = \frac{(a^\dagger)^n}{\sqrt{n!}}|0\rangle$$

其中 $a^\dagger|n\rangle = \sqrt{n+1}|n+1\rangle$，$a|n\rangle = \sqrt{n}|n-1\rangle$。

---

### 问题3：态的分解

**问题**: 设 $|\psi\rangle = \frac{1}{\sqrt{3}}|0\rangle + \sqrt{\frac{2}{3}}|1\rangle$，其中 $|0\rangle, |1\rangle$ 是正交归一基。计算测量得到 $|0\rangle$ 和 $|1\rangle$ 的概率。

**解答**:

概率由Born规则给出：

测量得到 $|0\rangle$ 的概率：
$$P(0) = |\langle 0|\psi\rangle|^2 = \left|\frac{1}{\sqrt{3}}\right|^2 = \frac{1}{3}$$

测量得到 $|1\rangle$ 的概率：
$$P(1) = |\langle 1|\psi\rangle|^2 = \left|\sqrt{\frac{2}{3}}\right|^2 = \frac{2}{3}$$

验证：$P(0) + P(1) = 1$。$\square$

---

## 📚 相关文献

1. **von Neumann, J.** (1955). *Mathematical Foundations of Quantum Mechanics*. Princeton.
2. **Reed, M., & Simon, B.** (1972). *Methods of Modern Mathematical Physics, Vol. 1: Functional Analysis*. Academic Press.
3. **Hall, B.C.** (2013). *Quantum Theory for Mathematicians*. Springer.

---

**最后更新**: 2026年4月4日
