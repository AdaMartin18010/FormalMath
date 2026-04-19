---
title: "README"
msc_primary: "00"
---

# 数学物理方法：从经典力学到量子场论

## 1. 引言

数学物理（Mathematical Physics）是应用数学与理论物理的交叉领域，其核心任务在于为物理理论提供严格的数学基础，并借助物理直觉发现新的数学结构。从Newton力学中的常微分方程到广义相对论中的微分几何，从量子力学的泛函分析到统计力学的概率论，数学物理始终是推动数学与物理双向发展的核心动力。

本文聚焦于数学物理中的三大支柱——**变分法与Euler-Lagrange方程**、**Hilbert空间中的量子力学表述**以及**Fourier分析与波动方程**，通过严格定义与完整证明，展示数学工具如何精确刻画物理定律。

---

## 2. 严格数学定义

### 2.1 变分法与泛函导数

**定义 2.1（泛函）**
设 $X$ 为函数空间（如 $C^1[a,b]$）。映射 $J: X \to \mathbb{R}$ 称为**泛函**。若存在线性映射 $\delta J[y; \eta]$ 使得
$$J[y + \varepsilon \eta] = J[y] + \varepsilon \delta J[y; \eta] + o(\varepsilon), \quad \varepsilon \to 0$$
则称 $\delta J$ 为 $J$ 在 $y$ 处沿方向 $\eta$ 的**一阶变分**。

**定义 2.2（Euler-Lagrange方程）**
设 Lagrangian $L(t, q, \dot{q})$ 为 $C^2$ 函数。泛函
$$S[q] = \int_{t_0}^{t_1} L(t, q(t), \dot{q}(t)) \, dt$$
的临界点满足**Euler-Lagrange方程**：
$$\frac{\partial L}{\partial q^i} - \frac{d}{dt}\frac{\partial L}{\partial \dot{q}^i} = 0, \quad i = 1, \ldots, n$$

### 2.2 量子力学的Hilbert空间表述

**定义 2.3（量子态与可观测量）**
量子系统的**纯态**由复Hilbert空间 $\mathcal{H}$ 中的单位向量 $|\psi\rangle$（模为1，且相差一个相位因子视为等价）描述。**可观测量**对应 $\mathcal{H}$ 上的自伴算子 $A = A^\dagger$。

**定义 2.4（期望值与不确定性）**
可观测量 $A$ 在态 $|\psi\rangle$ 下的**期望值**为
$$\langle A \rangle_\psi = \langle \psi | A | \psi \rangle$$
**方差**为
$$(\Delta A)_\psi^2 = \langle (A - \langle A \rangle)^2 \rangle_\psi = \langle A^2 \rangle_\psi - \langle A \rangle_\psi^2$$

### 2.3 Fourier变换

**定义 2.5（$L^1$ Fourier变换）**
对 $f \in L^1(\mathbb{R}^n)$，其**Fourier变换**定义为
$$\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i x \cdot \xi} \, dx$$
**逆变换**为
$$f(x) = \int_{\mathbb{R}^n} \hat{f}(\xi) e^{2\pi i x \cdot \xi} \, d\xi$$
（在适当条件下成立）

---

## 3. 核心定理与证明

### 定理 3.1（Euler-Lagrange方程的推导）

设 $q \in C^2[t_0, t_1]$ 使 $S[q]$ 取极值，且满足固定端点条件 $q(t_0) = q_0$，$q(t_1) = q_1$。则 $q$ 满足Euler-Lagrange方程。

**证明**：取任意 $C^2$ 变分 $\eta$ 满足 $\eta(t_0) = \eta(t_1) = 0$。定义 $\Phi(\varepsilon) = S[q + \varepsilon \eta]$。由极值条件，$\Phi'(0) = 0$。

计算：
$$\Phi'(\varepsilon) = \int_{t_0}^{t_1} \left[\frac{\partial L}{\partial q^i} \eta^i + \frac{\partial L}{\partial \dot{q}^i} \dot{\eta}^i\right] dt$$

对第二项分部积分：
$$\int_{t_0}^{t_1} \frac{\partial L}{\partial \dot{q}^i} \dot{\eta}^i \, dt = \left[\frac{\partial L}{\partial \dot{q}^i} \eta^i\right]_{t_0}^{t_1} - \int_{t_0}^{t_1} \frac{d}{dt}\frac{\partial L}{\partial \dot{q}^i} \cdot \eta^i \, dt$$

边界项消失（$\eta$ 在端点为零），故
$$\Phi'(0) = \int_{t_0}^{t_1} \left[\frac{\partial L}{\partial q^i} - \frac{d}{dt}\frac{\partial L}{\partial \dot{q}^i}\right] \eta^i \, dt = 0$$

由变分法基本引理（$\eta$ 任意），被积函数必须为零。$\square$

### 定理 3.2（Heisenberg不确定性原理）

设 $A, B$ 为Hilbert空间 $\mathcal{H}$ 上的自伴算子，$|\psi\rangle \in D(AB) \cap D(BA)$。则
$$\Delta A \cdot \Delta B \geq \frac{1}{2} |\langle [A, B] \rangle_\psi|$$
其中 $[A, B] = AB - BA$ 为交换子。

**证明**：令 $\tilde{A} = A - \langle A \rangle_\psi I$，$\tilde{B} = B - \langle B \rangle_\psi I$。则 $[\tilde{A}, \tilde{B}] = [A, B]$，且 $(\Delta A)^2 = \langle \tilde{A}^2 \rangle$，$(\Delta B)^2 = \langle \tilde{B}^2 \rangle$。

对任意 $\lambda \in \mathbb{R}$，考虑
$$0 \leq \langle (\tilde{A} + i\lambda \tilde{B})\psi | (\tilde{A} + i\lambda \tilde{B})\psi \rangle = \langle \tilde{A}^2 \rangle + \lambda^2 \langle \tilde{B}^2 \rangle + i\lambda \langle [\tilde{A}, \tilde{B}] \rangle$$

（利用 $\tilde{A}, \tilde{B}$ 自伴，$\langle \tilde{A}\tilde{B} \rangle^* = \langle \tilde{B}\tilde{A} \rangle$）

令 $\alpha = \langle \tilde{A}^2 \rangle$，$\beta = \langle \tilde{B}^2 \rangle$，$\gamma = i\langle [A, B] \rangle$（注意 $[A,B]$ 反自伴，故 $\gamma \in \mathbb{R}$）。则对所有 $\lambda$：
$$\alpha + \lambda^2 \beta + \lambda \gamma \geq 0$$

作为 $\lambda$ 的二次函数恒非负，判别式 $\gamma^2 - 4\alpha\beta \leq 0$，即
$$\alpha\beta \geq \frac{\gamma^2}{4} = \frac{|\langle [A, B] \rangle|^2}{4}$$
开方即得结论。$\square$

### 定理 3.3（Fourier变换的Plancherel定理）

Fourier变换可延拓为 $L^2(\mathbb{R}^n) \to L^2(\mathbb{R}^n)$ 的酉算子，且
$$\|\hat{f}\|_{L^2} = \|f\|_{L^2}$$

**证明概要**：先对 Schwartz 空间 $\mathcal{S}(\mathbb{R}^n)$ 证明。对 $f, g \in \mathcal{S}$，定义 $h = \overline{\hat{g}}$，则 $\hat{h} = \overline{g}$（适当归一化下）。由Fourier逆定理：
$$\int f \overline{g} = \int f \hat{h} = \int \hat{f} h = \int \hat{f} \overline{\hat{g}}$$
取 $f = g$ 得 $\|f\|_2 = \|\hat{f}\|_2$。由于 $\mathcal{S}$ 在 $L^2$ 中稠密，Fourier变换唯一延拓为酉算子。$\square$

---

## 4. 详细例子

### 例 4.1：谐振子的Euler-Lagrange方程与运动

经典谐振子的Lagrangian为
$$L(t, x, \dot{x}) = \frac{1}{2}m\dot{x}^2 - \frac{1}{2}kx^2$$

Euler-Lagrange方程：
$$\frac{\partial L}{\partial x} = -kx, \quad \frac{\partial L}{\partial \dot{x}} = m\dot{x}$$
$$-kx - \frac{d}{dt}(m\dot{x}) = -kx - m\ddot{x} = 0$$
即 $\ddot{x} + \omega^2 x = 0$，其中 $\omega = \sqrt{k/m}$。

通解：$x(t) = A\cos(\omega t) + B\sin(\omega t)$。给定初值 $x(0) = x_0$，$\dot{x}(0) = v_0$，得 $A = x_0$，$B = v_0/\omega$。

作用量 $S$ 沿经典轨道取值。对周期 $T = 2\pi/\omega$，计算
$$S = \int_0^T \left[\frac{1}{2}m\dot{x}^2 - \frac{1}{2}kx^2\right] dt = 0$$
（利用能量守恒 $E = \frac{1}{2}m\dot{x}^2 + \frac{1}{2}kx^2 = \text{const}$，一个周期内动能与势能平均值相等）

### 例 4.2：量子谐振子的能量本征值

量子谐振子的Hamilton算子
$$\hat{H} = \frac{\hat{p}^2}{2m} + \frac{1}{2}m\omega^2 \hat{x}^2$$
引入升降算子
$$a = \sqrt{\frac{m\omega}{2\hbar}}\left(\hat{x} + \frac{i\hat{p}}{m\omega}\right), \quad a^\dagger = \sqrt{\frac{m\omega}{2\hbar}}\left(\hat{x} - \frac{i\hat{p}}{m\omega}\right)$$

满足 $[a, a^\dagger] = 1$，且 $\hat{H} = \hbar\omega(a^\dagger a + \frac{1}{2})$。

设 $|\psi_n\rangle$ 满足 $a^\dagger a |\psi_n\rangle = n |\psi_n\rangle$。则
$$\hat{H} |\psi_n\rangle = \hbar\omega\left(n + \frac{1}{2}\right) |\psi_n\rangle$$

能级 $E_n = \hbar\omega(n + 1/2)$。基态 $|\psi_0\rangle$ 满足 $a|\psi_0\rangle = 0$，即
$$\left(\frac{d}{dx} + \frac{m\omega}{\hbar}x\right)\psi_0(x) = 0$$
解得 $\psi_0(x) = \left(\frac{m\omega}{\pi\hbar}\right)^{1/4} e^{-m\omega x^2 / 2\hbar}$。

---

## 5. 进阶主题与关联

### 5.1 杨-Mills方程与规范场论

杨-Mills作用量
$$S_{YM} = \frac{1}{2g^2} \int \text{Tr}(F \wedge *F)$$
其中 $F = dA + A \wedge A$ 为规范场的曲率。Euler-Lagrange方程给出**Yang-Mills方程**：
$$D_A *F = 0, \quad D_A F = 0$$
（Bianchi恒等式自动满足）。瞬子解对应自对偶条件 $F = *F$ 或反自对偶 $F = -*F$。

### 5.2 数学物理与形式化验证

Lean4与Coq中已开始形式化量子力学的部分结果，包括：
- 谱定理的构造性版本
- 有限维量子力学的密度矩阵形式化
- 杨-Mills存在性与质量间隙问题的严格表述

---

## 内容导航

- **01-核心内容** — 数学物理的核心理论与方法
- **02-补充内容1** — 拓展阅读与进阶主题
- **03-补充内容2** — 专题深化与前沿介绍
- **数学物理思维导图** — 知识结构全景图
- **数学物理方程习题精解** — 经典习题详解

## 相关链接

- [项目总索引](../../INDEX.md)
- [语义模型](../10-语义模型)
- [实战问题解决](../00-实战问题解决)
