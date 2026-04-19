---
title: "README"
msc_primary: "00"
---

# 数学物理方法：从经典力学到量子场论

数学物理（Mathematical Physics）是应用数学与理论物理的交叉领域，其核心任务在于为物理理论提供严格的数学基础，并借助物理直觉发现新的数学结构。从 Newton 力学中的常微分方程到广义相对论中的微分几何，从量子力学的泛函分析到统计力学的概率论，数学物理始终是推动数学与物理双向发展的核心动力。

## 1. 变分法与 Euler-Lagrange 方程

### 1.1 泛函

**定义 1.1（泛函）**. 设 $X$ 为函数空间。泛函 $J: X \to \mathbb{R}$ 将函数映射到实数。

**定义 1.2（泛函导数）**. $J$ 在 $y$ 处沿方向 $\eta$ 的变分为：

$$\delta J(y)[\eta] = \lim_{\epsilon \to 0} \frac{J(y + \epsilon\eta) - J(y)}{\epsilon}.$$

### 1.2 Euler-Lagrange 方程

**定理 1.3（Euler-Lagrange）**. 设 $L(x, y, y')$ 为 Lagrange 量。泛函 $J(y) = \int_a^b L(x, y, y') dx$ 的临界点满足：

$$\frac{\partial L}{\partial y} - \frac{d}{dx}\frac{\partial L}{\partial y'} = 0.$$

*证明*. 对 $J(y + \epsilon\eta)$ 求导，分部积分，利用 $\eta(a) = \eta(b) = 0$，由基本引理得结论。$\square$

## 2. Hilbert 空间中的量子力学

### 2.1 量子力学公理

**公理 1（态）**. 量子系统的态由复 Hilbert 空间 $\mathcal{H}$ 中的单位向量 $|\psi\rangle$ 描述。

**公理 2（可观测量）**. 物理可观测量对应 $\mathcal{H}$ 上的自伴算子 $A$。

**公理 3（测量）**. 对 $A$ 的测量得到其谱中的值 $\lambda$，概率为 $|\langle \lambda | \psi \rangle|^2$。

### 2.2 Schrödinger 方程

**定义 2.1（Schrödinger 方程）**. 

$$i\hbar \frac{\partial}{\partial t}|\psi(t)\rangle = H|\psi(t)\rangle,$$

其中 $H$ 为 Hamilton 算子（能量可观测量）。

**定理 2.2（幺正演化）**. 若 $H$ 自伴，则解为 $|\psi(t)\rangle = e^{-iHt/\hbar}|\psi(0)\rangle$，保持范数。

## 3. Fourier 分析与波动方程

### 3.1 波动方程

**定义 3.1（波动方程）**. 

$$\frac{\partial^2 u}{\partial t^2} = c^2 \Delta u.$$

**定理 3.2（d'Alembert 解）**. 一维波动方程的通解为 $u(x,t) = f(x-ct) + g(x+ct)$。

## 4. 例子

### 4.1 例子：谐振子

量子谐振子：$H = \frac{p^2}{2m} + \frac{1}{2}m\omega^2 x^2$。

能量本征值：$E_n = \hbar\omega(n + 1/2)$，$n = 0, 1, 2, \dots$

### 4.2 例子：氢原子

氢原子 Schrödinger 方程的解：能量 $E_n = -\frac{13.6}{n^2}$ eV，角动量量子数 $l = 0, \dots, n-1$，磁量子数 $m = -l, \dots, l$。

## 5. 交叉引用

- [泛函分析](docs/03-分析学/03-泛函分析/03-泛函分析.md) — Hilbert 空间与算子理论
- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 广义相对论
- [偏微分方程](docs/03-分析学/04-偏微分方程/01-偏微分方程基础.md) — 波动方程与热方程
- [概率论](docs/06-概率统计/01-概率论基础.md) — 统计力学
- [辛几何](docs/04-几何与拓扑/辛几何-基础.md) — 经典力学的几何化

---

**适用**：docs/11-数学物理/
