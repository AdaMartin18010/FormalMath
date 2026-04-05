---
msc_primary: 82B20
msc_secondary:
- 82B26
- 82B27
- 60K35
title: Ising模型与相变
processed_at: '2026-04-05'
---
# Ising模型与相变

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

Ising模型是统计力学中最简单且最重要的格点模型，它展现了从有序到无序的相变现象。Onsager于1944年给出的二维Ising模型精确解是统计力学数学化的里程碑。该模型不仅深刻揭示了相变的本质，也为临界现象和普适性的研究奠定了基础。

**核心思想**: 短程相互作用可以导致长程有序，临界现象具有普适性。

---

## 📝 基础概念

### 1.1 Ising模型的定义

**定义 1.1** (Ising模型)
$d$ 维**Ising模型**定义在整数格点 $\mathbb{Z}^d$ 的有限子集 $\Lambda \subset \mathbb{Z}^d$ 上。每个格点 $i \in \Lambda$ 有自旋变量 $\sigma_i \in \{-1, +1\}$。

**Hamilton量**:
$$H_\Lambda(\sigma) = -J \sum_{\langle i,j \rangle \subset \Lambda} \sigma_i \sigma_j - h \sum_{i \in \Lambda} \sigma_i$$

其中：
- $\langle i,j \rangle$ 表示最近邻对
- $J > 0$（铁磁性）或 $J < 0$（反铁磁性）
- $h$ 是外磁场

**Gibbs测度**: 对 $\beta > 0$，有限体积Gibbs测度为：
$$\mu_{\Lambda,\beta,h}(\sigma) = \frac{1}{Z_{\Lambda,\beta,h}} \exp\left(-\beta H_\Lambda(\sigma)\right)$$

---

### 1.2 热力学极限

**定义 1.2** (热力学极限)
Ising模型的**热力学极限**是当 $\Lambda \nearrow \mathbb{Z}^d$（在 van Hove 意义下）时Gibbs测度的极限行为。

**定义 1.3** (自由能密度)
**自由能密度**定义为：
$$f(\beta, h) = -\lim_{\Lambda \nearrow \mathbb{Z}^d} \frac{1}{\beta|\Lambda|} \ln Z_{\Lambda,\beta,h}$$

极限的存在性和与边界条件的无关性是统计力学的重要定理。

---

### 1.3 自发磁化与临界温度

**定义 1.4** (自发磁化)
**自发磁化**定义为：
$$m^*(\beta) = \lim_{h \to 0^+} \lim_{\Lambda \nearrow \mathbb{Z}^d} \langle \frac{1}{|\Lambda|} \sum_{i \in \Lambda} \sigma_i \rangle_{\Lambda,\beta,h}$$

外磁场先趋于零，再取热力学极限。

**定义 1.5** (临界温度)
**临界温度** $\beta_c$（或 $T_c$）定义为：
$$\beta_c = \sup\{\beta : m^*(\beta) = 0\}$$

---

## 🎯 核心定理

### 2.1 Peierls论证

**定理 2.1** (Peierls论证, 1936)
对 $d \geq 2$ 的Ising模型，存在有限临界温度 $\beta_c \in (0, \infty)$ 使得：

- 当 $\beta < \beta_c$（高温）：$m^*(\beta) = 0$，唯一Gibbs态
- 当 $\beta > \beta_c$（低温）：$m^*(\beta) > 0$，至少两个不同的极值Gibbs态

**证明概要**:

**低温相（$\beta$ 大）**: 利用Peierls轮廓论证。在+边界条件下，自旋翻转的区域被轮廓包围。轮廓的能量正比于其长度，熵正比于长度。低温下能量占优，大轮廓被压制，系统保持正磁化。

**高温相（$\beta$ 小）**: 利用高温展开或Dobrushin唯一性准则。证明不同边界条件下的Gibbs测度趋于相同极限。$\square$

---

### 2.2 Onsager精确解

**定理 2.2** (Onsager, 1944)
二维零场Ising模型 ($h = 0$) 的自由能可精确计算：
$$-\beta f(\beta, 0) = \ln 2 + \frac{1}{2} \int_0^\pi \int_0^\pi \ln\left[1 + \frac{1}{\sinh^2(2\beta J)}(\cos\theta_1 + \cos\theta_2)\right] \frac{d\theta_1 d\theta_2}{(2\pi)^2}$$

**临界温度**:
$$\sinh(2\beta_c J) = 1 \quad \Rightarrow \quad k_B T_c = \frac{2J}{\ln(1+\sqrt{2})} \approx 2.269J$$

**临界指数**: Onsager解揭示临界点附近的热力学量呈现幂律行为：

| 量 | 临界行为 | 临界指数 |
|----|---------|---------|
| 比热 | $C \sim \ln|T - T_c|$ | $\alpha = 0$ (对数) |
| 自发磁化 | $m^* \sim (T_c - T)^\beta$ | $\beta = 1/8$ |
| 磁化率 | $\chi \sim |T - T_c|^{-\gamma}$ | $\gamma = 7/4$ |
| 关联长度 | $\xi \sim |T - T_c|^{-\nu}$ | $\nu = 1$ |

---

### 2.3 Gibbs测度的唯一性与多重性

**定义 2.1** (无限体积Gibbs态)
**无限体积Gibbs态**（或DLR态）是 $\{-1,+1\}^{\mathbb{Z}^d}$ 上的概率测度 $\mu$，满足对任何有限 $\Lambda \subset \mathbb{Z}^d$，条件分布 $\mu(\cdot|\mathcal{F}_{\Lambda^c})$ 由Gibbs测度给出。

**定理 2.3** (Gibbs测度的结构)
极值Gibbs测度（遍历态）对应于纯热力学相。Ising模型在 $\beta > \beta_c$ 时至少有两个极值Gibbs测度：

- $\mu_+$：正边界条件下的极限，$\langle\sigma_0\rangle_+ = m^*(\beta)$
- $\mu_-$：负边界条件下的极限，$\langle\sigma_0\rangle_- = -m^*(\beta)$

---

## 💡 实战问题

### 问题1：一维Ising模型

**问题**: 证明一维Ising模型对所有 $\beta > 0$ 没有相变（$m^* = 0$）。

**解答**:

**转移矩阵方法**: 配分函数可写为：
$$Z_N = \text{Tr}(T^N)$$

其中转移矩阵：
$$T = \begin{pmatrix} e^{\beta(J+h)} & e^{-\beta J} \\ e^{-\beta J} & e^{\beta(J-h)} \end{pmatrix}$$

当 $N \to \infty$，$Z_N \approx \lambda_+^N$，其中 $\lambda_+$ 是最大本征值。

热力学极限存在且解析。自由能是 $\beta$ 和 $h$ 的光滑函数，没有奇点。

**物理直觉**: 一维中畴壁的能量是 $O(1)$，而熵是 $O(\ln N)$。高温下熵占优，畴壁 proliferate，破坏长程序。$\square$

---

### 问题2：平均场近似

**问题**: 用平均场近似（Bragg-Williams近似）推导Ising模型的临界温度。

**解答**:

假设每个自旋感受到的平均场：
$$h_{\text{eff}} = h + zJm$$

其中 $z$ 是配位数，$m = \langle\sigma_i\rangle$ 是平均磁化。

自洽方程（来自两能级系统的磁化公式）：
$$m = \tanh(\beta(h + zJm))$$

零外场（$h = 0$）：
$$m = \tanh(\beta zJm)$$

非零解存在当且仅当 $\beta zJ > 1$，即：
$$T_c = \frac{zJ}{k_B}$$

临界温度与维度和晶格结构无关（平均场的局限）。

---

### 问题3：关联函数

**问题**: 在高温下，计算Ising模型的两点关联函数 $\langle\sigma_i \sigma_j\rangle$。

**解答**:

高温展开：$e^{\beta J \sigma_i \sigma_j} = \cosh(\beta J) + \sigma_i \sigma_j \sinh(\beta J)$

对于最近邻对：
$$\langle\sigma_i \sigma_j\rangle \approx \tanh(\beta J) \equiv \tau$$

对于距离为 $|i-j|$ 的两点，只有连接它们的路径有贡献：
$$\langle\sigma_i \sigma_j\rangle \approx \sum_{\text{paths}} \tau^{\text{length}} = \tau^{|i-j|} = e^{-|i-j|/\xi}$$

其中关联长度 $\xi = -1/\ln(\tanh(\beta J))$。

当 $\beta \to \beta_c$，$\xi \to \infty$，关联函数呈幂律衰减。

---

## 📚 相关文献

1. **Onsager, L.** (1944). Crystal statistics. I. A two-dimensional model with an order-disorder transition. *Physical Review*, 65(3-4), 117.
2. **McCoy, B.M., & Wu, T.T.** (1973). *The Two-Dimensional Ising Model*. Harvard University Press.
3. **Friedli, S., & Velenik, Y.** (2017). *Statistical Mechanics of Lattice Systems: A Concrete Mathematical Introduction*. Cambridge University Press.

---

**最后更新**: 2026年4月4日
