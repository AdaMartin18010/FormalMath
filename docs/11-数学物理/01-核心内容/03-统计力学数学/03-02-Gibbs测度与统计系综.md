---
msc_primary: 82B03
msc_secondary:
- 82B05
- 60G60
- 28D20
title: Gibbs测度与统计系综
processed_at: '2026-04-05'
---
# Gibbs测度与统计系综

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

Gibbs测度是统计力学中描述平衡态的核心概念。Boltzmann的统计假说和Gibbs的系综理论为统计力学奠定了物理基础。从数学角度看，Gibbs测度是在给定宏观约束下使熵最大的概率测度，这一变分原理体现了热力学第二定律的统计本质。

**核心思想**: 平衡态对应于在给定宏观约束下熵最大的概率分布。

---

## 📝 基础概念

### 1.1 统计系综的数学表述

**定义 1.1** (微观状态空间)
$N$ 粒子系统的**微观状态空间**是相空间 $\Gamma_N = \Lambda^N \times \mathbb{R}^{3N}$（经典情形）或Hilbert空间 $\mathcal{H}_N$（量子情形），其中 $\Lambda \subset \mathbb{R}^3$ 是系统容器。

**定义 1.2** (宏观可观测量)
**宏观可观测量**是微观状态的函数 $A: \Gamma_N \to \mathbb{R}$，通常是大量粒子的集体性质（如总能量、粒子数密度）。

---

### 1.2 Gibbs测度

**定义 1.3** (正则系综的Gibbs测度)
考虑粒子数固定、体积固定、温度固定的系统。**Gibbs测度**（正则分布）定义为：
$$d\mu_\beta = \frac{1}{Z_\beta} e^{-\beta H_N(x)} dx$$

其中：
- $H_N: \Gamma_N \to \mathbb{R}$ 是系统的Hamilton函数
- $\beta = (k_B T)^{-1}$ 是逆温度
- $Z_\beta = \int_{\Gamma_N} e^{-\beta H_N(x)} dx$ 是**配分函数**

**定义 1.4** (巨正则系综)
粒子数可变时，**巨正则Gibbs测度**为：
$$d\mu_{\beta,\mu} = \frac{1}{\Xi_{\beta,\mu}} \sum_{N=0}^\infty \frac{z^N}{N!} e^{-\beta H_N(x)} dx$$

其中 $z = e^{\beta\mu}$ 是逸度，$\mu$ 是化学势，$\Xi_{\beta,\mu}$ 是**巨配分函数**。

---

### 1.3 熵

**定义 1.5** (Gibbs熵)
概率测度 $\mu$ 相对于参考测度 $dx$ 的**Gibbs熵**定义为：
$$S(\mu) = -k_B \int \rho(x) \ln \rho(x) \, dx$$
其中 $\rho = d\mu/dx$ 是密度函数。

**定义 1.6** (相对熵 / Kullback-Leibler散度)
测度 $\mu$ 相对于 $\nu$ 的**相对熵**为：
$$S(\mu|\nu) = \int \ln\left(\frac{d\mu}{d\nu}\right) d\mu$$
若 $\mu$ 不绝对连续于 $\nu$，则 $S(\mu|\nu) = +\infty$。

---

## 🎯 核心定理

### 2.1 Gibbs变分原理

**定理 2.1** (Gibbs变分原理)
在所有具有给定平均能量 $E$ 的概率测度中，Gibbs测度使熵最大。等价地，Gibbs测度最小化自由能泛函：
$$F(\mu) = \int H \, d\mu - \frac{1}{\beta} S(\mu)$$

**证明概要**:
对任意 $\mu$，考虑相对熵 $S(\mu|\mu_\beta)$：
$$S(\mu|\mu_\beta) = \int \rho \ln\left(\frac{\rho}{e^{-\beta H}/Z}\right) dx = \beta F(\mu) - \beta F(\mu_\beta) \geq 0$$

等号成立当且仅当 $\mu = \mu_\beta$。$\square$

---

### 2.2 热力学量

由配分函数可导出所有热力学量：

| 热力学量 | 公式 |
|----------|------|
| 内能 | $U = \langle H \rangle = -\frac{\partial \ln Z}{\partial \beta}$ |
| 自由能 | $F = -\frac{1}{\beta}\ln Z$ |
| 熵 | $S = k_B(\ln Z + \beta U)$ |
| 热容 | $C = \frac{\partial U}{\partial T} = k_B \beta^2 \frac{\partial^2 \ln Z}{\partial \beta^2}$ |
| 压强 | $P = \frac{1}{\beta}\frac{\partial \ln Z}{\partial V}$ |

---

### 2.3 理想气体的配分函数

**定理 2.2** (理想气体的配分函数)
$N$ 个无相互作用粒子的配分函数为：
$$Z_N = \frac{1}{N!}\left(\frac{V}{\lambda^3}\right)^N$$

其中 $\lambda = h/\sqrt{2\pi mk_BT}$ 是热de Broglie波长。

**自由能**:
$$F = -k_BT \ln Z_N = -k_BT N\left[\ln\left(\frac{V}{N\lambda^3}\right) + 1\right]$$

这是Sackur-Tetrode方程。

---

## 💡 实战问题

### 问题1：两能级系统

**问题**: 考虑两能级系统，能级为 $E_0 = 0$ 和 $E_1 = \epsilon$。计算配分函数、内能和热容。

**解答**:

配分函数：
$$Z = e^{-\beta \cdot 0} + e^{-\beta \epsilon} = 1 + e^{-\beta\epsilon}$$

内能：
$$U = -\frac{\partial \ln Z}{\partial \beta} = \frac{\epsilon e^{-\beta\epsilon}}{1 + e^{-\beta\epsilon}} = \frac{\epsilon}{e^{\beta\epsilon} + 1}$$

热容：
$$C = \frac{\partial U}{\partial T} = k_B (\beta\epsilon)^2 \frac{e^{\beta\epsilon}}{(1 + e^{\beta\epsilon})^2}$$

在高温极限（$\beta\epsilon \ll 1$）：$U \approx \epsilon/2$，$C \approx k_B(\beta\epsilon)^2/4 \to 0$

在低温极限（$\beta\epsilon \gg 1$）：$U \approx \epsilon e^{-\beta\epsilon} \to 0$，$C \approx k_B(\beta\epsilon)^2 e^{-\beta\epsilon} \to 0$

热容在中间温度有极大值（Schottky反常）。

---

### 问题2：谐振子系统

**问题**: 量子谐振子 $H = \hbar\omega(n + 1/2)$ 与热库接触。计算平均能量和热容。

**解答**:

配分函数：
$$Z = \sum_{n=0}^\infty e^{-\beta\hbar\omega(n + 1/2)} = \frac{e^{-\beta\hbar\omega/2}}{1 - e^{-\beta\hbar\omega}}$$

平均能量：
$$U = -\frac{\partial \ln Z}{\partial \beta} = \hbar\omega\left(\frac{1}{2} + \frac{1}{e^{\beta\hbar\omega} - 1}\right)$$

热容：
$$C = k_B (\beta\hbar\omega)^2 \frac{e^{\beta\hbar\omega}}{(e^{\beta\hbar\omega} - 1)^2}$$

在高温极限（$\beta\hbar\omega \ll 1$）：$C \approx k_B$（经典极限）
在低温极限（$\beta\hbar\omega \gg 1$）：$C \approx k_B (\beta\hbar\omega)^2 e^{-\beta\hbar\omega} \to 0$（量子效应）

---

### 问题3：熵的凹性

**问题**: 证明Gibbs熵是凹函数：$S(\lambda\mu_1 + (1-\lambda)\mu_2) \geq \lambda S(\mu_1) + (1-\lambda)S(\mu_2)$。

**解答**:

设 $\mu = \lambda\mu_1 + (1-\lambda)\mu_2$，对应的密度 $\rho = \lambda\rho_1 + (1-\lambda)\rho_2$。

由于 $f(x) = -x\ln x$ 是凹函数：
$$f(\rho) = f(\lambda\rho_1 + (1-\lambda)\rho_2) \geq \lambda f(\rho_1) + (1-\lambda)f(\rho_2)$$

积分两边：
$$S(\mu) = \int f(\rho) dx \geq \lambda \int f(\rho_1)dx + (1-\lambda)\int f(\rho_2)dx = \lambda S(\mu_1) + (1-\lambda)S(\mu_2)$$

熵的凹性反映了混合增加不确定性（熵）。$\square$

---

## 📚 相关文献

1. **Ruelle, D.** (1969). *Statistical Mechanics: Rigorous Results*. Benjamin.
2. **Georgii, H.O.** (2011). *Gibbs Measures and Phase Transitions* (2nd ed.). de Gruyter.
3. **Pathria, R.K., & Beale, P.D.** (2011). *Statistical Mechanics* (3rd ed.). Academic Press.

---

**最后更新**: 2026年4月4日
