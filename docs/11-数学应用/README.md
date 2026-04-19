---
title: "README"
msc_primary: "00"
---

# 数学建模方法论：从抽象到应用的系统框架

## 1. 引言

数学应用（Applied Mathematics）的本质在于将现实世界中的复杂现象抽象为可分析的数学结构，通过严格的逻辑推演获得对系统的深层理解，并最终指导工程实践与科学决策。从Newton建立微积分以描述天体运动，到Shannon创立信息论以量化通信容量，数学应用始终是科学革命的引擎。

本文系统阐述数学建模的通用方法论——问题抽象、模型构建、分析求解、验证迭代——并通过三个典型案例展示数学工具如何解决真实世界问题。

---

## 2. 严格数学定义

### 2.1 数学模型的分类

**定义 2.1（数学模型）**
给定现实世界系统 $\mathcal{S}$，**数学模型**是一个三元组 $(\mathcal{M}, \Phi, \Psi)$，其中：
- $\mathcal{M}$ 为数学结构（方程、图、随机过程等）
- $\Phi: \mathcal{S} \to \mathcal{M}$ 为**抽象映射**（encoding），将系统特征映到数学对象
- $\Psi: \mathcal{M} \to \mathcal{P}$ 为**解释映射**（decoding），将数学结果映到预测或决策

**定义 2.2（良定义模型）**
模型 $(\mathcal{M}, \Phi, \Psi)$ 称为**良定义的**，若：
1. **存在性**：$\mathcal{M}$ 的解存在（或依概率存在）
2. **唯一性**：解在适当意义下唯一
3. **稳定性**：解对初值/参数连续依赖（well-posedness in Hadamard sense）

### 2.2 动力系统模型

**定义 2.3（常微分方程系统）**
**自治ODE系统**为
$$\frac{dx}{dt} = f(x), \quad x(0) = x_0, \quad x \in \mathbb{R}^n$$
其中 $f: \mathbb{R}^n \to \mathbb{R}^n$ 为向量场。

**定义 2.4（平衡点与稳定性）**
点 $x^*$ 满足 $f(x^*) = 0$ 称为**平衡点**。称 $x^*$ 是**Lyapunov稳定**的，若对任意 $\varepsilon > 0$，存在 $\delta > 0$ 使得当 $\|x_0 - x^*\| < \delta$ 时，解 $x(t)$ 对所有 $t \geq 0$ 满足 $\|x(t) - x^*\| < \varepsilon$。

若 additionally $\|x(t) - x^*\| \to 0$（$t \to \infty$），则称**渐近稳定**。

### 2.3 随机模型

**定义 2.5（随机过程）**
设 $(\Omega, \mathcal{F}, \mathbb{P})$ 为概率空间，$(E, \mathcal{E})$ 为可测空间。**随机过程**是映射 $X: \Omega \times T \to E$ 使得对每个 $t \in T$，$X_t: \Omega \to E$ 可测。

**定义 2.6（马尔可夫性）**
过程 $X_t$ 具有**马尔可夫性**，若
$$\mathbb{P}(X_{t+s} \in A \mid \mathcal{F}_t) = \mathbb{P}(X_{t+s} \in A \mid X_t), \quad \forall s, t \geq 0, A \in \mathcal{E}$$
其中 $\mathcal{F}_t = \sigma(X_s : s \leq t)$。

---

## 3. 核心定理与证明

### 定理 3.1（SIR流行病模型的动力学分析）

SIR模型：
$$\frac{dS}{dt} = -\beta SI, \quad \frac{dI}{dt} = \beta SI - \gamma I, \quad \frac{dR}{dt} = \gamma I$$
其中 $S + I + R = N$（总人口）。设初始条件 $S(0) = S_0$，$I(0) = I_0$，$R(0) = 0$。

**定理**：定义基本再生数 $\mathcal{R}_0 = \frac{\beta S_0}{\gamma}$。
1. 若 $\mathcal{R}_0 \leq 1$，则 $I(t)$ 单调递减至0，无病平衡态 $(S_0, 0, 0)$ 全局渐近稳定
2. 若 $\mathcal{R}_0 > 1$，则 $I(t)$ 先增后减，最终 $I(t) \to 0$，但 $S(t) \to S_\infty > 0$

**证明**：由 $\frac{dI}{dS} = \frac{\beta SI - \gamma I}{-\beta SI} = -1 + \frac{\gamma}{\beta S}$，积分得
$$I(S) = I_0 + S_0 - S + \frac{\gamma}{\beta}\ln\frac{S}{S_0}$$

在 $S$-$I$ 相平面上，轨道满足上述关系。令 $I = 0$，$S_\infty$ 满足超越方程：
$$S_0 - S_\infty + \frac{\gamma}{\beta}\ln\frac{S_\infty}{S_0} = 0$$

对 $I$ 的方程，$\frac{dI}{dt} = I(\beta S - \gamma)$。当 $S > \gamma/\beta$（即 $\mathcal{R}_0 > 1$ 初始），$\frac{dI}{dt} > 0$，感染人数增长；当 $S$ 降至 $\gamma/\beta$ 以下，$\frac{dI}{dt} < 0$。最终因 $R$ 单调增且 $S + I + R = N$，$I \to 0$。$\square$

### 定理 3.2（Black-Scholes期权定价公式的推导）

假设股票价格 $S_t$ 服从几何布朗运动：
$$dS_t = \mu S_t \, dt + \sigma S_t \, dW_t$$
无风险利率为 $r$。欧式看涨期权价格 $C(S, t)$ 满足 Black-Scholes PDE：
$$\frac{\partial C}{\partial t} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 C}{\partial S^2} + rS\frac{\partial C}{\partial S} - rC = 0$$
边界条件 $C(S, T) = \max(S - K, 0)$。

**证明（风险中性定价）**：
由Itô引理，对 $C(S_t, t)$：
$$dC = \left(\frac{\partial C}{\partial t} + \mu S \frac{\partial C}{\partial S} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 C}{\partial S^2}\right)dt + \sigma S \frac{\partial C}{\partial S} dW_t$$

构造自融资组合 $\Pi = C - \Delta S$，选择 $\Delta = \frac{\partial C}{\partial S}$（delta对冲），则
$$d\Pi = \left(\frac{\partial C}{\partial t} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 C}{\partial S^2}\right)dt$$

无套利要求 $d\Pi = r\Pi \, dt$，代入得 Black-Scholes PDE。

通过变量替换 $x = \ln(S/K)$，$\tau = T - t$，$C = K v(x, \tau)$，化为热方程，解得
$$C(S, t) = S N(d_1) - K e^{-r(T-t)} N(d_2)$$
其中
$$d_{1,2} = \frac{\ln(S/K) + (r \pm \sigma^2/2)(T-t)}{\sigma\sqrt{T-t}}$$
$N(\cdot)$ 为标准正态CDF。$\square$

---

## 4. 详细例子

### 例 4.1：PageRank算法的马尔可夫链模型

网页链接结构建模为有向图 $G = (V, E)$，$|V| = n$。定义转移矩阵 $P$：
$$P_{ij} = \begin{cases} \frac{1}{d_i} & \text{if } (i,j) \in E \\ 0 & \text{otherwise} \end{cases}$$
其中 $d_i$ 为出度。对悬挂节点（无出边），设 $P_{ij} = 1/n$。

引入阻尼因子 $\alpha \in (0, 1)$，Google矩阵为
$$G = \alpha P + (1-\alpha)\frac{1}{n}\mathbf{1}\mathbf{1}^T$$

**定理**：$G$ 为正矩阵，由Perron-Frobenius定理存在唯一稳态分布 $\pi$（PageRank向量），满足 $\pi^T G = \pi^T$。

对 $\alpha = 0.85$，幂迭代 $\pi_{k+1}^T = \pi_k^T G$ 线性收敛，收敛率由第二特征值 $|\lambda_2| \leq \alpha$ 控制。

### 例 4.2：压缩感知的稀疏恢复理论

设信号 $x \in \mathbb{R}^n$ 为 $k$-稀疏（最多 $k$ 个非零元）。测量 $y = Ax + \eta$，其中 $A \in \mathbb{R}^{m \times n}$，$m \ll n$，$\eta$ 为噪声。

**定理（Restricted Isometry Property, RIP）**：若 $A$ 满足 $2k$-RIP，即存在 $\delta_{2k} \in (0, \sqrt{2}-1)$ 使得
$$(1-\delta_{2k})\|x\|^2 \leq \|Ax\|^2 \leq (1+\delta_{2k})\|x\|^2$$
对所有 $2k$-稀疏 $x$ 成立，则基追踪（Basis Pursuit）
$$\hat{x} = \arg\min \|z\|_1 \quad \text{s.t.} \quad \|Az - y\|_2 \leq \varepsilon$$
满足误差界
$$\|\hat{x} - x\|_2 \leq C_1 \frac{\|x - x_k\|_1}{\sqrt{k}} + C_2 \varepsilon$$
其中 $x_k$ 为 $x$ 的最佳 $k$-项逼近。

高斯随机矩阵 $A_{ij} \sim \mathcal{N}(0, 1/m)$ 以高概率满足RIP，只要 $m = O(k \log(n/k))$。

---

## 5. 进阶主题

### 5.1 机器学习优化的数学基础

神经网络训练可视为非凸优化：
$$\min_\theta \frac{1}{N}\sum_{i=1}^N \mathcal{L}(f_\theta(x_i), y_i)$$

梯度下降的收敛性在凸情形下由Lipschitz梯度条件保证：若 $\nabla f$ 是 $L$-Lipschitz，步长 $\eta \leq 1/L$，则
$$f(x_k) - f^* \leq \frac{\|x_0 - x^*\|^2}{2\eta k}$$

非凸情形下，只能保证收敛到一阶稳定点（$\|\nabla f\| \leq \varepsilon$），复杂度为 $O(\varepsilon^{-2})$。

### 5.2 形式化验证在数学建模中的应用

Lean4等定理证明器开始用于验证：
- 数值算法的误差界（浮点运算的严格分析）
- 控制系统的稳定性证明（Lyapunov函数的形式化构造）
- 密码学协议的安全性归约

---

## 内容导航

- **应用数学建模方法论 / 数学应用跨学科图谱**
- **结构力学中的变分方法**
- **流体力学数值模拟案例**
- **信号处理中的傅里叶分析**
- **控制论与最优控制实例**
- **期权定价Black-Scholes模型详解**
- **风险管理中的极值理论 / 量化投资策略数学原理**
- **种群动力学模型 / 流行病学SIR模型族**
- **神经科学的数学模型**
- **主成分分析的数学原理 / 神经网络优化的数学基础**

## 相关链接

- [项目总索引](../../INDEX.md)
- [实例与案例分析](../06-实例与案例分析)
- [实战问题解决](../00-实战问题解决)
