---
title: "README"
msc_primary: "00"
---

# 生物数学：数学在生命科学中的应用

生物数学应用数学模型与分析方法研究生命现象，涵盖种群动力学、流行病学、进化博弈论与神经科学等领域。

## 1. 种群动力学

### 1.1 Logistic 增长

**定义 1.1（Logistic 方程）**. 

$$\frac{dN}{dt} = rN\left(1 - \frac{N}{K}\right),$$

其中 $r$ 为内禀增长率，$K$ 为环境容纳量。

**解**：$N(t) = \frac{K}{1 + (\frac{K}{N_0} - 1)e^{-rt}}$。

### 1.2 Lotka-Volterra 捕食者-猎物模型

$$\begin{cases} \frac{dx}{dt} = ax - bxy \\ \frac{dy}{dt} = -cy + dxy \end{cases}$$

**定理 1.2**. 系统有周期轨道（中性稳定），中心在 $(c/d, a/b)$。

## 2. 流行病学

### 2.1 SIR 模型

$$\begin{cases} \frac{dS}{dt} = -\beta SI \\ \frac{dI}{dt} = \beta SI - \gamma I \\ \frac{dR}{dt} = \gamma I \end{cases}$$

**基本再生数**：$R_0 = \frac{\beta S_0}{\gamma}$。若 $R_0 > 1$，疫情爆发。

## 3. 进化博弈论

### 3.1 复制子动态

$$\dot{x}_i = x_i((Ax)_i - x^TAx)$$

其中 $x_i$ 为策略 $i$ 的频率，$A$ 为支付矩阵。

**定理 3.2（ESS）**. 进化稳定策略（ESS）是复制子动态的渐近稳定平衡点。

## 4. 例子

### 4.1 例子：Hodgkin-Huxley 模型

描述神经元动作电位的离子通道模型：

$$C_m \frac{dV}{dt} = -g_{Na}m^3h(V-E_{Na}) - g_K n^4(V-E_K) - g_L(V-E_L) + I_{ext}$$

其中 $m, h, n$ 为门控变量的概率。

### 4.2 例子：Turing 图案形成

反应扩散系统：

$$\begin{cases} \frac{\partial u}{\partial t} = D_u \Delta u + f(u,v) \\ \frac{\partial v}{\partial t} = D_v \Delta v + g(u,v) \end{cases}$$

在 $D_u \neq D_v$ 时，均匀稳态可通过扩散失稳产生空间图案。

## 5. 交叉引用

- [ODE](docs/03-分析学/ODE-习题与数值解.md) — 常微分方程
- [偏微分方程](docs/03-分析学/04-偏微分方程/01-偏微分方程基础.md) — 反应扩散方程
- [动力系统](docs/11-高级数学/动力系统-扩展/01-常微分方程定性理论/00-README.md) — 定性分析
- [概率论](docs/06-概率统计/01-概率论基础.md) — 随机过程
- [博弈论](docs/10-应用数学/博弈论-基础.md) — 博弈论基础

---

**适用**：docs/26-生物数学/
