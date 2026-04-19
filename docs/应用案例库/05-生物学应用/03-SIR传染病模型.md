---
msc_primary: 20

  - 20A99
  - 35A99
  - 00A99
  - 00A99
title: SIR传染病模型的传播动力学
processed_at: '2026-04-05'
---
# SIR传染病模型的传播动力学

## 应用领域

**学科**: 流行病学 / 公共卫生  
**具体应用**: COVID-19建模、流感预测、疫苗接种策略、疫情控制  
**MSC分类**: 92D30 (Epidemiology), 34C23 (Bifurcation), 93C15 (Control systems governed by ODE)

---

## 数学概念

### 核心数学工具

1. **房室模型**: 将人群分为不同状态
2. **基本再生数** $R_0$: 一个感染者平均传染人数
3. **微分方程系统**: 非线性ODE
4. **平衡点分析**: 疾病自由平衡与地方病平衡
5. **参数估计**: 从数据拟合模型参数

### 关键定义

- **S**: 易感者(Susceptible)
- **I**: 感染者(Infectious)
- **R**: 康复/移除者(Removed/Recovered)
- **$R_0$**: 基本再生数

---

## 问题描述

### 流行病学问题

**核心问题**:
1. 疾病是否会流行？
2. 最终感染多少人？
3. 如何控制疫情？

### SIR模型假设

1. 封闭人群（无出生、死亡、迁移）
2. 均匀混合（所有人接触概率相同）
3. 康复后免疫（不再次感染）
4. 潜伏期可忽略

---

## 数学模型

### SIR微分方程

**总人数**: $N = S + I + R = \text{const}$

**动态方程**:

$$\boxed{\frac{dS}{dt} = -\beta \frac{SI}{N}}$$
$$\boxed{\frac{dI}{dt} = \beta \frac{SI}{N} - \gamma I}$$
$$\boxed{\frac{dR}{dt} = \gamma I}$$

**参数**:
- $\beta$: 传染率（单位时间内有效接触次数）
- $\gamma$: 恢复率（$1/\gamma$ 是平均感染期）
- $\beta/\gamma = R_0$: 基本再生数

### 基本再生数 $R_0$

**定义**: 当几乎所有人口都易感时，一个感染者在其感染期内平均传染的人数。

$$R_0 = \frac{\beta}{\gamma}$$

**流行病学意义**:
- $R_0 < 1$: 疾病自然消亡
- $R_0 > 1$: 疾病流行

### 最终规模方程

**关键观察**: 从第一和第三方程:

$$\frac{dS}{dR} = -\frac{S}{R_0 N}$$

**解得**:

$$S(t) = S(0) \exp\left(-\frac{R(t)}{N}R_0\right)$$

**最终规模**（$t \to \infty$，$I = 0$）:

设 $s_0 = S(0)/N \approx 1$，$s_\infty = S(\infty)/N$:

$$s_\infty = \exp(R_0(s_\infty - 1))$$

**最终感染比例**:

$$r_\infty = 1 - s_\infty$$

### 群体免疫阈值

**当 $R_0 > 1$ 时**，为使 $R_{eff} = R_0 s < 1$:

需要免疫比例:

$$p_c = 1 - \frac{1}{R_0}$$

| 疾病 | $R_0$ | 群体免疫阈值 |
|------|-------|-------------|
| 麻疹 | 12-18 | 92-94% |
| 脊髓灰质炎 | 5-7 | 80-86% |
| COVID-19(原始) | 2-3 | 50-67% |
| 流感 | 1-2 | 0-50% |

---

## 求解过程

### 步骤1：无量纲化

**变量变换**:

$$s = \frac{S}{N}, \quad i = \frac{I}{N}, \quad r = \frac{R}{N}, \quad \tau = \gamma t$$

**无量纲方程**:

$$\frac{ds}{d\tau} = -R_0 s i$$
$$\frac{di}{d\tau} = R_0 s i - i = (R_0 s - 1)i$$
$$\frac{dr}{d\tau} = i$$

**初始条件**: $s(0) = 1 - \epsilon$, $i(0) = \epsilon$, $r(0) = 0$（小引入）

### 步骤2：数值求解

**显式欧拉**（教学用，需小步长）:

$$s_{n+1} = s_n - h R_0 s_n i_n$$
$$i_{n+1} = i_n + h (R_0 s_n - 1) i_n$$
$$r_{n+1} = r_n + h i_n$$

**改进方法**:
- Runge-Kutta 4阶
- 保持 $s + i + r = 1$

### 步骤3：参数估计

**从疫情数据估计 $R_0$**:

早期指数增长: $I(t) \approx I_0 e^{(R_0 - 1)\gamma t}$

拟合: $\ln I(t)$ vs $t$ 的斜率 $= (R_0 - 1)\gamma$

**从序列数据估计**:
- 最大似然估计
- 贝叶斯推断（MCMC）

### 步骤4：控制策略建模

**社交距离**: 降低 $\beta$ 至 $\beta' = (1-p)\beta$

有效再生数:

$$R_{eff} = (1-p)R_0$$

其中 $p$ 是社交距离强度。

**疫苗接种**: 将个体从 $S$ 直接移至 $R$

**隔离**: 将感染者从 $I$ 移至隔离状态

---

## 结果分析

### 流行病曲线

**特征**:
1. 潜伏期（指数增长）
2. 峰值（$R_{eff} = 1$，即 $s = 1/R_0$）
3. 下降期（易感者耗尽）

**峰值感染比例**:

当 $s = 1/R_0$ 时，$i$ 达到最大:

$$i_{max} = 1 - \frac{1}{R_0}(1 + \ln R_0)$$

### 模型局限性

| 局限 | 影响 | 改进模型 |
|------|------|----------|
| **均匀混合** | 忽视网络结构 | 网络SIR |
| **无潜伏期** | 传播速度高估 | SEIR模型 |
| **永久免疫** | 不适用反复感染 | SIRS/SIS模型 |
| **封闭人群** | 忽视出生/死亡 | 带人口动态的SIR |
| **空间同质** | 忽视地理传播 | 反应-扩散模型 |

### 扩展模型

**SEIR模型**（含潜伏期）:

$$\frac{dS}{dt} = -\beta \frac{SI}{N}$$
$$\frac{dE}{dt} = \beta \frac{SI}{N} - \sigma E$$
$$\frac{dI}{dt} = \sigma E - \gamma I$$
$$\frac{dR}{dt} = \gamma I$$

其中 $E$ 是暴露（潜伏）人群，$1/\sigma$ 是平均潜伏期。

**$R_0$ 变为**:

$$R_0 = \frac{\beta}{\gamma}$$（形式相同，但动态不同）

---

## 参考资源

### 经典文献

- **Kermack, W.O. & McKendrick, A.G.** (1927). "A contribution to the mathematical theory of epidemics". *Proc. R. Soc. Lond. A*.
- **Anderson, R.M. & May, R.M.** (1991). *Infectious Diseases of Humans: Dynamics and Control*.

### COVID-19建模

- **Ferguson, N.M. et al.** (2020). "Impact of non-pharmaceutical interventions (NPIs) to reduce COVID-19 mortality". *Imperial College*.

### 推荐教材

- **Keeling, M.J. & Rohani, P.** *Modeling Infectious Diseases in Humans and Animals*.
- **Brauer, F., Castillo-Chavez, C., & Feng, Z.** *Mathematical Models in Epidemiology*.

---

**创建日期**: 2026年4月2日  
**最后更新**: 2026年4月2日
