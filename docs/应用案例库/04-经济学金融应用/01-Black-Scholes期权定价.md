---
msc_primary: "00A99"
msc_secondary: ['35-XX', '12Exx', '13Cxx']
---

# Black-Scholes期权定价模型

## 应用领域

**学科**: 金融工程 / 随机微积分  
**具体应用**: 期权定价、风险管理、衍生品交易、投资组合对冲  
**MSC分类**: 91G20 (Derivative securities), 60H10 (Stochastic ODE), 35K15 (Parabolic PDE)

---

## 数学概念

### 核心数学工具

1. **布朗运动**: 随机游走的连续极限
2. **伊藤引理**: 随机过程的链式法则
3. **风险中性定价**: 鞅测度下的期望
4. **偏微分方程**: Black-Scholes PDE
5. **Girsanov定理**: 测度变换

### 关键定义

- **几何布朗运动**: $dS_t = \mu S_t dt + \sigma S_t dW_t$
- **无套利**: 不存在无风险利润机会

---

## 问题描述

### 期权定价问题

**欧式看涨期权**: 到期日 $T$ 以执行价 $K$ 购买标的资产的权利。

** payoff**: $C_T = \max(S_T - K, 0)$

**问题**: 在时刻 $t < T$，期权的公平价格是多少？

### 市场假设

1. **无摩擦市场**: 无交易成本、无税收
2. **连续交易**: 可连续调整对冲组合
3. **无风险利率**: $r$ 为常数
4. **标的资产价格**: 遵循几何布朗运动
5. **无股息**: 标的资产不支付股息

---

## 数学模型

### 几何布朗运动

**标的资产价格**:

$$dS_t = \mu S_t dt + \sigma S_t dW_t$$

其中:
- $\mu$: 漂移率（预期收益率）
- $\sigma$: 波动率
- $W_t$: 标准布朗运动

**解**:

$$S_t = S_0 \exp\left(\left(\mu - \frac{\sigma^2}{2}\right)t + \sigma W_t\right)$$

$\ln S_t$ 服从正态分布: $\mathcal{N}(\ln S_0 + (\mu - \sigma^2/2)t, \sigma^2 t)$

### Black-Scholes PDE

**推导**: 构建无风险组合 $\Pi = C - \Delta S$

选择 $\Delta = \frac{\partial C}{\partial S}$ 消除随机性，由无套利要求：

$$\boxed{\frac{\partial C}{\partial t} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 C}{\partial S^2} + rS\frac{\partial C}{\partial S} - rC = 0}$$

**边界条件**: $C(S, T) = \max(S - K, 0)$

### Black-Scholes公式

**欧式看涨期权**:

$$C(S, t) = S N(d_1) - K e^{-r(T-t)} N(d_2)$$

其中:

$$d_1 = \frac{\ln(S/K) + (r + \sigma^2/2)(T-t)}{\sigma\sqrt{T-t}}$$
$$d_2 = d_1 - \sigma\sqrt{T-t}$$

$N(\cdot)$ 是标准正态累积分布函数。

**欧式看跌期权**（由Put-Call平价）:

$$P(S, t) = K e^{-r(T-t)} N(-d_2) - S N(-d_1)$$

或 $P = C - S + Ke^{-r(T-t)}$

---

## 求解过程

### 步骤1：变量变换

将Black-Scholes PDE转换为热方程。

**变换**:
- $\tau = T - t$（到期时间）
- $x = \ln(S/K)$（对数价格）
- $C = K e^{-\frac{1}{2}(k-1)x - \frac{1}{4}(k+1)^2\tau} u(x, \tau)$

其中 $k = 2r/\sigma^2$。

**结果**: 标准热方程

$$\frac{\partial u}{\partial \tau} = \frac{\partial^2 u}{\partial x^2}$$

### 步骤2：热方程求解

**初始条件**: $u(x, 0) = \max(e^{\frac{1}{2}(k+1)x} - e^{\frac{1}{2}(k-1)x}, 0)$

**解**:

$$u(x, \tau) = \frac{1}{\sqrt{4\pi\tau}} \int_{-\infty}^{\infty} u(y, 0) e^{-(x-y)^2/4\tau} dy$$

计算得:

$$u(x, \tau) = e^{\frac{1}{2}(k+1)x + \frac{1}{4}(k+1)^2\tau} N(d_1) - e^{\frac{1}{2}(k-1)x + \frac{1}{4}(k-1)^2\tau} N(d_2)$$

### 步骤3：变换回原变量

代回 $C(S, t)$，得到Black-Scholes公式。

### 步骤4：风险中性推导

**鞅测度**: 在风险中性测度 $\mathbb{Q}$ 下，$e^{-rt}S_t$ 是鞅。

**定价公式**:

$$C(S, t) = e^{-r(T-t)} \mathbb{E}^\mathbb{Q}[\max(S_T - K, 0) | S_t = S]$$

在 $\mathbb{Q}$ 下，$dS_t = rS_t dt + \sigma S_t dW_t^\mathbb{Q}$

计算该期望得到相同结果。

---

## 结果分析

### Greeks（敏感度分析）

| Greek | 定义 | 公式 | 意义 |
|-------|------|------|------|
| **Delta** | $\Delta = \frac{\partial C}{\partial S}$ | $N(d_1)$ | 对冲比率 |
| **Gamma** | $\Gamma = \frac{\partial^2 C}{\partial S^2}$ | $\frac{N'(d_1)}{S\sigma\sqrt{T-t}}$ | Delta变化率 |
| **Theta** | $\Theta = \frac{\partial C}{\partial t}$ | 复杂 | 时间衰减 |
| **Vega** | $\mathcal{V} = \frac{\partial C}{\partial \sigma}$ | $S N'(d_1)\sqrt{T-t}$ | 波动率敏感度 |
| **Rho** | $\rho = \frac{\partial C}{\partial r}$ | $K(T-t)e^{-r(T-t)}N(d_2)$ | 利率敏感度 |

### 隐含波动率

**问题**: 从市场价格反推波动率 $\sigma_{imp}$。

$$C_{market} = C_{BS}(S, K, T, r, \sigma_{imp})$$

**波动率微笑**: 不同执行价的隐含波动率不同，违背BS常数波动率假设。

### 模型局限性

| 假设 | 现实 | 改进 |
|------|------|------|
| 常数波动率 | 波动率随机 | 随机波动率模型(Heston) |
| 连续价格 | 跳跃存在 | 跳跃扩散模型(Merton) |
| 无摩擦 | 有交易成本 | 交易成本模型 |
| 对数正态分布 | 厚尾现象 | Levy过程模型 |

---

## 参考资源

### 原始论文

- **Black, F. & Scholes, M.** (1973). "The pricing of options and corporate liabilities". *J. Polit. Econ.*.
- **Merton, R.C.** (1973). "Theory of rational option pricing". *Bell J. Econ.*.

### 推荐教材

- **Hull, J.C.** *Options, Futures, and Other Derivatives*.
- **Shreve, S.E.** *Stochastic Calculus for Finance II: Continuous-Time Models*.
- **Björk, T.** *Arbitrage Theory in Continuous Time*.

---

**创建日期**: 2026年4月2日  
**最后更新**: 2026年4月2日
