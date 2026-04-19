---
msc_primary: 00

  - 00A99
title: Black-Scholes期权定价公式推导链
processed_at: '2026-04-05'
---
# Black-Scholes期权定价公式推导链

## 概述
本推理树展示从随机微分方程到Black-Scholes期权定价公式的完整推导过程，包括无套利原理、风险中性定价、偏微分方程求解等核心步骤。

---

## 推理树

```mermaid
graph TD
    subgraph 市场模型
        A1[股票价格过程<br/>几何布朗运动<br/>dSₜ = μSₜdt + σSₜdWₜ] --> A2[无风险资产<br/>dBₜ = rBₜdt]
        A2 --> A3[完备市场假设<br/>无套利+可复制]
    end
    
    subgraph 无套利原理
        A3 --> B1[自融资策略<br/>dVₜ = αₜdSₜ + βₜdBₜ]
        B1 --> B2[期权复制<br/>V_T = (S_T - K)⁺]
        B2 --> B3[唯一性定理<br/>无套利⇒价格唯一]
    end
    
    subgraph 风险中性测度
        B3 --> C1[Girsanov定理<br/>测度变换: P → Q]
        C1 --> C2[新布朗运动<br/>dW̃ₜ = dWₜ + θdt]
        C2 --> C3[风险中性漂移<br/>μ → r]
    end
    
    subgraph Black-Scholes PDE
        B3 --> D1[伊藤引理<br/>df = fₜdt + fₛdS + ½fₛₛd[S]]
        D1 --> D2[构建无风险组合<br/>Π = f - Δ·S]
        D2 --> D3[BS偏微分方程<br/>fₜ + rSfₛ + ½σ²S²fₛₛ = rf]
    end
    
    subgraph 边界条件
        D3 --> E1[看涨期权边界<br/>f(T,S) = (S-K)⁺]
        E1 --> E2[零边界条件<br/>f(t,0) = 0]
        E2 --> E3[渐近条件<br/>f(t,S) ~ S 当 S→∞]
    end
    
    subgraph 解析解
        C3 --> F1[风险中性期望<br/>f = e⁻ʳᵀE_Q[(S_T-K)⁺]]
        D3 --> F2[变量变换<br/>x = ln(S/K)]
        F2 --> F3[热方程转化<br/>∂u/∂τ = ∂²u/∂x²]
        F3 --> F4[Fourier解法<br/>高斯积分]
        F1 --> G1[Black-Scholes公式<br/>f = SN(d₁) - Ke⁻ʳᵀN(d₂)]
        F4 --> G1
    end
    
    G1 --> H1[希腊字母<br/>Delta, Gamma, Vega, Theta]
    G1 --> H2[隐含波动率<br/>σ_implied]
    
    style G1 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style D3 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style A1 fill:#e1f5ff,stroke:#01579b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：几何布朗运动模型

**假设**：股票价格 $S_t$ 服从几何布朗运动

$$dS_t = \mu S_t dt + \sigma S_t dW_t$$

其中：
- $\mu$：漂移率（预期收益率）
- $\sigma$：波动率
- $W_t$：标准布朗运动

**解的形式**：
$$S_t = S_0 \exp\left[\left(\mu - \frac{\sigma^2}{2}\right)t + \sigma W_t\right]$$

### 第二步：伊藤引理应用

设 $f(t, S_t)$ 为期权价格，应用伊藤引理：

$$df = \frac{\partial f}{\partial t}dt + \frac{\partial f}{\partial S}dS_t + \frac{1}{2}\frac{\partial^2 f}{\partial S^2}(dS_t)^2$$

代入 $dS_t = \mu S_t dt + \sigma S_t dW_t$：

$$df = \left(f_t + \mu S f_S + \frac{1}{2}\sigma^2 S^2 f_{SS}\right)dt + \sigma S f_S dW_t$$

### 第三步：构建无风险组合

**策略**：持有1份期权，做空 $\Delta = \frac{\partial f}{\partial S}$ 份股票

$$\Pi = f - \Delta \cdot S = f - f_S \cdot S$$

组合价值变化：
$$d\Pi = df - f_S \cdot dS$$

$$= \left(f_t + \frac{1}{2}\sigma^2 S^2 f_{SS}\right)dt$$

### 第四步：Black-Scholes PDE

由无套利原理：$d\Pi = r\Pi dt$

$$f_t + \frac{1}{2}\sigma^2 S^2 f_{SS} + rSf_S - rf = 0$$

**边界条件**（看涨期权）：
- 终端：$f(T, S) = \max(S - K, 0)$
- 边界：$f(t, 0) = 0$，当 $S \to \infty$ 时 $f \sim S$

### 第五步：风险中性定价

**Girsanov定理**：存在等价鞅测度 $Q$，使得
$$\tilde{W}_t = W_t + \frac{\mu - r}{\sigma}t$$

在 $Q$ 下：$dS_t = rS_t dt + \sigma S_t d\tilde{W}_t$

**鞅表示**：$e^{-rt}S_t$ 是 $Q$-鞅

### 第六步：解析解推导

**风险中性定价公式**：
$$f(t, S) = e^{-r(T-t)} E_Q[(S_T - K)^+ | \mathcal{F}_t]$$

**计算过程**：
1. 令 $\tau = T - t$，$x = \ln(S/K)$
2. PDE 转化为热方程
3. Fourier 变换求解
4. 得到高斯积分形式

**Black-Scholes公式**：

$$C(S, t) = S N(d_1) - K e^{-r(T-t)} N(d_2)$$

其中：
$$d_1 = \frac{\ln(S/K) + (r + \sigma^2/2)(T-t)}{\sigma\sqrt{T-t}}$$

$$d_2 = d_1 - \sigma\sqrt{T-t} = \frac{\ln(S/K) + (r - \sigma^2/2)(T-t)}{\sigma\sqrt{T-t}}$$

---

## 希腊字母（敏感性分析）

| 希腊字母 | 定义 | 公式 | 意义 |
|---------|------|------|------|
| Delta | $\Delta = \frac{\partial C}{\partial S}$ | $N(d_1)$ | 价格对冲比率 |
| Gamma | $\Gamma = \frac{\partial^2 C}{\partial S^2}$ | $\frac{N'(d_1)}{S\sigma\sqrt{T-t}}$ | Delta变化率 |
| Vega | $\mathcal{V} = \frac{\partial C}{\partial \sigma}$ | $S\sqrt{T-t}N'(d_1)$ | 波动率风险 |
| Theta | $\Theta = \frac{\partial C}{\partial t}$ | $-\frac{S\sigma N'(d_1)}{2\sqrt{T-t}} - rKe^{-r(T-t)}N(d_2)$ | 时间衰减 |
| Rho | $\rho = \frac{\partial C}{\partial r}$ | $K(T-t)e^{-r(T-t)}N(d_2)$ | 利率风险 |

---

## 依赖关系图

```

随机微积分基础
    ↓
几何布朗运动 ← 伊藤引理
    ↓
无套利原理 → 完备市场
    ↓
Black-Scholes PDE ← Girsanov定理
    ↓
风险中性定价 = PDE解法
    ↓
Black-Scholes公式
    ↓
希腊字母分析 + 隐含波动率

```

---

## 关键引理汇总

| 引理/定理 | 作用 | 证明复杂度 |
|-----------|------|------------|
| 伊藤引理 | 随机过程函数微分 | ★★★ |
| Girsanov定理 | 测度变换 | ★★★★ |
| 鞅表示定理 | 可复制性证明 | ★★★ |
| 热方程基本解 | PDE解析解 | ★★☆ |

---

## 参考

- Black, F. & Scholes, M. (1973). "The Pricing of Options and Corporate Liabilities"
- Merton, R. C. (1973). "Theory of Rational Option Pricing"
- Shreve, S. E. (2004). *Stochastic Calculus for Finance II*
- Øksendal, B. (2003). *Stochastic Differential Equations*

---

*生成时间：2026年4月*
