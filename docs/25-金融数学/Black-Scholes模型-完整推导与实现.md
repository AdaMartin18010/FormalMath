---
title: Black-Scholes期权定价模型 - 完整推导与Python实现
msc_primary: 91G20
---

# Black-Scholes期权定价模型 - 完整推导与实现

## 模型假设

1. 标的资产价格服从几何布朗运动：$dS_t = \mu S_t dt + \sigma S_t dW_t$
2. 无风险利率 $r$ 为常数
3. 无交易成本和税收
4. 可以无限制地以无风险利率借贷
5. 标的资产可以无限分割
6. 市场无套利机会

## Black-Scholes偏微分方程推导

### 步骤1：伊藤引理

设 $V(S, t)$ 是期权价格，由伊藤引理：

$$dV = \left(\frac{\partial V}{\partial t} + \mu S \frac{\partial V}{\partial S} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 V}{\partial S^2}\right)dt + \sigma S \frac{\partial V}{\partial S} dW$$

### 步骤2：构建无风险组合

构造组合 $\Pi = V - \Delta S$，选择 $\Delta = \frac{\partial V}{\partial S}$ 使组合无风险：

$$d\Pi = \left(\frac{\partial V}{\partial t} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 V}{\partial S^2}\right)dt$$

### 步骤3：无套利条件

无风险组合收益率必须等于无风险利率：

$$\frac{\partial V}{\partial t} + \frac{1}{2}\sigma^2 S^2 \frac{\partial^2 V}{\partial S^2} + rS\frac{\partial V}{\partial S} - rV = 0$$

### 步骤4：边界条件

- 看涨期权：$V(S, T) = \max(S - K, 0)$
- 看跌期权：$V(S, T) = \max(K - S, 0)$

## Black-Scholes公式

### 欧式看涨期权

$$C = S_0 N(d_1) - Ke^{-rT}N(d_2)$$

### 欧式看跌期权

$$P = Ke^{-rT}N(-d_2) - S_0 N(-d_1)$$

其中：
$$d_1 = \frac{\ln(S_0/K) + (r + \sigma^2/2)T}{\sigma\sqrt{T}}$$
$$d_2 = d_1 - \sigma\sqrt{T}$$

$N(\cdot)$ 是标准正态分布累积分布函数。

## Python完整实现

```python
import numpy as np
from scipy.stats import norm
import matplotlib.pyplot as plt

# Black-Scholes期权定价公式
def black_scholes_call(S, K, T, r, sigma):
    """
    欧式看涨期权定价

    参数:
    S: 标的资产现价
    K: 执行价格
    T: 到期时间（年）
    r: 无风险利率
    sigma: 波动率
    """
    d1 = (np.log(S / K) + (r + 0.5 * sigma**2) * T) / (sigma * np.sqrt(T))
    d2 = d1 - sigma * np.sqrt(T)

    call_price = S * norm.cdf(d1) - K * np.exp(-r * T) * norm.cdf(d2)

    return call_price

def black_scholes_put(S, K, T, r, sigma):
    """欧式看跌期权定价（看跌-看涨平价）"""
    call = black_scholes_call(S, K, T, r, sigma)
    put = call - S + K * np.exp(-r * T)
    return put

# 希腊字母计算
def greeks(S, K, T, r, sigma):
    """计算期权的希腊字母"""
    d1 = (np.log(S / K) + (r + 0.5 * sigma**2) * T) / (sigma * np.sqrt(T))
    d2 = d1 - sigma * np.sqrt(T)

    # Delta: 对标的资产价格的一阶导
    delta_call = norm.cdf(d1)
    delta_put = norm.cdf(d1) - 1

    # Gamma: 对标的资产价格的二阶导（看涨看跌相同）
    gamma = norm.pdf(d1) / (S * sigma * np.sqrt(T))

    # Theta: 对时间的一阶导
    theta_call = (-S * norm.pdf(d1) * sigma / (2 * np.sqrt(T))
                  - r * K * np.exp(-r * T) * norm.cdf(d2))

    # Vega: 对波动率的一阶导（看涨看跌相同）
    vega = S * norm.pdf(d1) * np.sqrt(T)

    # Rho: 对利率的一阶导
    rho_call = K * T * np.exp(-r * T) * norm.cdf(d2)

    return {
        'delta_call': delta_call,
        'delta_put': delta_put,
        'gamma': gamma,
        'theta_call': theta_call,
        'vega': vega,
        'rho_call': rho_call
    }

# 示例计算
S = 100      # 标的资产价格
K = 100      # 执行价格
T = 1.0      # 到期时间1年
r = 0.05     # 无风险利率5%
sigma = 0.2  # 波动率20%

call_price = black_scholes_call(S, K, T, r, sigma)
put_price = black_scholes_put(S, K, T, r, sigma)
g = greeks(S, K, T, r, sigma)

print(f"欧式看涨期权价格: {call_price:.4f}")
print(f"欧式看跌期权价格: {put_price:.4f}")
print(f"\n希腊字母:")
print(f"  Delta (Call): {g['delta_call']:.4f}")
print(f"  Gamma: {g['gamma']:.4f}")
print(f"  Vega: {g['vega']:.4f}")
```

## 可视化分析

```python
# 期权价格随标的价格变化
S_range = np.linspace(50, 150, 100)
call_prices = [black_scholes_call(s, K, T, r, sigma) for s in S_range]
put_prices = [black_scholes_put(s, K, T, r, sigma) for s in S_range]

plt.figure(figsize=(12, 5))

plt.subplot(1, 2, 1)
plt.plot(S_range, call_prices, 'b-', linewidth=2, label='Call Option')
plt.plot(S_range, np.maximum(S_range - K, 0), 'r--', label='Payoff at Expiration')
plt.xlabel('Stock Price')
plt.ylabel('Option Price')
plt.title('European Call Option')
plt.legend()
plt.grid(True)

plt.subplot(1, 2, 2)
plt.plot(S_range, put_prices, 'g-', linewidth=2, label='Put Option')
plt.plot(S_range, np.maximum(K - S_range, 0), 'r--', label='Payoff at Expiration')
plt.xlabel('Stock Price')
plt.ylabel('Option Price')
plt.title('European Put Option')
plt.legend()
plt.grid(True)

plt.tight_layout()
plt.savefig('black_scholes_prices.png', dpi=150)
```

## 隐含波动率计算

```python
from scipy.optimize import brentq

def implied_volatility(market_price, S, K, T, r, option_type='call'):
    """计算隐含波动率"""
    def objective(sigma):
        if option_type == 'call':
            return black_scholes_call(S, K, T, r, sigma) - market_price
        else:
            return black_scholes_put(S, K, T, r, sigma) - market_price

    # 使用Brent方法求解
    try:
        iv = brentq(objective, 1e-6, 5.0)
        return iv
    except ValueError:
        return None

# 示例：已知市场价格求隐含波动率
market_call_price = 10.0
iv = implied_volatility(market_call_price, S, K, T, r, 'call')
print(f"隐含波动率: {iv:.4f} ({iv*100:.2f}%)")
```

## 蒙特卡洛模拟验证

```python
def monte_carlo_option_price(S, K, T, r, sigma, n_simulations=100000, option_type='call'):
    """使用蒙特卡洛模拟计算期权价格"""
    np.random.seed(42)

    # 模拟标的资产到期价格
    Z = np.random.standard_normal(n_simulations)
    S_T = S * np.exp((r - 0.5 * sigma**2) * T + sigma * np.sqrt(T) * Z)

    # 计算收益
    if option_type == 'call':
        payoffs = np.maximum(S_T - K, 0)
    else:
        payoffs = np.maximum(K - S_T, 0)

    # 折现求期望
    option_price = np.exp(-r * T) * np.mean(payoffs)

    # 计算标准误差
    stderr = np.exp(-r * T) * np.std(payoffs) / np.sqrt(n_simulations)

    return option_price, stderr

# 验证Black-Scholes公式
mc_price, mc_stderr = monte_carlo_option_price(S, K, T, r, sigma)
bs_price = black_scholes_call(S, K, T, r, sigma)

print(f"Black-Scholes价格: {bs_price:.4f}")
print(f"Monte Carlo价格: {mc_price:.4f} ± {mc_stderr:.4f}")
print(f"差异: {abs(bs_price - mc_price):.4f}")
```

## 敏感性分析

```python
# 波动率微笑分析
strikes = np.linspace(80, 120, 20)
implied_vols = []

# 假设市场价格有偏离
for k in strikes:
    # 模拟市场价格（带有一些偏离）
    true_price = black_scholes_call(S, k, T, r, sigma)
    market_price = true_price * (1 + np.random.normal(0, 0.02))  # 2%噪声

    iv = implied_volatility(market_price, S, k, T, r, 'call')
    implied_vols.append(iv)

plt.figure(figsize=(10, 6))
plt.plot(strikes, implied_vols, 'bo-', linewidth=2, markersize=8)
plt.axhline(y=sigma, color='r', linestyle='--', label=f'Theoretical σ = {sigma}')
plt.xlabel('Strike Price')
plt.ylabel('Implied Volatility')
plt.title('Volatility Smile')
plt.legend()
plt.grid(True)
plt.savefig('volatility_smile.png', dpi=150)
```

## 习题

### 习题1

证明看跌-看涨平价关系：$C - P = S - Ke^{-rT}$

**证明**：构造两个组合：

- 组合A：看涨期权 + $Ke^{-rT}$现金
- 组合B：看跌期权 + 1股标的资产

到期时两个组合价值均为$\max(S_T, K)$，由无套利原理，当前价值相等：
$$C + Ke^{-rT} = P + S$$
整理即得。∎

### 习题2

计算当$S = K$，$r = 0$时，看涨期权的Delta值。

**解答**：$d_1 = \frac{\sigma\sqrt{T}}{2}$，$\Delta = N(\frac{\sigma\sqrt{T}}{2})$

当$\sigma\sqrt{T} \to 0$时，$\Delta \to 0.5$

### 习题3

解释为什么Vega总是正的。

**解答**：波动率增加会增加标的资产价格的不确定性，从而增加期权的潜在收益，但不增加潜在损失（因为期权买方的损失最多是期权费），所以期权价格随波动率增加而增加。

---

**适用**：docs/25-金融数学/
