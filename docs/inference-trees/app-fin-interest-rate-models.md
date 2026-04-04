---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 利率模型推导链

## 概述
本推理树展示利率期限结构模型的数学基础，包括短期利率模型（Vasicek、CIR）、HJM框架、LIBOR市场模型等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 利率基础
        A1[即期利率曲线<br/>r(t,T)] --> A2[远期利率<br/>f(t,T)]
        A2 --> A3[瞬时利率<br/>rₜ = f(t,t)]
        A3 --> A4[零息债券<br/>P(t,T)]
    end
    
    subgraph 短期利率模型
        A3 --> B1[一般SDE<br/>dr = μdt + σdW]
        B1 --> B2[Vasicek模型<br/>dr = κ(θ-r)dt + σdW]
        B1 --> B3[CIR模型<br/>dr = κ(θ-r)dt + σ√r dW]
        B1 --> B4[Ho-Lee模型<br/>dr = θdt + σdW]
        B1 --> B5[Hull-White模型<br/>dr = κ(θ-r)dt + σdW]
    end
    
    subgraph 仿射期限结构
        B2 --> C1[债券定价PDE<br/>∂P/∂t + μ∂P/∂r + ½σ²∂²P/∂r² = rP]
        B3 --> C1
        C1 --> C2[仿射解形式<br/>P(t,T) = exp(A-B·r)]
        C2 --> C3[Riccati方程<br/>A'和B'的ODE系统]
    end
    
    subgraph HJM框架
        A2 --> D1[远期利率动态<br/>df = αdt + σdW]
        D1 --> D2[无套利条件<br/>α = σ·∫σds]
        D2 --> D3[HJM漂移条件<br/>漂移由波动率决定]
        D3 --> D4[测度不变性<br/>波动率测度无关]
    end
    
    subgraph LIBOR市场模型
        D4 --> E1[离散远期利率<br/>Fₖ(t)]
        E1 --> E2[对数正态假设<br/>dF/F = μdt + σdW]
        E2 --> E3[Black公式<br/>Caplet定价]
        E3 --> E4[互换测度<br/>互换利率鞅性]
    end
    
    C3 --> F1[利率衍生品<br/>债券期权、Cap、Floor]
    E4 --> F1
    F1 --> F2[数值方法<br/>树方法、蒙特卡洛]
    
    style B2 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style B3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style D3 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style C2 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px

```

---

## 核心推导详解

### 第一步：利率曲线基础

**即期利率**：$r(t, T)$ 表示 $t$ 时刻投资到 $T$ 时刻的收益率

$$P(t, T) = \exp(-r(t, T) \cdot (T-t))$$

**远期利率**：$f(t, T)$ 表示 $t$ 时刻约定的 $T$ 时刻瞬时利率

$$f(t, T) = -\frac{\partial \ln P(t, T)}{\partial T}$$

**瞬时短期利率**：$r_t = f(t, t)$

**关系式**：
$$P(t, T) = \exp\left(-\int_t^T f(t, s) ds\right)$$

### 第二步：Vasicek模型

**随机微分方程**：
$$dr_t = \kappa(\theta - r_t)dt + \sigma dW_t$$

其中：
- $\kappa$：均值回归速度
- $\theta$：长期均值
- $\sigma$：波动率

**解的形式**：
$$r_t = r_0 e^{-\kappa t} + \theta(1 - e^{-\kappa t}) + \sigma \int_0^t e^{-\kappa(t-s)} dW_s$$

**统计性质**：
- $E[r_t] = r_0 e^{-\kappa t} + \theta(1 - e^{-\kappa t})$
- $\text{Var}(r_t) = \frac{\sigma^2}{2\kappa}(1 - e^{-2\kappa t})$
- 平稳分布：$\mathcal{N}(\theta, \frac{\sigma^2}{2\kappa})$

**特点**：
- ✓ 解析可解
- ✓ 均值回归
- ✗ 利率可能为负

### 第三步：CIR模型

**随机微分方程**：
$$dr_t = \kappa(\theta - r_t)dt + \sigma\sqrt{r_t} dW_t$$

**特点**：
- 波动率与利率水平相关（平方根过程）
- 利率非负（Feller条件：$2\kappa\theta \geq \sigma^2$）
- 非中心卡方分布

**债券定价**：
$$P(t, T) = A(t, T) \exp(-B(t, T) \cdot r_t)$$

其中 $A$ 和 $B$ 满足Riccati方程。

### 第四步：仿射期限结构

**仿射模型定义**：零息债券价格具有形式
$$P(t, T) = \exp(A(t, T) - B(t, T) \cdot r_t)$$

**Vasicek模型的显式解**：

$$B(t, T) = \frac{1 - e^{-\kappa(T-t)}}{\kappa}$$

$$A(t, T) = \left(\theta - \frac{\sigma^2}{2\kappa^2}\right)(B - (T-t)) - \frac{\sigma^2 B^2}{4\kappa}$$

### 第五步：HJM框架

**远期利率动态**：
$$df(t, T) = \alpha(t, T)dt + \sigma(t, T) \cdot dW_t$$

**关键推导**：债券价格满足
$$\frac{dP(t, T)}{P(t, T)} = r_t dt - \left(\int_t^T \sigma(t, s)ds\right) \cdot dW_t$$

**无套利条件（HJM漂移条件）**：
$$\alpha(t, T) = \sigma(t, T) \cdot \int_t^T \sigma(t, s)ds$$

**意义**：在风险中性测度下，远期利率的漂移完全由波动率结构决定。

### 第六步：LIBOR市场模型

**离散远期LIBOR利率**：
$$F_k(t) = \frac{1}{\tau_k}\left(\frac{P(t, T_{k-1})}{P(t, T_k)} - 1\right)$$

**市场模型假设**：在 $T_k$-远期测度下
$$\frac{dF_k(t)}{F_k(t)} = \sigma_k(t) \cdot dW_t^{T_k}$$

**Black公式应用**：
$$\text{Caplet}_k(0) = \tau_k P(0, T_k) \cdot \text{Black}(K, F_k(0), \sigma_k^{\text{imp}})$$

---

## 模型对比

| 特性 | Vasicek | CIR | Ho-Lee | Hull-White | HJM |
|------|---------|-----|--------|------------|-----|
| 均值回归 | ✓ | ✓ | ✗ | ✓ | - |
| 利率非负 | ✗ | ✓ | ✗ | ✗ | - |
| 解析债券 | ✓ | ✓ | ✓ | ✓ | ✓ |
| 校准灵活性 | 低 | 低 | 中 | 高 | 高 |
| 多因子扩展 | 难 | 难 | 中 | 中 | 易 |

---

## 依赖关系图

```

随机微分方程理论
    ↓
利率曲线基础
    ↓
短期利率模型 ← 均值回归过程
    ↓
仿射期限结构 ← PDE方法
    ↓
HJM框架 ← 远期利率方法
    ↓
LIBOR市场模型 ← Black公式一致性
    ↓
利率衍生品定价

```

---

## 关键公式汇总

| 名称 | 公式 | 应用 |
|------|------|------|
| Vasicek债券 | $P = \exp(A - Br)$ | 零息债券定价 |
| CIR债券 | 非中心卡方分布矩母函数 | 非负利率债券 |
| HJM漂移 | $\alpha = \sigma \int \sigma$ | 无套利约束 |
| Black公式 | $F \cdot N(d_1) - K \cdot N(d_2)$ | Caplet定价 |

---

## 参考

- Vasicek, O. (1977). "An Equilibrium Characterization of the Term Structure"
- Cox, J., Ingersoll, J., & Ross, S. (1985). "A Theory of the Term Structure of Interest Rates"
- Heath, D., Jarrow, R., & Morton, A. (1992). "Bond Pricing and the Term Structure of Interest Rates"
- Brace, A., Gatarek, D., & Musiela, M. (1997). "The Market Model of Interest Rate Dynamics"
- Andersen, L. & Piterbarg, V. (2010). *Interest Rate Modeling*

---

*生成时间：2026年4月*
