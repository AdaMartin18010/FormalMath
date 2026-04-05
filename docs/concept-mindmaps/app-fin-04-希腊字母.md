---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 希腊字母 - 思维导图
processed_at: '2026-04-05'
---
# 希腊字母 - 思维导图

## 概述

希腊字母(Greeks)是期权价格对各种参数的敏感性度量，是金融衍生品风险管理和对冲策略的核心工具。它们分别度量期权价格对标的资产价格、时间、波动率、利率等因素的变化率，帮助交易员理解和控制投资组合的风险暴露。

---

## 核心思维导图

```mermaid
mindmap
  root((希腊字母<br/>Greeks))
    一阶希腊字母
      Delta Δ
        定义: ∂V/∂S
        含义: 股价敏感性
        应用: Delta对冲
        性质: 0 ≤ Δ ≤ 1 (看涨)
      Theta Θ
        定义: ∂V/∂t
        含义: 时间衰减
        应用: 时间价值分析
        通常: Θ < 0
      Vega ν
        定义: ∂V/∂σ
        含义: 波动率敏感性
        应用: 波动率交易
        性质: ν > 0
      Rho ρ
        定义: ∂V/∂r
        含义: 利率敏感性
        应用: 利率风险对冲
    二阶希腊字母
      Gamma Γ
        定义: ∂²V/∂S²
        含义: Delta变化率
        应用: Gamma对冲
        性质: Γ > 0 (多头)
      Vanna
        定义: ∂²V/∂S∂σ
        含义: Delta对波动率敏感
      Volga/Vomma
        定义: ∂²V/∂σ²
        含义: Vega对波动率敏感
      Charm
        定义: ∂²V/∂S∂t
        Delta时间衰减
      Veta
        定义: ∂²V/∂σ∂t
        Vega时间衰减
    高阶希腊字母
      Speed
        ∂³V/∂S³
      Zomma
        ∂³V/∂S²∂σ
      Color
        ∂³V/∂S²∂t
      Ultima
        ∂³V/∂σ³

```

---

## BS模型希腊字母公式

```mermaid
graph TD
    subgraph 一阶Greeks
        A[Delta Δ = N(d₁)] --> B[看涨: 0→1, 看跌: -1→0]
        C[Theta Θ = -SN'(d₁)σ/(2√T) - rKe⁻ʳᵀN(d₂)] --> D[时间衰减]
        E[Vega ν = SN'(d₁)√T] --> F[波动率敏感]
        G[Rho ρ = KTe⁻ʳᵀN(d₂)] --> H[利率敏感]
    end
    
    subgraph 二阶Greeks
        I[Gamma Γ = N'(d₁)/(Sσ√T)] --> J[Delta凸性]
        K[Vanna = ν(1-d₁/σ√T)/S] --> L[Skew暴露]
        M[Volga = ν·d₁·d₂/σ] --> N[Vol convexity]
    end
    
    subgraph 符号说明
        O[N(·): 标准正态CDF] --> P[N'(·): 标准正态PDF]
    end
    
    style A fill:#e3f2fd
    style E fill:#e3f2fd
    style I fill:#fff3e0

```

---

## 希腊字母特性表

| 希腊字母 | 定义 | 看涨期权BS公式 | 看跌期权BS公式 | 符号 | 风险暴露 |
|----------|------|----------------|----------------|------|----------|
| Delta (Δ) | ∂V/∂S | N(d₁) | N(d₁) - 1 | + (看涨) | 方向风险 |
| Gamma (Γ) | ∂²V/∂S² | N'(d₁)/(Sσ√T) | 相同 | + | 凸性风险 |
| Theta (Θ) | ∂V/∂t | 公式复杂 | 公式复杂 | - (多头) | 时间衰减 |
| Vega (ν) | ∂V/∂σ | SN'(d₁)√T | 相同 | + | 波动率风险 |
| Rho (ρ) | ∂V/∂r | KTe⁻ʳᵀN(d₂) | -KTe⁻ʳᵀN(-d₂) | + (看涨) | 利率风险 |

---

## 对冲策略

```mermaid
mindmap
  root((对冲策略))
    Delta对冲
      原理
        使组合Δ = 0
        消除一阶价格风险
      实施
        Δ = ∂V/∂S
        持有-Δ份标的资产
      再平衡
        离散对冲成本
        Gamma影响
    Gamma对冲
      目的
        减少再平衡频率
        控制Delta变化
      方法
        使用其他期权
        构造Gamma中性
    Vega对冲
      目标
        对冲波动率风险
      挑战
        波动率不可直接交易
        隐含波动率vs实际波动率
    多希腊字母对冲
      Delta-Gamma对冲
      Delta-Vega对冲
      全希腊字母对冲

```

---

## 希腊字母的动态行为

```mermaid
graph TD
    subgraph 价内vs价外
        A[深度价内] --> B[Δ ≈ 1, Γ ≈ 0]
        C[平价附近] --> D[Δ ≈ 0.5, Γ最大]
        E[深度价外] --> F[Δ ≈ 0, Γ ≈ 0]
    end
    
    subgraph 时间影响
        G[到期日长] --> H[Vega大, Gamma小]
        I[到期日近] --> J[Vega小, Gamma大]
    end
    
    subgraph 波动率影响
        K[高波动率] --> L[Gamma平缓]
        M[低波动率] --> N[Gamma尖锐]
    end
    
    style D fill:#fff3e0
    style J fill:#fff3e0

```

---

## 风险度量与监控

```mermaid
mindmap
  root((风险管理))
    希腊字母限额
      Delta限额
        方向风险上限
      Gamma限额
        凸性风险上限
      Vega限额
        波动率风险上限
    情景分析
      价格情景
        股价大幅变动
        Delta和Gamma影响
      波动率情景
        波动率跳变
        Vega和Volga影响
      时间情景
        临近到期
        Theta和Charm影响
    P&L解释
      P&L = Δ·ΔS + ½Γ·(ΔS)² + ν·Δσ + Θ·Δt + ...
      希腊字母归因
      对冲效率评估

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[Black-Scholes模型] --> B[期权定价公式]
    end
    
    subgraph L2[一阶Greeks]
        B --> C[Delta]
        C --> D[Gamma]
        D --> E[Theta/Vega/Rho]
    end
    
    subgraph L3[应用]
        E --> F[Delta对冲]
        F --> G[Gamma对冲]
        G --> H[风险管理]
    end
    
    subgraph L4[进阶]
        H --> I[高阶Greeks]
        I --> J[复杂产品]
    end
    
    style C fill:#e3f2fd
    style D fill:#e3f2fd
    style F fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $\Delta_{call} = N(d_1)$ | 看涨Delta |
| $\Delta_{put} = N(d_1) - 1$ | 看跌Delta |
| $\Gamma = \frac{N'(d_1)}{S\sigma\sqrt{T}}$ | Gamma |
| $\nu = S N'(d_1) \sqrt{T}$ | Vega |
| $\Theta_{call} = -\frac{S N'(d_1) \sigma}{2\sqrt{T}} - rKe^{-rT}N(d_2)$ | 看涨Theta |
| $\rho_{call} = K T e^{-rT} N(d_2)$ | 看涨Rho |
| $\text{Vanna} = \frac{\nu}{S}(1 - \frac{d_1}{\sigma\sqrt{T}})$ | Vanna |
| $\text{Volga} = \frac{\nu \cdot d_1 \cdot d_2}{\sigma}$ | Volga |

---

## 应用领域

- **期权做市**: 管理库存风险，设定买卖报价
- **结构化产品**: 设计和对冲复杂衍生品
- **风险管理**: 风险限额设置，VaR计算
- **波动率交易**: Vega/Volga策略，波动率套利
- **算法交易**: 自动化对冲策略

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 金融数学 / 思维导图*
