---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 利率模型 - 思维导图

## 概述

利率模型是描述利率随机演化的数学框架，是固定收益证券、利率衍生品定价和风险管理的核心工具。从早期的均衡模型到现代的无套利模型，利率模型的发展极大地推动了固定收益金融市场的发展。

---

## 核心思维导图

```mermaid
mindmap
  root((利率模型<br/>Interest Rate Models))
    短期利率模型
      单因子模型
        Vasicek模型
          dr = θ(μ-r)dt + σdW
          均值回归
          正态分布(可能负利率)
        CIR模型
          dr = θ(μ-r)dt + σ√rdW
          平方根扩散
          非负利率
        Ho-Lee模型
          无套利模型
          时间依赖漂移
      多因子模型
        两因子CIR
        长短期利率分离
        相关结构
    无套利模型
      Ho-Lee
        dr = θ(t)dt + σdW
        完全拟合期限结构
      Hull-White
        dr = (θ(t)-ar)dt + σdW
        Vasicek扩展
      Black-Derman-Toy
        对数正态
        离散时间
    市场模型
      HJM框架
        远期利率驱动
        无套利条件
        漂移限制
      LIBOR市场模型
        离散远期利率
        对数正态假设
        Black公式兼容
    期限结构
      零息债券
        P(t,T) = E[e^(-∫ₜᵀrₛds)]
      远期利率
        f(t,T) = -∂lnP/∂T
      收益率曲线
        y(t,T) = -lnP/(T-t)

```

---

## 短期利率模型比较

```mermaid
graph TD
    subgraph Vasicek
        A[dr = θ(μ-r)dt + σdW] --> B[均值回归速度θ]
        B --> C[长期均值μ]
        C --> D[正态分布]
        D --> E[可能负利率]
    end
    
    subgraph CIR
        F[dr = θ(μ-r)dt + σ√rdW] --> G[平方根项]
        G --> H[保证r≥0]
        H --> I[非中心χ²分布]
    end
    
    subgraph Hull-White
        J[dr = (θ(t)-ar)dt + σdW] --> K[时间依赖漂移]
        K --> L[完全拟合市场数据]
        L --> M[Vasicek扩展]
    end
    
    style A fill:#e3f2fd
    style F fill:#fff3e0
    style J fill:#e8f5e9

```

---

## 模型特性对比

| 模型 | SDE形式 | 利率非负 | 解析债券公式 | 解析期权公式 | 拟合期限结构 |
|------|---------|----------|--------------|--------------|--------------|
| Vasicek | dr = θ(μ-r)dt + σdW | ✗ | ✓ | ✓ | 部分拟合 |
| CIR | dr = θ(μ-r)dt + σ√rdW | ✓ | ✓ | ✓ | 部分拟合 |
| Ho-Lee | dr = θ(t)dt + σdW | ✗ | ✓ | ✓ | 完全拟合 |
| Hull-White | dr = (θ(t)-ar)dt + σdW | ✗ | ✓ | ✓ | 完全拟合 |
| Black-Karasinski | dlnr = (...)dt + σdW | ✓ | ✗ | ✗ | 完全拟合 |

---

## HJM框架

```mermaid
mindmap
  root((HJM框架))
    基本概念
      远期利率
        f(t,T): t时看到的T时瞬时利率
      即期利率
        r(t) = f(t,t)
      零息债券
        P(t,T) = exp(-∫ₜᵀf(t,s)ds)
    HJM方程
      一般形式
        df(t,T) = α(t,T)dt + σ(t,T)dW
      无套利条件
        α(t,T) = σ(t,T)∫ₜᵀσ(t,s)ds
        漂移完全由波动率决定
    模型实现
      高斯HJM
        确定性波动率
        解析可处理
      马尔可夫限制
        多因子扩展
        计算效率
    与短期利率关系
      单因子等价
        特定波动率结构
        对应Hull-White
      多因子优势
        更丰富的期限结构动态

```

---

## LIBOR市场模型

```mermaid
graph LR
    subgraph 离散远期利率
        A[Lᵢ(t) = L(t;Tᵢ,Tᵢ₊₁)] --> B[简单复利远期]
        B --> C[可观测市场数据]
    end
    
    subgraph 对数正态假设
        D[dLᵢ/Lᵢ = μᵢdt + σᵢdWᵢ]
        E[Black公式兼容]
    end
    
    subgraph 测度选择
        F[远期测度<br/>Tᵢ₊₁-远期]
        G[Spot LIBOR测度]
        H[互换测度]
    end
    
    subgraph 定价应用
        I[Cap/Floor: 解析解]
        J[Swaption: 近似解]
        K[CMS产品: 数值方法]
    end
    
    C --> D
    D --> E
    F --> I
    F --> J
    
    style D fill:#e3f2fd
    style E fill:#fff3e0

```

---

## 期限结构数学

```mermaid
mindmap
  root((期限结构))
    利率类型
      短期利率
        r(t) = f(t,t)
      远期利率
        f(t,T) = -∂lnP(t,T)/∂T
      即期利率
        y(t,T) = -lnP(t,T)/(T-t)
      互换利率
        固定端现值=浮动端现值
    债券定价
      零息债券
        P(t,T) = E[e^(-∫ₜᵀrₛds)|ℱₜ]

      付息债券
        ∑cᵢP(t,Tᵢ) + NP(t,Tₙ)
      浮动利率债券
        面值附近波动
    利率衍生品
      利率上限/下限
        看涨/看跌期权组合
      互换期权
        进入互换的权利
      结构化产品
        复杂收益结构

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[利率期限结构] --> B[零息债券]
        B --> C[远期利率]
    end
    
    subgraph L2[均衡模型]
        C --> D[Vasicek模型]
        D --> E[CIR模型]
    end
    
    subgraph L3[无套利模型]
        E --> F[Ho-Lee模型]
        F --> G[Hull-White模型]
        G --> H[HJM框架]
    end
    
    subgraph L4[市场模型]
        H --> I[LIBOR市场模型]
        I --> J[多因子扩展]
    end
    
    style D fill:#e3f2fd
    style G fill:#fff3e0
    style H fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $P(t,T) = E[e^{-\int_t^T r_s ds} \mid \mathcal{F}_t]$ | 零息债券价格 |
| $f(t,T) = -\frac{\partial \ln P(t,T)}{\partial T}$ | 瞬时远期利率 |
| $y(t,T) = -\frac{\ln P(t,T)}{T-t}$ | 到期收益率 |
| $df(t,T) = \sigma(t,T)\int_t^T \sigma(t,s)ds \cdot dt + \sigma(t,T)dW$ | HJM方程 |
| $A(t,T)e^{-B(t,T)r(t)}$ | 仿射债券公式 |
| $L(t;T_i,T_{i+1}) = \frac{1}{\delta}\left(\frac{P(t,T_i)}{P(t,T_{i+1})}-1\right)$ | LIBOR利率 |

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 金融数学 / 思维导图*
