---
msc_primary: 00

  - 00A99
title: 数学×经济学：金融数学的随机分析
processed_at: '2026-04-05'
---
# 数学×经济学：金融数学的随机分析

## 概述

金融数学运用随机分析、偏微分方程和优化理论来研究金融市场中的资产定价、风险管理和投资组合优化。从Black-Scholes期权定价公式到现代风险度量理论，数学为金融实践提供了坚实的理论基础。

---

## 核心思维导图

```mermaid
mindmap
  root((金融数学<br/>Financial Mathematics))
    随机分析基础
      Brown运动
        Wiener过程 W_t
        独立增量
        高斯分布
      随机积分
        Itô积分
        伊藤引理
        二次变差
      SDE
        扩散过程
        dX = μdt + σdW
        解的存在唯一性
      Girsanov定理
        测度变换
        鞅表示
        风险中性
    资产定价
      Black-Scholes
        期权定价公式
        几何Brown运动
        无套利定价
      鞅方法
        等价鞅测度
        风险中性定价
        第一基本定理
      利率模型
        Vasicek模型
        CIR模型
        HJM框架
      信用风险
        违约概率
        CDS定价
        结构化模型
    衍生品定价
      期权类型
        欧式/美式
        奇异期权
        路径依赖
      数值方法
        二叉树
        蒙特卡洛
        有限差分
      希腊字母
        Delta, Gamma
        Theta, Vega
        风险对冲
      波动率
        隐含波动率
        波动率微笑
        局部/随机波动率
    投资组合理论
      Markowitz均值方差
        有效前沿
        最优组合
        两基金分离
      CAPM
        市场均衡
        β系数
        证券市场线
      套利定价
        APT模型
        多因子模型
        线性定价
      效用理论
        期望效用
        风险厌恶
        随机占优
    风险管理
      风险度量
        VaR
        CVaR/ES
        一致性公理
      极值理论
        尾部风险
        GEV分布
        POT方法
      压力测试
        情景分析
        敏感性分析
        模型风险
      资本配置
        经济资本
        RAROC
        风险调整
    高级主题
      不完全市场
        超对冲
        效用无差别定价
        最小熵鞅
      市场微观结构
        订单簿模型
        做市策略
        高频交易
      行为金融
        前景理论
        有限理性
        市场异象

```

---

## 定价理论的数学框架

```mermaid
graph TD
    subgraph 概率框架
        P[真实世界测度 P] --> M[等价鞅测度 Q]
        M --> E[期望定价]
        SDE[SDE dS = μSdt + σSdW] --> BS[Black-Scholes PDE]
    end
    
    subgraph 定价公式
        E --> C[看涨期权 C = e^(-rT)E_Q[max(S_T-K,0)]]
        BS --> PDE[∂V/∂t + ½σ²S²∂²V/∂S² + rS∂V/∂S - rV = 0]
    end
    
    style M fill:#e3f2fd
    style C fill:#e3f2fd
    style BS fill:#e8f5e9

```

---

## Black-Scholes公式

| 变量 | 公式 | 说明 |
|------|------|------|
| 看涨期权 | C = S₀N(d₁) - Ke^(-rT)N(d₂) | d₁,₂ = [ln(S₀/K) + (r±σ²/2)T]/(σ√T) |
| 看跌期权 | P = Ke^(-rT)N(-d₂) - S₀N(-d₁) | 看跌-看涨平价 |
| Delta | ∂C/∂S = N(d₁) | 对冲比率 |
| Gamma | ∂²C/∂S² = n(d₁)/(Sσ√T) | Delta变化率 |
| Theta | ∂C/∂t | 时间衰减 |
| Vega | ∂C/∂σ = S√T n(d₁) | 波动率敏感度 |

---

## 风险度量公理

```mermaid
mindmap
  root((一致性风险度量<br/>Coherent Risk Measures))
    Artzner公理
      单调性
        X ≤ Y ⇒ ρ(X) ≥ ρ(Y)
        较小损失风险较大
      正齐次性
        ρ(λX) = λρ(X)
        比例不变
      平移不变性
        ρ(X+m) = ρ(X) - m
        现金加减少风险
      次可加性
        ρ(X+Y) ≤ ρ(X) + ρ(Y)
        分散降低风险
    常见度量
      VaR
        分位数定义
        不满足次可加性
        监管标准
      CVaR/ES
        尾部条件期望
        一致性
        凸优化
      谱风险
        加权平均
        一般化ES
        风险厌恶函数

```

---

## 投资组合前沿

- **最小方差组合**: min wᵀΣw s.t. wᵀ1=1
- **切线组合**: 夏普比率最大
- **有效前沿**: 给定收益下最小风险
- **两基金定理**: 任何有效组合可由两个基金生成

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数学×经济学 / 交叉学科*
