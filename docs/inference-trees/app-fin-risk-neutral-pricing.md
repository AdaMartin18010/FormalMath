---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 风险中性定价理论推导链
processed_at: '2026-04-05'
---
# 风险中性定价理论推导链

## 概述
本推理树展示风险中性定价理论的完整数学基础，包括鞅测度存在性、市场完备性、定价表示定理等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 市场框架
        A1[概率空间<br/>Ω, F, P] --> A2[信息流<br/>Fₜ滤子]
        A2 --> A3[适应过程<br/>Sₜ关于Fₜ可测]
        A3 --> A4[资产价格过程<br/>S = Sₜ, Bₜ]
    end
    
    subgraph 套利理论
        A4 --> B1[自融资策略<br/>H = Hₜ, ΔH·S = 0]
        B1 --> B2[套利机会<br/>V₀=0, V_T≥0, P(V_T>0)>0]
        B2 --> B3[一价定律<br/>无套利⇒价格唯一]
    end
    
    subgraph 鞅测度
        B3 --> C1[等价鞅测度Q<br/>Q ~ P]
        C1 --> C2[折现价格是鞅<br/>E_Q[S̃ₜ₊₁|Fₜ] = S̃ₜ]

        C2 --> C3[测度存在性<br/>Dalang-Morton-Willinger]
    end
    
    subgraph 定价表示
        C3 --> D1[或有索取权<br/>X = f(S_T)]
        D1 --> D2[可达性<br/>X = V_T^H]
        D2 --> D3[定价公式<br/>π(X) = E_Q[X̃]]
    end
    
    subgraph 完备市场
        D2 --> E1[唯一鞅测度<br/>|M| = 1]

        E1 --> E2[表示定理<br/>任意X可被复制]
        E2 --> E3[完备市场<br/>Second FTAP]
    end
    
    subgraph 多期扩展
        E3 --> F1[向后归纳<br/>t = T-1,...,0]
        F1 --> F2[美式期权<br/>最优停止问题]
        F2 --> F3[早期执行边界<br/>Snell包络]
    end
    
    style C3 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px
    style D3 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style E3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：金融市场模型

**概率空间**：$(\Omega, \mathcal{F}, P)$

**信息流**：滤子 $\mathbb{F} = \{\mathcal{F}_t\}_{t=0}^T$

**资产价格**：$S = (S^0, S^1, \ldots, S^d)$
- $S^0$：无风险资产，$S^0_t = (1+r)^t$（离散）或 $e^{rt}$（连续）
- $S^i$：风险资产，$i = 1, \ldots, d$

**折现价格**：$\tilde{S}_t = S_t / S^0_t$

### 第二步：无套利条件

**交易策略**：$H = (H^0, H^1, \ldots, H^d)$

**价值过程**：$V_t(H) = H_t \cdot S_t = \sum_{i=0}^d H_t^i S_t^i$

**自融资条件**：
$$H_t \cdot S_{t+1} = H_{t+1} \cdot S_{t+1}$$

即交易只通过资产价值的重新分配实现，无外部资金流入流出。

**套利机会**：策略 $H$ 满足：
1. $V_0(H) = 0$（零初始投资）
2. $V_T(H) \geq 0$，$P$-a.s.
3. $P(V_T(H) > 0) > 0$（正收益概率为正）

### 第三步：第一基本定理

**定理（First Fundamental Theorem of Asset Pricing）**：

市场无套利 $\Leftrightarrow$ 存在等价鞅测度 $Q$

**证明概要**（⇒方向）：
1. 考虑所有可达支付空间 $\mathcal{R}$
2. 定义线性泛函 $\pi: \mathcal{R} \to \mathbb{R}$
3. 应用Hahn-Banach定理扩展到整个空间
4. 由Riesz表示得到鞅测度

### 第四步：等价鞅测度

**定义**：概率测度 $Q$ 称为等价鞅测度，如果：
1. $Q \sim P$（等价性：同零集）
2. 折现价格过程 $\tilde{S}$ 是 $Q$-鞅

$$E_Q[\tilde{S}_{t+1} | \mathcal{F}_t] = \tilde{S}_t, \quad \forall t$$

**经济意义**：在风险中性世界中，所有资产的期望收益率等于无风险利率。

### 第五步：风险中性定价

**或有索取权**：到期支付 $X = f(S_T)$

**可达性**：存在自融资策略 $H$ 使得 $V_T(H) = X$

**定价公式**：
$$\pi_t(X) = S_t^0 \cdot E_Q\left[\frac{X}{S_T^0} \Big| \mathcal{F}_t\right]$$

连续情形（$r$ 为常数）：
$$\pi_t(X) = e^{-r(T-t)} E_Q[X | \mathcal{F}_t]$$

### 第六步：第二基本定理

**定理（Second Fundamental Theorem of Asset Pricing）**：

市场完备（所有或有索取权可达）$\Leftrightarrow$ 等价鞅测度唯一

**完备市场特性**：
- 每个或有索取权可被完美对冲
- 存在唯一的公平价格
- 期权复制策略唯一

### 第七步：美式期权

**最优停止问题**：
$$V_t = \sup_{\tau \in \mathcal{T}_{t,T}} E_Q[e^{-r(\tau-t)} f(S_\tau) | \mathcal{F}_t]$$

**Snell包络**：最小上鞅控制者

**最优执行边界**：$\mathcal{E} = \{(t, S): V(t, S) = f(S)\}$

---

## 离散模型：二叉树

```

        S·u
       /    Cu = max(Su-K, 0)
      S
       \    Cd = max(Sd-K, 0)
        S·d

风险中性概率：q = (e^(rΔt) - d)/(u - d)

期权价格：C = e^(-rΔt)[q·Cu + (1-q)·Cd]

```

---

## 依赖关系图

```

概率论基础
    ↓
随机过程理论 ← 鞅论
    ↓
金融市场模型
    ↓
无套利条件 → 第一基本定理
    ↓
等价鞅测度存在
    ↓
风险中性定价公式
    ↓
完备市场 ← 第二基本定理
    ↓
美式期权定价

```

---

## 关键定理汇总

| 定理 | 陈述 | 意义 |
|------|------|------|
| 第一基本定理 | 无套利 ⇔ 鞅测度存在 | 定价理论基础 |
| 第二基本定理 | 完备 ⇔ 鞅测度唯一 | 对冲完备性 |
| 鞅表示定理 | 鞅可由布朗运动表示 | 复制策略存在 |
| 最优停止定理 | Snell包络刻画 | 美式期权定价 |

---

## 参考

- Harrison, J. M. & Pliska, S. R. (1981). "Martingales and Stochastic Integrals in the Theory of Continuous Trading"
- Delbaen, F. & Schachermayer, W. (2006). *The Mathematics of Arbitrage*
- Shreve, S. E. (2004). *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*
- Duffie, D. (2001). *Dynamic Asset Pricing Theory*

---

*生成时间：2026年4月*
