---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 微积分基本定理推导
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 微积分基本定理推导

## 概述
本推理树展示微积分基本定理的完整推导，包括第一基本定理（积分求导）和第二基本定理（Newton-Leibniz公式）。

```mermaid
graph TD
    subgraph 变上限积分
        A1[定义F(x)=∫ₐˣf(t)dt] --> A2[积分连续性]
        A2 --> A3[变上限积分性质]
    end
    
    subgraph 第一基本定理
        A1 --> B1[f连续条件]
        B1 --> B2[F'(x)=f(x)]
        B2 --> B3[积分求导互逆]
    end
    
    subgraph 原函数存在
        B2 --> C1[连续函数有原函数]
        C1 --> C2[原函数族结构]
        C2 --> C3[F(x)+C]
    end
    
    subgraph 第二基本定理
        C1 --> D1[Newton-Leibniz公式]
        D1 --> D2[∫ₐᵇf(x)dx=F(b)-F(a)]
        D2 --> D3[计算简化]
    end
    
    subgraph 分部积分
        D2 --> E1[乘积法则积分]
        E1 --> E2[∫udv=uv-∫vdu]
    end
    
    subgraph 换元积分
        D2 --> F1[链式法则积分]
        F1 --> F2[∫f(φ)φ'dx]
    end
    
    style B2 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style D1 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 核心定理

### 第一基本定理

**定理**：设 $f$ 在 $[a,b]$ 连续，$F(x) = \int_a^x f(t)dt$，则：

$$F'(x) = f(x), \quad \forall x \in [a,b]$$

**证明**：
$$\frac{F(x+h)-F(x)}{h} = \frac{1}{h}\int_x^{x+h} f(t)dt$$

由积分中值定理，存在 $\xi$ 在 $x$ 与 $x+h$ 之间：
$$= f(\xi) \to f(x) \text{ (当 } h \to 0 \text{)}$$

### 第二基本定理（Newton-Leibniz）

**定理**：设 $f$ 在 $[a,b]$ 连续，$F$ 是 $f$ 的原函数，则：

$$\int_a^b f(x)dx = F(b) - F(a)$$

**证明**：设 $G(x) = \int_a^x f(t)dt$，则 $G'(x) = f(x) = F'(x)$

故 $G(x) - F(x) = C$（常数）

令 $x = a$：$G(a) = 0$，故 $C = -F(a)$

令 $x = b$：$\int_a^b f = G(b) = F(b) + C = F(b) - F(a)$ ∎

## 依赖关系

```

积分定义
    ↓
积分中值定理
    ↓
第一基本定理
    ↓
原函数存在性
    ↓
第二基本定理 ← Lagrange中值

```
