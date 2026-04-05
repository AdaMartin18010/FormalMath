---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 导数定义 → 中值定理家族推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 导数定义 → 中值定理家族推理树

## 概述
本推理树展示从导数定义出发，经Fermat定理、Rolle定理，最终导出微分中值定理家族的完整推理链。

```mermaid
graph TD
    subgraph 导数定义
        A1[差商定义] --> A2[导数定义]
        A2 --> A3[几何意义]
        A2 --> A4[单侧导数]
        A4 --> A5[可微⇒连续]
    end
    
    subgraph Fermat定理
        A2 --> B1[Fermat定理]
        B1 --> B2[内点极值f'=0]
    end
    
    subgraph Rolle定理
        B2 --> C1[Rolle定理]
        C1 --> C2[f(a)=f(b)⇒存在f'(ξ)=0]
    end
    
    subgraph Lagrange中值
        C1 --> D1[Lagrange MVT]
        D1 --> D2[f(b)-f(a)=f'(ξ)(b-a)]
    end
    
    subgraph Cauchy中值
        D1 --> E1[Cauchy MVT]
        E1 --> E2[双函数中值]
    end
    
    subgraph 中值定理推论
        D2 --> F1[单调性判定]
        D2 --> F2[常数判定]
        E2 --> F3[LHopital法则]
    end
    
    style D1 fill:#e1f5ff,stroke:#01579b,stroke-width:3px

```

## 推理步骤详解

### 第一步：导数定义

**定义**：函数 $f$ 在点 $x_0$ 可导，若极限存在：

$$f'(x_0) = \lim_{\Delta x \to 0} \frac{f(x_0 + \Delta x) - f(x_0)}{\Delta x}$$

### 第二步：Fermat定理

**定理**：若 $f$ 在 $x_0$ 可导且 $x_0$ 是极值点，则 $f'(x_0) = 0$。

### 第三步：Rolle定理

**定理**：设 $f$ 在 $[a, b]$ 连续，在 $(a, b)$ 可导，$f(a) = f(b)$，则存在 $\xi \in (a, b)$ 使 $f'(\xi) = 0$。

### 第四步：Lagrange中值定理

**定理**：设 $f$ 在 $[a, b]$ 连续，在 $(a, b)$ 可导，则存在 $\xi \in (a, b)$：

$$f(b) - f(a) = f'(\xi)(b - a)$$

**证明**：构造 $F(x) = f(x) - \frac{f(b)-f(a)}{b-a}(x-a)$，应用Rolle定理。

### 第五步：Cauchy中值定理

**定理**：设 $f, g$ 在 $[a, b]$ 连续，在 $(a, b)$ 可导，$g'(x) \neq 0$，则存在 $\xi \in (a, b)$：

$$\frac{f(b)-f(a)}{g(b)-g(a)} = \frac{f'(\xi)}{g'(\xi)}$$

### 第六步：L'Hôpital法则

由Cauchy中值定理导出，用于计算不定式极限。

## 依赖关系

```

导数定义
    ↓
Fermat定理 ← 极限保号性
    ↓
Rolle定理 ← 极值定理
    ↓
Lagrange中值
    ↓
Cauchy中值 ← 参数化技巧
    ↓
L'Hôpital法则

```
