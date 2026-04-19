---
msc_primary: 00

  - 00A99
title: 序列极限 → 函数极限推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 序列极限 → 函数极限推理树

## 概述
本推理树展示序列极限与函数极限之间的深刻联系，包括Heine定理（序列判别法）及其应用，建立离散与连续之间的桥梁。

```mermaid
graph TD
    subgraph 序列极限基础
        A1[数列极限定义<br/>lim aₙ = L] --> A2[ε-N语言<br/>∀ε>0, ∃N, n>N⇒|aₙ-L|<ε]

        A2 --> A3[序列收敛性质<br/>有界性、唯一性]
        A3 --> A4[单调收敛定理<br/>Monotone Convergence]
        A4 --> A5[Cauchy收敛准则<br/>完备性刻画]
    end
    
    subgraph 子序列理论
        A3 --> B1[子序列定义<br/>aₙₖ, nₖ→∞]
        B1 --> B2[Bolzano-Weierstrass<br/>有界序列有收敛子列]
        B2 --> B3[聚点定理<br/>Accumulation Point]
    end
    
    subgraph Heine定理
        A2 --> C1[Heine定理<br/>函数极限⇔序列极限]
        C1 --> C2[⇒方向: 序列判别法<br/>xₙ→a ⇒ f(xₙ)→L]
        C1 --> C3[⇐方向: 反证构造<br/>构造发散序列]
    end
    
    subgraph 函数极限性质
        C1 --> D1[归结原理<br/>Reduction Principle]
        D1 --> D2[夹逼定理推广<br/>Squeeze for Functions]
        D1 --> D3[Cauchy准则<br/>函数版]
    end
    
    subgraph 单侧极限与序列
        C2 --> E1[右极限序列判别<br/>xₙ→a⁺]
        C2 --> E2[左极限序列判别<br/>xₙ→a⁻]
        E1 --> E3[单调收敛到a的序列<br/>特殊作用]
        E2 --> E3
    end
    
    subgraph 应用与推论
        D2 --> F1[重要极限证明<br/>lim sinx/x = 1]
        D2 --> F2[e的定义<br/>lim(1+1/n)ⁿ]
        D3 --> F3[一致连续性<br/>序列判别法]
        B2 --> F4[紧致性<br/>有限覆盖定理]
    end
    
    style C1 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style A4 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style F1 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px

```

## 核心定理：Heine归结原理

### 定理陈述

设函数 $f$ 在点 $a$ 的去心邻域 $\mathring{U}(a)$ 有定义，则：

$$\lim_{x \to a} f(x) = L \quad \Leftrightarrow \quad \forall \{x_n\} \subset \mathring{U}(a), x_n \to a \text{ 且 } x_n \neq a, \text{有} \lim_{n \to \infty} f(x_n) = L$$

### 证明：⇒ 方向

**假设**：$\lim_{x \to a} f(x) = L$

**证明**：任取序列 $\{x_n\}$ 满足 $x_n \to a$ 且 $x_n \neq a$

由函数极限定义：$\forall \varepsilon > 0, \exists \delta > 0$，当 $0 < |x - a| < \delta$ 时：
$$|f(x) - L| < \varepsilon$$

由 $x_n \to a$：对上述 $\delta > 0, \exists N$，当 $n > N$ 时：
$$|x_n - a| < \delta$$

又因 $x_n \neq a$，故 $0 < |x_n - a| < \delta$

因此当 $n > N$ 时：$|f(x_n) - L| < \varepsilon$

即 $\lim_{n \to \infty} f(x_n) = L$。 ∎

### 证明：⇐ 方向（反证法）

**假设**：对任意满足条件的序列，都有 $f(x_n) \to L$

**反设**：$\lim_{x \to a} f(x) \neq L$

则存在 $\varepsilon_0 > 0$，使得对任意 $\delta > 0$，都存在 $x_\delta$ 满足：
$$0 < |x_\delta - a| < \delta \text{ 但 } |f(x_\delta) - L| \geq \varepsilon_0$$

**构造序列**：取 $\delta_n = \frac{1}{n}$，得到序列 $\{x_n\}$ 满足：
- $0 < |x_n - a| < \frac{1}{n}$（故 $x_n \to a$ 且 $x_n \neq a$）
- $|f(x_n) - L| \geq \varepsilon_0$（故 $f(x_n)$ 不收敛到 $L$）

这与假设矛盾！ ∎

## 推理链详解

### 链1：序列极限基础

**单调收敛定理**：单调有界数列必收敛。

**证明框架**：

```

有界 → 存在上确界/下确界
    ↓
单调递增 → sup{aₙ} 即为极限
单调递减 → inf{aₙ} 即为极限

```

**关键步骤**：设 $A = \sup\{a_n\}$（单调递增情形）

$\forall \varepsilon > 0$，$A - \varepsilon$ 不是上界

故 $\exists N$，使 $a_N > A - \varepsilon$

由单调性，当 $n > N$ 时：$A - \varepsilon < a_N \leq a_n \leq A < A + \varepsilon$

因此 $|a_n - A| < \varepsilon$。 ∎

**依赖**：确界存在定理 ← 实数完备性公理

### 链2：Cauchy收敛准则

**定理**：数列 $\{a_n\}$ 收敛 $\Leftrightarrow$ $\{a_n\}$ 是Cauchy列

$$\forall \varepsilon > 0, \exists N, \forall m,n > N: |a_m - a_n| < \varepsilon$$

**⇒ 方向**：三角不等式直接得
$$|a_m - a_n| \leq |a_m - L| + |L - a_n| < 2\varepsilon$$

**⇐ 方向**：

```

Cauchy列 → 有界 → 有收敛子列
    ↓
子列收敛到L
    ↓
利用Cauchy条件证明整个序列收敛到L

```

### 链3：Bolzano-Weierstrass定理

**定理**：有界数列必有收敛子列。

**证明（区间套法）**：

设 $\{a_n\} \subset [a, b]$（有界）

1. 二分区间，至少有一个子区间包含无穷多项
2. 选取该子区间，继续二分
3. 得到区间套 $[a_n, b_n]$，长度 $b_n - a_n = \frac{b-a}{2^n} \to 0$
4. 由区间套定理，存在唯一 $\xi \in \bigcap [a_n, b_n]$
5. 从每个 $[a_n, b_n]$ 中选取一项 $a_{n_k}$
6. 则 $|a_{n_k} - \xi| \leq b_k - a_k \to 0$

故子列 $\{a_{n_k}\}$ 收敛到 $\xi$。 ∎

### 链4：函数极限Cauchy准则

**定理**：$\lim_{x \to a} f(x)$ 存在 $\Leftrightarrow$ 
$$\forall \varepsilon > 0, \exists \delta > 0, \forall x_1, x_2: 0 < |x_i - a| < \delta \Rightarrow |f(x_1) - f(x_2)| < \varepsilon$$

**证明**：利用Heine定理归结到序列版本

**应用**：证明极限不存在只需找到两个收敛到 $a$ 但函数值极限不同的序列

## 典型应用

### 应用1：证明 $\lim_{x \to 0} \sin\frac{1}{x}$ 不存在

**构造序列**：
- $x_n = \frac{1}{n\pi} \to 0$，$\sin\frac{1}{x_n} = \sin(n\pi) = 0$
- $y_n = \frac{1}{2n\pi + \frac{\pi}{2}} \to 0$，$\sin\frac{1}{y_n} = 1$

两序列函数值极限不同，故原极限不存在。 ∎

### 应用2：证明 $\lim_{x \to 0} \frac{\sin x}{x} = 1$

**序列法证明**：

首先证明对于 $0 < x < \frac{\pi}{2}$：$\cos x < \frac{\sin x}{x} < 1$（单位圆面积比较）

任取 $x_n \to 0^+$，由夹逼定理：$\frac{\sin x_n}{x_n} \to 1$

同理可证左极限。

由Heine定理，函数极限存在且等于1。 ∎

### 应用3：连续性序列判别

**定理**：$f$ 在 $a$ 点连续 $\Leftrightarrow$ 对任意 $x_n \to a$，有 $f(x_n) \to f(a)$

**注意**：此处 $x_n$ 可以等于 $a$（与极限情形的区别）

## 依赖关系总图

```

实数完备性
    ├──→ 确界存在定理
    │       └──→ 单调收敛定理
    │               └──→ 级数收敛判别
    │
    └──→ 区间套定理
            ├──→ Bolzano-Weierstrass
            │       └──→ 聚点定理
            │               └──→ Heine定理(⇐方向)
            │
            └──→ Cauchy准则(序列版)
                    └──→ Cauchy准则(函数版)
                            └──→ 一致连续Cauchy判别

Heine定理
    ├──→ 归结原理
    │       ├──→ 函数极限性质证明简化
    │       └──→ 不存在的判定方法
    │
    └──→ 连续性序列判别
            └──→ 可微性序列判别

```

## 关键引理与复杂度

| 引理/定理 | 核心思想 | 复杂度 | 依赖 |
|-----------|----------|--------|------|
| 三角不等式 | 距离控制 | ★☆☆ | 无 |
| 确界存在 | 有界集合的"边界" | ★★☆ | 完备性 |
| 单调收敛 | 单调+有界→收敛 | ★★☆ | 确界存在 |
| Bolzano-Weierstrass | 无限→有收敛子列 | ★★★ | 区间套 |
| Heine定理 | 离散刻画连续 | ★★★ | Cauchy+B-W |
| Cauchy准则 | 自完备性 | ★★★ | B-W+三角不等式 |

## 参考

- 《数学分析》华东师大，第二章、第三章
- 《数学分析教程》常庚哲，第二章
- 《Understanding Analysis》Abbott, Chapter 2
