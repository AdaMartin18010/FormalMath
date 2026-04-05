---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 幂级数性质推导
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 幂级数性质推导

## 概述
本推理树展示从幂级数收敛半径出发，经Abel定理，最终导出幂级数分析性质的完整推理链。

```mermaid
graph TD
    subgraph 收敛半径
        A1[幂级数定义Σaₙxⁿ] --> A2[Cauchy-Hadamard]
        A2 --> A3[R=1/limsupⁿ√|aₙ|]

        A2 --> A4[比值法求R]
        A3 --> A5[收敛区间]
    end
    
    subgraph Abel定理
        A5 --> B1[端点收敛性]
        B1 --> B2[Abel定理]
        B2 --> B3[一致收敛到端点]
    end
    
    subgraph 分析性质
        A3 --> C1[内闭一致收敛]
        C1 --> C2[连续性]
        C1 --> C3[逐项可积]
        C1 --> C4[逐项可微]
    end
    
    subgraph 系数的唯一性
        C2 --> D1[和函数唯一]
        D1 --> D2[系数由导数确定]
        D2 --> D3[aₙ=f⁽ⁿ⁾(0)/n!]
    end
    
    subgraph 运算性质
        C3 --> E1[幂级数加法]
        C3 --> E2[幂级数乘法]
        C3 --> E3[幂级数复合]
    end
    
    subgraph Taylor展开
        D3 --> F1[解析函数]
        F1 --> F2[Taylor展开]
        C4 --> F2
    end
    
    style A3 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style F2 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 核心定理

### Cauchy-Hadamard定理

**定理**：幂级数 $\sum a_n x^n$ 的收敛半径：

$$R = \frac{1}{\limsup_{n \to \infty} \sqrt[n]{|a_n|}}$$

**收敛域**：$(-R, R)$，端点需单独判别

### Abel定理

**定理**：若幂级数在 $x = R$ 收敛，则它在 $[0, R]$ 上一致收敛。

**推论**：和函数在 $x = R$ 左连续

### 逐项运算定理

**定理**：设 $S(x) = \sum a_n x^n$，$|x| < R$：

1. **连续性**：$S(x)$ 在 $(-R, R)$ 连续
2. **可积性**：$\int_0^x S(t)dt = \sum \frac{a_n}{n+1}x^{n+1}$
3. **可微性**：$S'(x) = \sum n a_n x^{n-1}$

**关键性质**：逐项求导/积分后收敛半径不变

### Taylor展开唯一性

**定理**：若 $f(x) = \sum a_n x^n$，则：

$$a_n = \frac{f^{(n)}(0)}{n!}$$

**依赖关系**：

```

收敛半径定义
    ↓
内闭一致收敛
    ↓
逐项运算合法性
    ↓
系数与导数关系
    ↓
Taylor展开

```
