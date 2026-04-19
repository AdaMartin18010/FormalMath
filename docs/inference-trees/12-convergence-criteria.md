---
msc_primary: 00

  - 00A99
title: 收敛判别法决策链
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 收敛判别法决策链

## 概述
本推理树展示数项级数各种收敛判别法之间的逻辑关系，形成完整的收敛性判定决策树。

```mermaid
graph TD
    subgraph 基本定义
        A1[级数定义Σaₙ] --> A2[部分和Sₙ]
        A2 --> A3[收敛定义]
        A3 --> A4[必要条件aₙ→0]
    end
    
    subgraph 正项级数判别
        A3 --> B1[正项级数]
        B1 --> B2[比较判别法]
        B2 --> B3[比值判别法]
        B2 --> B4[根值判别法]
        B1 --> B5[积分判别法]
        B1 --> B6[p-级数标准]
    end
    
    subgraph 一般项级数
        A3 --> C1[交错级数]
        C1 --> C2[Leibniz判别法]
        A3 --> C3[绝对收敛]
        C3 --> C4[条件收敛]
    end
    
    subgraph 精细判别
        B3 --> D1[Raabe判别法]
        B3 --> D2[Gauss判别法]
        B2 --> D3[对数判别法]
    end
    
    subgraph 一致收敛
        C3 --> E1[函数项级数]
        E1 --> E2[Weierstrass判别]
        E1 --> E3[Abel判别法]
        E1 --> E4[Dirichlet判别法]
    end
    
    style B2 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style C3 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 核心判别法

### 正项级数判别层次

```

必要条件检验(aₙ→0)
    ↓ 通过
比较判别法(找标准级数)
    ├── 比值判别法(lim aₙ₊₁/aₙ)
    │       ├── =1失效→Raabe
    │       └── 结果明确
    ├── 根值判别法(lim ⁿ√aₙ)
    │       └── 最强（与比值关系）
    └── 积分判别法(单调函数)

```

### 关键定理

**比较判别法**：$0 \leq a_n \leq b_n$，则
- $\sum b_n$ 收敛 ⇒ $\sum a_n$ 收敛
- $\sum a_n$ 发散 ⇒ $\sum b_n$ 发散

**比值判别法(D'Alembert)**：$\lim \frac{a_{n+1}}{a_n} = \rho$
- $\rho < 1$：收敛
- $\rho > 1$：发散
- $\rho = 1$：不确定

**根值判别法(Cauchy)**：$\limsup \sqrt[n]{a_n} = \rho$
- 结论同比值判别法
- 适用范围更广

**Leibniz判别法**：$a_n \downarrow 0$，则 $\sum (-1)^n a_n$ 收敛

### 判别法强度比较

$$\text{根值} \geq \text{比值} \geq \text{Raabe}$$

等号成立条件：极限存在时
