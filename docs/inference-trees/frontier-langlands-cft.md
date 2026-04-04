---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# Langlands纲领：类域论到Langlands对应推理树

## 概述

本推理树展示从经典类域论到Langlands纲领的深刻推广，揭示数论与表示论之间的神秘联系。

## 推理树

```mermaid
graph TD
    A[Langlands纲领] --> B[类域论基础]
    B --> B1[Abel扩张理论]<-->B2[局部/整体类域论]
    B --> B3[Artin互反律]<-->B4[Gal^ab ≅ C_K]
    
    B --> C[高维推广]
    C --> C1[非Abel扩张]<-->C2[n维表示]
    C --> C3[自守形式]<-->C4[GLn上的函数]
    
    A --> D[局部Langlands对应]
    D --> D1[p进域上的对应]<-->D2[GLnK ↔ WD_K]
    D --> D3[Galois表示]<-->D4[Weil群表示]
    
    D --> E[局部分类]
    E --> E1[不可约可容许表示]<-->E2[WD表示]
    E --> E3[L因子与ε因子]<-->E4[局部对应保持]
    
    A --> F[整体Langlands对应]
    F --> F1[整体Galois表示]<-->F2[GalQ̄/Q表示]
    F --> F3[自守尖点表示]<-->F4[GLnAQ的表示]
    
    F --> G[函子性原理]
    G --> G1[群同态G→H]<-->G2[表示提升Lifting]
    G --> G3[自守L函数]<-->G4[Euler积分解]
    
    H[几何实现] --> H1[Shimura簇]<-->H2[特殊点与Galois作用]
    H --> H3[Shtuka]<-->H4[Drinfeld意义下的对应]
    
    I[应用领域] --> I1[Fermat大定理]<-->I2[Wiles证明]
    I --> I3[Serre猜想]<-->I4[2维Galois表示来源]
    
    J[未解问题] --> J1[Langlands函子性]<-->J2[一般群上的对应]
    J --> J3[几何Langlands]<-->J4[代数曲线上的对应]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#f96,stroke:#333
    style E fill:#fbb,stroke:#333
    style F fill:#fdd,stroke:#333
    style G fill:#fcc,stroke:#333
    style H fill:#f99,stroke:#333
    style I fill:#f88,stroke:#333
    style J fill:#f77,stroke:#333

```

## 核心概念详解

### 1. 类域论回顾

**局部类域论**：对于p进域K，有Artin同构

```

K^× ≅ W_K^ab

```

**整体类域论**：对于数域K，有

```

GalK^ab/K ≅ C_K/K̄^×

```

### 2. 局部Langlands对应

对于p进域K，存在双射：

```

{GLnK的不可约可容许表示} ↔ {WD_K的n维Frobenius半单表示}

```

其中WD_K = Weil-Deligne群。

### 3. 整体Langlands对应

猜想：存在对应

```

{GLnAQ的尖点自守表示} ↔ {GalQ̄/Q的n维不可约表示}

```

## 重要定理

| 定理 | 陈述 | 证明者 |
|------|------|--------|
| 局部对应n=1 | GL₁对应 | Lubin-Tate |
| 局部对应n=2 | GL₂局部对应 | Kutzko |
| 局部对应一般n | 特征0 | Harris-Taylor |
| 整体对应n=2 | 经典模形式 | Wiles等 |
| 函数域对应 | GL_n | Drinfeld, Lafforgue |

## 研究前沿

1. **p进Langlands对应**: 模p与p进族版本
2. **几何Langlands**: 代数曲线上的对应
3. **函子性猜想**: 一般约化群的提升

---
*生成时间: 2026年4月*
*领域: 数论 / 自守形式 / Langlands纲领*
