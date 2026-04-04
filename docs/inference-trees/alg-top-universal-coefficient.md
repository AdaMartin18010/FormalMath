---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 万有系数定理推理树

## 概述

本推理树展示万有系数定理的结构，它建立了整系数同调与任意系数同调之间的关系。

## 推理树

```mermaid
graph TD
    A[万有系数定理<br/>Universal Coefficient Theorem] --> B[同调版本]
    B --> B1[任意系数同调与整系数关系]
    B1 --> B2[HnX;G]
    
    B2 --> C[短正合列]
    C --> C1[0 -> HnX⊗G -> HnX;G -> TorHn-1X,G -> 0]
    C --> C2[分裂但非自然分裂]
    
    C1 --> D[HnX;G ≅ HnX⊗G ⊕ TorHn-1X,G]
    D --> D1[非典范同构]
    
    E[上同调版本] --> E1[H^nX;G]
    E1 --> F[短正合列]
    F --> F1[0 -> ExtHn-1X,G -> H^nX;G -> HomHnX,G -> 0]
    
    F1 --> G[分裂]
    G --> G1[H^nX;G ≅ HomHnX,G ⊕ ExtHn-1X,G]
    
    H[关键函子] --> H1[⊗张量积]
    H1 --> H2[HnX⊗G]
    H1 --> H3[保持直和]
    
    H --> H4[Tor挠函子]
    H4 --> H5[TorA,B]
    H4 --> H6[TorZ, B = 0]
    H4 --> H7[TorZ/nZ, B ≅ n-torsion of B]
    
    H --> H8[Hom]
    H8 --> H9[HomHnX, G]
    
    H --> H10[Ext]
    H10 --> H11[ExtA,G]
    H10 --> H12[ExtZ, G = 0]
    H10 --> H13[ExtZ/nZ, G ≅ G/nG]
    
    I[计算实例] --> I1[S^n with Z/2Z coeff]
    I1 --> I2[Hk = Z/2Z k=0,n; 0 else]
    
    I --> I3[RP^n with Z coeff]
    I3 --> I4[Hk = Z k=0; Z/2Z k odd < n; 0 else]
    
    J[应用] --> J1[Kunneth公式基础]
    J --> J2[Poincare对偶推广]
    J --> J3[示性数计算]
    
    K[导出函子] --> K1[左导出Tor]
    K --> K2[右导出Ext]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#fbb,stroke:#333
    style E fill:#bbf,stroke:#333
    style F fill:#bfb,stroke:#333
    style G fill:#fbb,stroke:#333
    style H fill:#f96,stroke:#333
    style I fill:#bfb,stroke:#333
    style J fill:#bfb,stroke:#333
    style K fill:#bbf,stroke:#333

```

## 定理详解

### 同调万有系数定理

对于拓扑空间 X 和 Abel 群 G，存在自然的短正合列：

```

0 -> Hn(X)⊗G -> Hn(X;G) -> Tor(Hn-1(X), G) -> 0

```

该序列分裂（非自然分裂），因此：

```

Hn(X;G) ≅ Hn(X)⊗G ⊕ Tor(Hn-1(X), G)

```

### 上同调万有系数定理

```

0 -> Ext(Hn-1(X), G) -> H^n(X;G) -> Hom(Hn(X), G) -> 0

```

分裂，因此：

```

H^n(X;G) ≅ Hom(Hn(X), G) ⊕ Ext(Hn-1(X), G)

```

## 关键函子

### Tor 函子（左导出）
- Tor(ℤ, B) = 0
- Tor(ℤ/nℤ, B) ≅ {b ∈ B : nb = 0}（n-挠子群）
- 挠子群间的关系

### Ext 函子（右导出）
- Ext(ℤ, G) = 0
- Ext(ℤ/nℤ, G) ≅ G/nG
- 测量同态扩张的障碍

## 应用

1. **Z/2Z 系数**: 常用于流形理论
2. **有理系数**: 消除挠，Hn(X;ℚ) ≅ Hn(X)⊗ℚ
3. **Kunneth公式**: 乘积空间同调计算基础

---
*生成时间: 2026年4月*
*领域: 代数拓扑 / 同调代数*
