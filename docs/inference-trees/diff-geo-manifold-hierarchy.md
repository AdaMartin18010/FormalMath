---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 流形定义层次推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 流形定义层次推理树

## 概述

本推理树展示从拓扑空间到光滑流形的严格层次结构，以及各种流形类型之间的关系。

## 推理树

```mermaid
graph TD
    A[流形层次结构] --> B[拓扑空间]
    
    B --> C[局部欧氏空间]
    C --> C1[每点有邻域同胚于R^n]
    
    C --> D[拓扑流形]
    D --> D1[Hausdorff]
    D --> D2[第二可数]
    D --> D3[dim = n]
    
    D --> E[光滑结构]
    E --> E1[图册Atlas]<-->E2[坐标卡Uα,φα]
    E1 --> E3[转移函数光滑]
    E3 --> E4[φβ∘φα^-1 ∈ C^∞]
    
    E --> F[光滑流形]<-->F1[极大图册]
    F --> G[定向]
    G --> G1[相容定向图册]
    G --> G2[体积形式存在]
    G --> H[定向光滑流形]
    
    F --> I[带边流形]<-->I1[局部像R^n+]<-->I2[边界∂M]
    
    J[结构层次] --> J1[实流形]<-->J2[C^∞ M]
    J --> J3[复流形]<-->J4[全纯图册]<-->J5[复维n = 实维2n]
    J --> J6[代数簇]<-->J7[多项式定义]
    
    K[重要概念] --> K1[切空间]<-->K2[TpM ≅ R^n]
    K --> K3[切丛]<-->K4[TM = ⊔TpM]
    K --> K5[向量丛]<-->K6[局部平凡化]
    
    L[映射] --> L1[光滑映射]<-->L2[f: M -> N]
    L --> L3[浸入]<-->L4[df单射]
    L --> L5[淹没]<-->L6[df满射]
    L --> L7[微分同胚]<-->L8[光滑同胚+光滑逆]
    
    M[定理] --> M1[单位分解]<-->M2[仿紧性+第二可数]
    M --> M3[Sard定理]<-->M4[临界点测度为零]
    M --> M5[Whitney嵌入]<-->M6[M^n ↪ R^2n+1]
    
    N[例子] --> N1[S^n, T^n]<-->N2[标准光滑结构]
    N --> N3[ exotic R^4]<-->N4[非标准光滑结构]
    N --> N5[Milnor球面]<-->N6[ exotic S^7]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#fee,stroke:#333
    style C fill:#fdd,stroke:#333
    style D fill:#fcc,stroke:#333
    style E fill:#fbb,stroke:#333
    style F fill:#f99,stroke:#333
    style G fill:#f88,stroke:#333
    style H fill:#f77,stroke:#333
    style I fill:#bbf,stroke:#333
    style J fill:#bfb,stroke:#333
    style K fill:#bfb,stroke:#333
    style L fill:#f96,stroke:#333
    style M fill:#bfb,stroke:#333
    style N fill:#fbb,stroke:#333

```

## 层次详解

### 1. 局部欧氏空间
- 每点有邻域同胚于 R^n 开集
- 维数局部常数（连通分支上常数）

### 2. 拓扑流形
增加两个拓扑条件：
- **Hausdorff**: 分离公理，保证极限唯一
- **第二可数**: 有可数的拓扑基，保证仿紧性

### 3. 光滑流形
- **图册**: 坐标卡集合覆盖全空间
- **光滑相容**: 转移函数是光滑微分同胚
- **极大图册**: 包含所有相容坐标卡

### 4. 定向
- **定向图册**: 所有转移函数的Jacobian行列式为正
- **等价**: 存在处处非零的 n-形式

## 重要定理

| 定理 | 内容 | 意义 |
|------|------|------|
| 单位分解 | 光滑函数族，局部有限，和为1 | 构造整体对象 |
| Sard定理 | 临界值集合测度为零 | 正则值丰富 |
| Whitney嵌入 | n维流形可嵌入 R^{2n+1} | 流形的具体表示 |

## 特殊例子

1. **Exotic R⁴**: 与标准 R⁴ 同胚但不微分同胚的光滑流形
2. **Milnor球面**: 与 S⁷ 同胚但不微分同胚的 7 维流形
3. **不可定向**: Möbius带, Klein瓶, RPⁿ

---
*生成时间: 2026年4月*
*领域: 微分几何 / 流形理论*
