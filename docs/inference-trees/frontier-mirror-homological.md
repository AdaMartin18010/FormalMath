---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 镜像对称：同源镜像对称推理树

## 概述

本推理树展示同源镜像对称（Homological Mirror Symmetry, HMS）猜想，这是Kontsevich提出的深刻数学框架，将代数几何与辛几何通过导出范畴等价联系起来。

## 推理树

```mermaid
graph TD
    A[同源镜像对称] --> B[两个范畴]
    B --> B1[导出范畴D^bCohX]<-->B2[代数几何侧]
    B --> B3[Fukaya范畴FukX̌]<-->B4[辛几何侧]
    
    A --> C[等价猜想]
    C --> C1[D^bCohX ≅ FukX̌]<-->C2[三角范畴等价]
    C --> C3[对象对应]<-->C4[复形 ↔ Lagrange子流形]
    C --> C5[态射对应]<-->C6[Ext ↔ Floer上同调]
    
    B1 --> D[导出范畴]
    D --> D1[凝聚层复形]<-->D2[有界导出范畴]
    D --> D3[导出张量积]<-->D4[导出Hom]
    D --> D5[Serre函子]<-->D6[SX = X⊗ω_X[n]]
    
    B3 --> E[Fukaya范畴]
    E --> E1[Lagrange子流形]<-->E2[对象]
    E --> E3[相交理论]<-->E4[HF^*L_0,L_1]
    E --> E5[A_∞结构]<-->E6[高阶积]
    
    A --> F[对象对应表]
    F --> F1[点 sheaf O_p]<-->F2[Lagrange环面]
    F --> F3[线丛O_D]<-->F4[Lagrange球面]
    F --> F5[结构层O_X]<-->F6[截面/对角线]
    
    G[函子对应] --> G1[Serre ↔ 对合]<-->G2[shift= grading]
    G --> G3[张量 ↔ 卷积]<-->G4[convolution]
    
    H[稳定性条件] --> H1[Bridegland稳定性]<-->H2[ hearts of t-structures ]
    H --> H3[稳定对象]<-->F1[特殊Lagrange]
    
    I[验证案例] --> I1[椭圆曲线]<-->I2[Polishchuk-Zaslow]
    I --> I3[Abel簇]<-->I4[Fukaya推广]
    I --> I5[四次曲面]<-->I6[Seidel证明]
    
    J[推广] --> J1[非交换几何]<-->J2[Landau-Ginzburg]
    J --> J3[范畴几何化]<-->J4[非Kähler情形]
    
    K[技术工具] --> K1[分解定理]<-->K2[例外对象]
    K --> K3[稳定性流形]<-->K4[模空间]
    
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
    style K fill:#bfb,stroke:#333

```

## 同源镜像对称猜想

### Kontsevich陈述

对于镜面对(X, X̌)，存在三角范畴等价：

```

D^b(Coh(X)) ≅ D^π Fuk(X̌)

```

其中：
- X是Calabi-Yau代数簇
- X̌是镜像辛流形
- D^π Fuk是Fukaya范畴的split-closure

## 导出范畴详解

### D^b(Coh(X))

- **对象**: 有界凝聚层复形
- **态射**: Ext群
- **三角结构**: 映射锥

### Serre函子

```

S: D^b(Coh(X)) → D^b(Coh(X))
S(E) = E ⊗ ω_X [n]

```

满足：

```

Hom(A,B)^* ≅ Hom(B, S(A))

```

## Fukaya范畴详解

### 对象

定向Lagrange子流形L，附加：
- grading (对graded Lagrange)
- spin结构或relative spin结构
- 平坦U(1)-联络

### 态射

Floer上同调群：

```

Hom(L_0, L_1) = HF^*(L_0, L_1)

```

### A_∞结构

高阶积：

```

m_k: Hom(L_0,L_1) ⊗ ... ⊗ Hom(L_{k-1},L_k) → Hom(L_0,L_k)[2-k]

```

计数伪全纯多边形。

## 对象对应表

| X (代数) | X̌ (辛) | 说明 |
|----------|--------|------|
| O_X | 对角线Δ ⊂ X̌×X̌ | 单位对象 |
| O_p (点) | 纤维环面T^n | SYZ对偶 |
| O(-D) | Lagrange球面 | exceptional object |
| 稳定层 | 特殊Lagrange | 极小子流形 |
| 扭平移 | Dehn扭转 | 对应 |

## 关键定理

| 结果 | 陈述 | 证明者 |
|------|------|--------|
| 椭圆曲线 | HMS对EC成立 | Polishchuk-Zaslow |
| Abel簇 | 一般维数 | Fukaya等 |
| 四次曲面 | HMS对quartic K3 | Seidel |
| 环面簇 | HMS for toric | Abouzaid |

## 稳定性条件

### Bridgegland稳定性

在三角范畴D上的稳定性条件包括：
-  hearts of bounded t-structure
- 中心Z: K(D) → ℂ
-  Harder-Narasimhan filtration

### 稳定对象与特殊Lagrange

猜想：

```

Bogomolov-Gieseker稳定层 ↔ 特殊Lagrange子流形

```

## 研究前沿

1. **Tropical HMS**: 热带几何与镜像对称
2. **Fano情形**: HMS for Fano varieties
3. **奇异性**: Landau-Ginzburg模型
4. **量子上同调**: 与Gromov-Witten不变量联系

---
*生成时间: 2026年4月*
*领域: 辛几何 / 代数几何 / 范畴论*
