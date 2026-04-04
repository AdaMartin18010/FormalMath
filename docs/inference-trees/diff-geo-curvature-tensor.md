---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 曲率张量性质推理树

## 概述

本推理树展示黎曼曲率张量的定义、代数性质、恒等式及其几何意义。

## 推理树

```mermaid
graph TD
    A[曲率张量R] --> B[定义方式]
    B --> B1[坐标定义]<-->B2[R^l_ijk = ∂_iΓ^l_jk - ∂_jΓ^l_ik + Γ^l_imΓ^m_jk - Γ^l_jmΓ^m_ik]
    B --> B3[抽象定义]<-->B4[RX,YZ = ∇_X∇_YZ - ∇_Y∇_XZ - ∇_XYZ]<-->B5[无坐标]
    B --> B6[交换子]<-->B7[[∇_X,∇_Y]Z - ∇_[X,Y]Z]
    
    A --> C[代数性质]
    C --> C1[反对称性]<-->C2[R^l_ijk = -R^l_jik]
    C --> C3[第一Bianchi]<-->C4[R^l_ijk + R^l_jki + R^l_kij = 0]
    C --> C5[代数Bianchi]<-->C6[R_XYZ + R_YZX + R_ZXY = 0]
    
    C --> D[指标下降]<-->D1[R_lijk = g_lm R^m_ijk]
    D --> D2[额外对称性]<-->D3[R_lijk = -R_ljik = R_ijlk]
    D --> D4[R_lijk = R_klij]<-->D5[配对对称]
    
    E[微分恒等式] --> E1[Bianchi恒等式]<-->E2[∇_i R_jklm + ∇_j R_kilm + ∇_k R_ijlm = 0]
    E --> E3[缩并形式]<-->E4[∇^i R_ijkl = ∇_k R_jl - ∇_l R_jk]
    
    F[由曲率构造] --> F1[Ricci张量]<-->F2[R_ij = R^k_ijk = g^kl R_kijl]
    F2 --> F3[对称]<-->F4[R_ij = R_ji]
    
    F --> G[标量曲率]<-->G1[R = g^ij R_ij]<-->G2[迹]
    
    F --> H[Weyl张量]<-->H1[C_ijkl = R_ijkl - 1/n-2g_ikR_jl - g_ilR_jk - g_jkR_il - g_jlR_ik + R/n-1g_ikg_jl - g_ilg_jk]<-->H2[无迹部分]
    
    F --> I[Einstein张量]<-->I1[G_ij = R_ij - 1/2 g_ij R]<-->I2[散度为零]<-->I3[∇^i G_ij = 0]
    
    J[几何解释] --> J1[截面曲率]<-->J2[Kσ = RX,YX,Y/gX,XgY,Y - gX,Y^2]<-->J3[二维截面]
    J --> J4[Ricci曲率]<-->J5[Riccv,v = 截面曲率平均]<-->J6[各向同性]
    J --> J7[数量曲率]<-->J8[R = 所有方向曲率平均]
    
    K[常曲率空间] --> K1[K = const]<-->K2[截面曲率处处相同]
    K --> K3[标准模型]<-->K4[S^n, R^n, H^n]
    K --> K5[R_ijkl = Kg_ikg_jl - g_ilg_jk]<-->K6[曲率形式]
    
    L[消失定理] --> L1[平坦]<-->L2[R = 0 ⇔ 局部等距于R^n]<-->L3[可展空间]
    L --> L4[Ricci平坦]<-->L5[R_ij = 0]<-->L6[Einstein真空方程]<-->L7[Calabi-Yau]
    L --> L8[Einstein流形]<-->L9[R_ij = λg_ij]<-->L10[均匀膨胀]
    
    M[变分] --> M1[Einstein-Hilbert作用]<-->M2[S = ∫ R dvol]<-->M3[引力作用量]
    M --> M4[变分]<-->M5[δS = 0 ⇒ G_ij = 0]<-->M6[真空Einstein方程]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#bfb,stroke:#333
    style E fill:#f96,stroke:#333
    style F fill:#f96,stroke:#333
    style G fill:#f77,stroke:#333
    style H fill:#f88,stroke:#333
    style I fill:#f99,stroke:#333
    style J fill:#f96,stroke:#333
    style K fill:#fbb,stroke:#333
    style L fill:#fbb,stroke:#333
    style M fill:#f66,stroke:#333

```

## 曲率张量详解

### 定义
黎曼曲率张量度量了协变导数的非交换性：

```

R(X,Y)Z = ∇_X∇_YZ - ∇_Y∇_XZ - ∇_[X,Y]Z

```

### 代数恒等式

1. **反对称**: R(X,Y)Z = -R(Y,X)Z
2. **第一Bianchi**: R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0
3. **配对对称**: ⟨R(X,Y)Z, W⟩ = ⟨R(Z,W)X, Y⟩

### Bianchi恒等式

```

∇_X R(Y,Z)W + ∇_Y R(Z,X)W + ∇_Z R(X,Y)W = 0

```

### 缩并得到
- **Ricci恒等式**: ∇_i R_jklm + ... = 0
- **缩并Bianchi**: ∇^i R_ijkl = ∇_k R_jl - ∇_l R_jk

## 由曲率构造的量

### Ricci张量

```

R_ij = g^kl R_kijl

```

对称张量，表示平均曲率

### 标量曲率

```

R = g^ij R_ij

```

标量函数，平均曲率的迹

### Einstein张量

```

G_ij = R_ij - ½ g_ij R

```

散度为零：∇^i G_ij = 0（来自Bianchi恒等式）

### Weyl张量
在 n≥4 时存在，曲率的无迹部分，共形不变

## 几何意义

| 曲率类型 | 几何解释 |
|----------|----------|
| 截面曲率 | 二维截面的Gauss曲率 |
| Ricci曲率 | 无穷小球体积变化率 |
| 标量曲率 | 体积元相对于平坦空间的变化 |
| Weyl张量 | 共形几何的曲率部分 |

## 特殊空间

1. **常曲率空间**: R_ijkl = K(g_ik g_jl - g_il g_jk)
2. **Einstein流形**: R_ij = λg_ij（引力真空解）
3. **Ricci平坦**: R_ij = 0（Calabi-Yau流形）

---
*生成时间: 2026年4月*
*领域: 微分几何 / 黎曼几何*
