---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 张量分析推导推理树

## 概述

本推理树展示张量代数的构造过程，从向量空间到张量场，以及微分运算的建立。

## 推理树

```mermaid
graph TD
    A[张量分析] --> B[向量空间基础]
    B --> B1[V: 有限维实向量空间]
    B --> B2[V*: 对偶空间]
    
    B1 --> C[张量积构造]
    B2 --> C
    
    C --> C1[k,l型张量]<-->C2[T^k_lV = V⊗...⊗V⊗V*⊗...⊗V*]
    C2 --> C3[k个逆变, l个协变]
    C2 --> C4[维数: n^k+l]
    
    D[分量表示] --> D1[基{e_i}, {e^j}]
    D1 --> D2[T = T^i1...ik_j1...jl e_i1⊗...⊗e_ik⊗e^j1⊗...⊗e^jl]
    
    E[张量运算] --> E1[加法]<-->E2[同型张量]
    E --> E3[数乘]<-->E4[逐分量]
    E --> E5[缩并]<-->E6[上下指标求和]<-->E7[降阶]
    E --> E8[张量积]<-->E9[不同类型组合]<-->E10[升阶]
    
    F[流形上的张量场] --> F1[每点p∈M赋予张量]
    F1 --> F2[T^k_lM = ⊔Tp^k_lM]
    F2 --> G[光滑性]<-->G1[分量函数光滑]
    
    H[重要张量] --> H1[度量张量g]<-->H2[0,2型对称正定]<-->H3[内积结构]
    H --> H4[Levi-Civita符号]<-->H5[体积元]<-->H6[定向]
    H --> H7[Kronecker delta]<-->H8[恒等映射]
    
    I[指标运算] --> I1[Einstein求和约定]<-->I2[重复指标求和]
    I --> I3[指标升降]<-->I4[用度量g_ij, g^ij]
    I3 --> I5[v_i = g_ij v^j]
    I3 --> I6[v^i = g^ij v_j]
    
    J[协变导数] --> J1[∇: 张量场 -> 张量场]<-->J2[满足Leibniz法则]
    J --> J3[Christoffel符号]<-->J4[Γ^k_ij = 1/2 g^kl∂_i g_jl + ∂_j g_il - ∂_l g_ij]
    
    J --> K[平行移动]<-->K1[沿曲线保持向量]
    J --> L[测地线方程]<-->L1[∇_γ'γ' = 0]
    
    M[曲率张量] --> M1[R^l_ijk = ∂_iΓ^l_jk - ∂_jΓ^l_ik + Γ^l_imΓ^m_jk - Γ^l_jmΓ^m_ik]
    M --> N[Ricci张量]<-->N1[R_ij = R^k_ijk]
    N --> O[标量曲率]<-->O1[R = g^ij R_ij]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#fbb,stroke:#333
    style E fill:#bfb,stroke:#333
    style F fill:#f96,stroke:#333
    style G fill:#fbb,stroke:#333
    style H fill:#f96,stroke:#333
    style I fill:#bfb,stroke:#333
    style J fill:#f96,stroke:#333
    style K fill:#fbb,stroke:#333
    style L fill:#fbb,stroke:#333
    style M fill:#f66,stroke:#333
    style N fill:#f77,stroke:#333
    style O fill:#f88,stroke:#333

```

## 张量构造详解

### 1. 张量积
给定向量空间 V，(k,l) 型张量空间：

```

T^k_l(V) = V ⊗ ... ⊗ V ⊗ V* ⊗ ... ⊗ V*
            └─ k个 ─┘    └─ l个 ─┘

```

### 2. 分量变换
基变换 {e_i} → {ẽ_j}，变换矩阵 A^i_j：
- 逆变分量: Ṫ^i = A^i_j T^j
- 协变分量: Ṫ_i = (A⁻¹)^j_i T_j

### 3. Einstein求和约定
- 重复指标（一上一下）自动求和
- 例: v^i e_i = Σᵢ v^i e_i

## 微分运算

### 协变导数
度量相容、无挠的联络（Levi-Civita联络）：

```

Γ^k_ij = ½ g^kl(∂ᵢg_jl + ∂ⱼg_il - ∂ₗg_ij)

```

### 张量的协变导数

```

∇_k T^i_j = ∂_k T^i_j + Γ^i_kl T^l_j - Γ^l_kj T^i_l

```

### 曲率张量

```

R^l_ijk = ∂_iΓ^l_jk - ∂_jΓ^l_ik + Γ^l_imΓ^m_jk - Γ^l_jmΓ^m_ik

```

## 重要恒等式

1. **Bianchi恒等式**: ∇_i R_jklm + ∇_j R_kilm + ∇_k R_ijlm = 0
2. **Ricci恒等式**: [∇_i, ∇_j] v^k = R^k_lij v^l
3. **度规相容**: ∇_k g_ij = 0

---
*生成时间: 2026年4月*
*领域: 微分几何 / 张量分析*
