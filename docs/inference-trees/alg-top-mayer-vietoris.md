# Mayer-Vietoris序列推理树

## 概述

本推理树展示Mayer-Vietoris序列的推导与应用，这是计算同调群最重要的工具之一。

## 推理树

```mermaid
graph TD
    A[Mayer-Vietoris定理] --> B[定理陈述]
    
    B --> C[前提条件]
    C --> C1[X = U ∪ V]
    C --> C2[U,V开集或子复形]
    C --> C3[U,V,U∩V道路连通]
    
    B --> D[同调版本]
    D --> D1[... -> HnU∩V -> HnU⊕HnV -> HnX -> Hn-1U∩V -> ...]
    
    D1 --> E[映射定义]
    E --> E1[i*: HnU∩V -> HnU⊕HnV<br/>x -> iU*x, iV*x]
    E --> E2[j*: HnU⊕HnV -> HnX<br/>a,b -> jU*a - jV*b]
    E --> E3[∂: HnX -> Hn-1U∩V<br/>连接同态]
    
    B --> F[上同调版本]
    F --> F1[... -> H^nX -> H^nU⊕H^nV -> H^nU∩V -> H^n+1X -> ...]
    
    G[证明方法] --> G1[链复形构造]
    G1 --> G2[C•U∩V -> C•U⊕C•V -> C•X -> 0]
    G2 --> G3[短正合列 -> 长正合列]
    
    G --> G4[空间对方法]
    G4 --> G5[X,A where A = X\U or X\V]
    
    H[应用: 球面] --> H1[S^n计算]
    H1 --> H2[U = S^n\N, V = S^n\S]
    H2 --> H3[U∩V ≃ S^n-1]
    H3 --> H4[HkS^n = Z k=0,n; 0 其他]
    
    I[应用: 紧流形] --> I1[定向类]
    I1 --> I2[在U,V上的限制]
    I --> I3[Poincare对偶]
    
    J[约化版本] --> J1[H~nX ≅ H~nU⊕H~nV / imi*]
    J --> J2[用于连通空间]
    
    K[广义MV] --> K1[任意多个开集]
    K --> K2[谱序列方法]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#bfb,stroke:#333
    style E fill:#fbb,stroke:#333
    style F fill:#bfb,stroke:#333
    style G fill:#f96,stroke:#333
    style H fill:#bfb,stroke:#333
    style I fill:#bfb,stroke:#333
    style J fill:#bbf,stroke:#333
    style K fill:#bbf,stroke:#333
```

## 定理详解

### Mayer-Vietoris正合列

设 X = U ∪ V，其中 U, V 是开集（或子复形），则存在长正合列：

```
... -> Hn(U∩V) -> Hn(U)⊕Hn(V) -> Hn(X) -> Hn-1(U∩V) -> ...
```

**映射说明**：
- `i*: Hn(U∩V) -> Hn(U)⊕Hn(V)`，x ↦ (iᵤ*(x), iᵥ*(x))
- `j*: Hn(U)⊕Hn(V) -> Hn(X)`，(a,b) ↦ jᵤ*(a) - jᵥ*(b)
- `∂: Hn(X) -> Hn-1(U∩V)`：连接同态

### 上同调版本

```
... -> H^n(X) -> H^n(U)⊕H^n(V) -> H^n(U∩V) -> H^{n+1}(X) -> ...
```

## 应用实例

### 1. 球面同调
- U = Sⁿ \ {北极}, V = Sⁿ \ {南极}
- U ∩ V ≃ Sⁿ⁻¹
- 归纳证明 Hₖ(Sⁿ) = ℤ (k=0,n)，否则 0

### 2. 实射影空间
- 分解为 RPⁿ = Dⁿ ∪ RPⁿ⁻¹
- 利用 MV 序列归纳计算

### 3. 亏格 g 曲面
- 分解为两个带边曲面
- 计算 H₁ 和 H₂

## 计算策略

1. **分解空间**: 将复杂空间分解为简单部分
2. **利用已知**: U,V,U∩V 的同调已知或可计算
3. **正合性**: 利用正合列追图求未知群
4. **降维**: 从高维同调求低维同调

---
*生成时间: 2026年4月*
*领域: 代数拓扑 / 同调计算*
