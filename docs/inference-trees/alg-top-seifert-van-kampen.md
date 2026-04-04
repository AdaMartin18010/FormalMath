# Seifert-van Kampen定理推理树

## 概述

本推理树展示Seifert-van Kampen定理的完整推导与应用，这是计算基本群最核心的工具。

## 推理树

```mermaid
graph TD
    A[Seifert-van Kampen定理] --> B[定理陈述]
    
    B --> C[前提条件]
    C --> C1[X = U ∪ V<br/>U,V开集]
    C --> C2[U,V道路连通]
    C --> C3[U ∩ V 非空道路连通]
    C --> C4[x₀ ∈ U ∩ V 基点]
    
    B --> D[结论]
    D --> D1[π₁X,x₀ ≅ π₁U * π₁V / N]
    D1 --> D2[自由积的商群]
    D --> D3[N的刻画]
    
    D3 --> E[正规子群N]
    E --> E1[由i*γ·j*γ⁻¹生成]
    E --> E2[i: U∩V ↪ U]
    E --> E3[j: U∩V ↪ V]
    E --> E4[γ ∈ π₁U∩V]
    
    F[证明思路] --> F1[构造同态Φ]
    F1 --> F2[π₁U * π₁V → π₁X]
    F2 --> F3[Φ是满射]
    
    F3 --> G[证明满射]
    G --> G1[任意X中回路可分解]
    G1 --> G2[分割成U,V中的段]
    G2 --> G3[每段在U或V中]
    G2 --> G4[在U∩V中调整基点]
    
    F3 --> H[证明kerΦ = N]
    H --> H1[N ⊆ kerΦ]<-->H2[i*γ = j*γ in π₁X]
    H --> H3[kerΦ ⊆ N]<-->H4[用2-维胞腔贴入]
    
    I[特殊情形] --> I1[U∩V单连通]<-->I2[π₁X ≅ π₁U * π₁V]
    I --> I3[U单连通]<-->I4[π₁X ≅ π₁V / N]
    I --> I5[V单连通]<-->I6[π₁X ≅ π₁U / N]
    
    J[应用: 贴空间] --> J1[贴1-胞腔]
    J1 --> J2[楔和: π₁A∨B = π₁A * π₁B]
    J2 --> J3[S¹ ∨ S¹: F₂]
    
    J --> K[贴2-胞腔]
    K --> K1[引入关系]
    K1 --> K2[贴入映射e: S¹→X₀]
    K2 --> K3[e*1 = 1 in π₁X]
    
    K --> L[亏格g曲面]
    L --> L1[4g边形表示]
    L --> L2[π₁ = ⟨a₁,b₁,...,a₉,b₉<br/>∏[aᵢ,bᵢ]=1⟩]
    
    M[应用: 图论] --> M1[图的基本群]
    M1 --> M2[π₁ = Fₙ<br/>n = 边数-顶点数+1]
    
    N[高维推广] --> N1[n维van Kampen]<-->N2[πₙ的Mayer-Vietoris]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#bfb,stroke:#333
    style E fill:#bbf,stroke:#333
    style F fill:#f96,stroke:#333
    style G fill:#fbb,stroke:#333
    style H fill:#fbb,stroke:#333
    style I fill:#bfb,stroke:#333
    style J fill:#bfb,stroke:#333
    style K fill:#bfb,stroke:#333
    style L fill:#f96,stroke:#333
    style M fill:#bfb,stroke:#333
    style N fill:#bbf,stroke:#333
```

## 定理详解

### 完整陈述

设 X 是拓扑空间，U 和 V 是 X 的开子集，满足：
1. X = U ∪ V
2. U, V, U ∩ V 都是道路连通的
3. x₀ ∈ U ∩ V 是基点

则有群同构：
```
π₁(X, x₀) ≅ π₁(U, x₀) * π₁(V, x₀) / N
```

其中：
- `*` 表示群的自由积
- N 是由 {i*(γ) · j*(γ)⁻¹ : γ ∈ π₁(U∩V)} 生成的正规子群
- i: U∩V ↪ U, j: U∩V ↪ V 是包含映射

### 证明概览

**步骤1: 构造同态 Φ**
- 由万有性质，存在 Φ: π₁(U) * π₁(V) → π₁(X)
- 在 π₁(U) 和 π₁(V) 上，Φ 就是包含诱导的同态

**步骤2: 证明 Φ 是满射**
- 任取 [f] ∈ π₁(X)
- 利用 Lebesgue 数引理，将 [0,1] 分割使每段在 U 或 V 中
- 在 U∩V 中调整基点
- 得到 f 是 U,V 中回路的乘积

**步骤3: 证明 ker(Φ) = N**
- N ⊆ ker(Φ): 因为 i*(γ) = j*(γ) in π₁(X)
- ker(Φ) ⊆ N: 构造2-维胞腔证明

## 应用实例

### 1. 楔和空间
```
π₁(A ∨ B) ≅ π₁(A) * π₁(B)
π₁(S¹ ∨ S¹) ≅ ℤ * ℤ = F₂（二元自由群）
```

### 2. 环面 T²
- U,V 为去一点的环面（可缩到 S¹ ∨ S¹）
- U∩V 可缩
- π₁(T²) ≅ ℤ * ℤ / [a,b] = 1 ≅ ℤ × ℤ

### 3. 亏格 g 曲面
- 4g 边形表示
- 一个关系: ∏ᵢ₌₁ᵍ [aᵢ, bᵢ] = 1
- π₁ = ⟨a₁,b₁,...,a₉,b₉ | ∏[aᵢ,bᵢ]=1⟩

### 4. 图的基本群
- 生成树收缩后得到楔和
- π₁ = Fₙ，n = 边数 - 顶点数 + 1

## 特殊情形

| 条件 | 结论 | 说明 |
|------|------|------|
| U∩V 单连通 | π₁(X) ≅ π₁(U) * π₁(V) | 自由积 |
| U 单连通 | π₁(X) ≅ π₁(V) / N | 商群 |
| U,V 都单连通 | π₁(X) = 0 | 单连通 |
| V 可缩 | π₁(X) ≅ π₁(U) / N | 商群 |

## 注意事项

1. **开集条件**: U,V 必须是开集
2. **道路连通**: U∩V 必须道路连通
3. **基点**: 必须在交集中取基点
4. **非开覆盖**: 可用形变收缩核处理

---
*生成时间: 2026年4月*
*领域: 代数拓扑 / 基本群计算*
