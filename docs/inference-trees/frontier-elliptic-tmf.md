---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 椭圆上同调：拓扑模形式推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 椭圆上同调：拓扑模形式推理树

## 概述

本推理树展示拓扑模形式（Topological Modular Forms, Tmf）理论，这是Hopkins-Miller构造的极高阶上同调理论，在稳定同伦群计算和数学物理中有重要应用。

## 推理树

```mermaid
graph TD
    A[拓扑模形式Tmf] --> B[模形式]
    B --> B1[全模群SL2Z]<-->B2[上半平面作用]
    B --> B3[模形式]<-->B4[全纯函数f: ℍ → ℂ]
    B --> B5[f(γτ) = cτ+d^k f(τ)]<-->B6[权k变换]
    
    B --> C[模形式环]
    C --> C1[MF_*]<-->C2[全纯模形式]
    C --> C3[Eisenstein级数]<-->C4[G_k, E_k]
    C --> C5[判别式Δ]<-->C6[c_4³ - c_6² = 1728Δ]
    C --> C7[j-不变量]<-->C8[j = c_4³/Δ]
    
    A --> D[椭圆曲线模空间]
    D --> D1[M_ell]<-->D2[椭圆曲线模叠]
    D --> D3[Deligne-Mumford]<-->D4[代数叠]
    D --> D5[j-线]<-->D6[紧致化M̄_ell]
    
    D --> E[通用椭圆曲线]
    E --> E1[E → M_ell]<-->E2[万有族]
    E --> E3[形式群Ê]<-->E4[通用形式群]
    
    A --> F[导出层]
    F --> F1[结构层O^top]<-->F2[上同调理论层]
    F --> F3[Hopkins-Miller]<-->F4[Einfty-环谱层]
    F --> F5[堆叠化]<-->F6[在etale拓扑上]
    
    F --> G[拓扑模形式]
    G --> G1[Tmf = ΓM̄_ell, O^top]<-->G2[整体截面]
    G --> G3[Tmf_*]<-->G4[同伦群]
    
    G --> H[连通版本]
    H --> H1[tmf]<-->H2[连通覆盖]
    H --> H3[tmf_*]<-->H4[到MF_*的映射]
    
    I[周期] --> I1[72-周期性]<-->I2[Σ^72 Tmf ≃ Tmf]
    I --> I3[Δ^6]<-->I4[周期元]
    
    J[同伦群] --> J1[Tmf_-¹ = 0]<-->J2[消失定理]
    J --> J3[边缘同态]<-->J4[Adams-Novikov]
    
    K[应用] --> K1[稳定同伦群]<-->K2[球面的同伦群]
    K --> K3[弦论]<-->K4[椭圆亏格]
    K --> K5[Witten亏格]<-->K6[loop space指标]
    
    L[广义版本] --> L1[拓扑自守形式]<-->L2[TAF]
    L --> L3[更高维Abel簇]<-->L4[模空间的推广]
    
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
    style L fill:#f66,stroke:#333

```

## 模形式回顾

### 定义

权k的模形式是上半平面上的全纯函数：

```

f: ℍ → ℂ

```

满足：
- 变换性: f(γ·τ) = (cτ+d)^k f(τ), ∀γ ∈ SL₂(ℤ)
- 在尖点全纯

### 经典例子

**Eisenstein级数**:

```

E_{2k}(τ) = 1 - (4k/B_{2k}) Σ σ_{2k-1}(n) q^n

```

其中q = e^{2πiτ}。

**判别式**:

```

Δ(τ) = q Π(1-q^n)^24 = (E_4³ - E_6²)/1728

```

**j-不变量**:

```

j(τ) = E_4³/Δ = 1/q + 744 + 196884q + ...

```

## 椭圆曲线模空间

### M_ell

椭圆曲线的模叠M_ell是Deligne-Mumford叠。

**Weierstrass universal family**:

```

y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆

```

系数(a₁, a₂, a₃, a₄, a₆)给出M_ell的坐标。

### 紧致化

添加尖点曲线（nodal cubic）得到M̄_ell。

## Hopkins-Miller定理

### 陈述

存在E_∞-环谱层O^top在M̄_ell上，使得：
- 在椭圆曲线C处，纤维是椭圆上同调E_C
- 形式上，π_*E_C对应C的形式群

### 构造

1. 在etale site上构造presheaf
2. 使用Goerss-Hopkins-Miller obstruction theory提升到E_∞
3. 层化得到O^top

## 拓扑模形式

### 定义

```

Tmf := Γ(M̄_ell, O^top)  (全局截面)
tmf := τ_{≥0} Tmf       (连通覆盖)

```

### 同伦群

**定理**: 
- Tmf具有72-周期性
- tmf_{<0} = 0
- tmf_* → MF_*（模形式环）在某些维数是同构

### 与球谱的关系

单位映射S → tmf给出：

```

π_*S → tmf_*

```

在稳定同伦群的2,3-局部计算中非常有用。

## 椭圆亏格与物理

### Ochanine亏格

弦流形的椭圆亏格：

```

φ_W(M) = ⟨Û(M), [M]⟩

```

### Witten亏格

假设M有弦结构：

```

W(M) = ind(D_{LM}) ∈ MF_*

```

其中D_{LM}是loop space上的Dirac算子。

**定理** (Witten, Hopkins, Mahowald, ...):

```

弦流形的Witten亏格是模形式

```

这对应于tmf的定向：

```

MString → tmf

```

## 计算与应用

| 维数 | tmf_n | 意义 |
|------|-------|------|
| 0 | ℤ | 整数 |
| 1 | ℤ/2 | η |
| 2 | ℤ/2 | η² |
| 3 | ℤ/24 | ν |
| ... | ... | 稳定同伦元 |

---
*生成时间: 2026年4月*
*领域: 代数拓扑 / 同伦论 / 模形式*
