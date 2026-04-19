---
msc_primary: 00

  - 00A99
title: 导出代数几何：无穷范畴基础推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 导出代数几何：无穷范畴基础推理树

## 概述

本推理树展示无穷范畴理论的基础，这是导出代数几何和高等代数拓扑的语言框架，涵盖单纯集合、拟范畴和稳定无穷范畴。

## 推理树

```mermaid
graph TD
    A[无穷范畴基础] --> B[单纯集合]
    B --> B1[单纯形Δ]<-->B2[序数范畴]
    B --> B3[Simplicial Set]<-->B4[Δ^op → Set]
    B --> B5[几何实现]<-->B6[| - |: sSet → Top]
    
    B --> C[Kan复形]
    C --> C1[填充条件]<-->C2[Inner/Outer Horn]
    C --> C3[∞-群胚]<-->C4[所有箭头可逆]
    C --> C5[同伦群]<-->C6[π_n Kan复形]
    
    A --> D[拟范畴]
    D --> D1[弱Kan条件]<-->D2[Inner Horn填充]
    D --> D3[∞-范畴]<-->D4[高维态射]
    D --> D5[同伦范畴]<-->D6[hC: 1-截断]
    
    D --> E[映射空间]
    E --> E1[Hom^R]<-->E2[右映射空间]
    E --> E3[Hom^L]<-->E4[左映射空间]
    E --> E5[Hom]<-->E6[同伦类映射]
    
    A --> F[极限与余极限]
    F --> F1[无穷极限]<-->F2[锥的同伦极限]
    F --> F3[余极限]<-->F4[余锥的同伦余极限]
    
    G[函子范畴] --> G1[FunC,D]<-->G2[无穷函子范畴]
    G --> G3[自然变换]<-->G4[高维胞腔]
    G --> G5[Join构造]<-->G6[Slice范畴]
    
    H[伴随] --> H1[无穷伴随]<-->H2[单位余元同伦]
    H --> H3[等价]<-->H4[互逆等价]
    
    I[稳定无穷范畴] --> I1[零对象]<-->I2[初始且终对象]
    I --> I3[纤维余纤维]<-->I4[正方形既是拉回又是推出]
    I --> I5[平移函子]<-->I6[Σ: C ≃ C]
    
    J[t-结构] --> J1[同调代数]<-->J2[截断函子]
    J --> J3[心脏]<-->J4[C^♡: Abel范畴]
    
    K[模型范畴] --> K1[弱等价]<-->K2[纤维化/余纤维化]
    K --> K3[Quillen等价]<-->K4[导出等价]
    K --> K5[Simplicial model]<-->K6[单纯丰富]
    
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

## 单纯集合详解

### 1. 单纯形范畴

Δ: 有限非空序数范畴
- 对象: [n] = {0, 1, ..., n}
- 态射: 保序映射

### 2. 单纯集合

```

X: Δ^op → Set
X_n = X([n]) 称为n-单形

```

**面与退化映射**：

```

d_i: X_n → X_{n-1}  (面)
s_i: X_n → X_{n+1}  (退化)

```

### 3. Kan复形

X满足Kan条件：每个inner horn Λ^n_i → X可填充：

```

Λ^n_i → X
  ↓     ↗
 Δ^n

```

## 拟范畴详解

### 1. 弱Kan条件

拟范畴C: 满足所有**inner horns**可填充：

```

∀ 0 < i < n: Hom(Λ^n_i, C) ← Hom(Δ^n, C)

```

### 2. 同伦范畴

hC的构造：
- 对象: C的对象
- 态射: π₀(Hom^R_C(x,y))

### 3. 等价

f: x → y在C中是等价，如果在hC中是同构。

## 稳定无穷范畴

### 定义

C是稳定的，如果：
1. 有零对象
2. 每个纤维序列是余纤维序列，反之亦然
3. 推出正方形也是拉回正方形

### 平移

```

Σ: C → C  ( suspension )
Ω: C → C  ( loop )
Σ ⊣ Ω 是等价

```

### t-结构

一对满子范畴(C_{≤0}, C_{≥0})满足：
1. ΣC_{≤0} ⊆ C_{≤0}
2. ΩC_{≥0} ⊆ C_{≥0}
3. Hom(C_{≤0}, ΩC_{≥0}) = 0
4. 任意对象有纤维序列

## 模型范畴

### Quillen模型结构

三类态射：
- 弱等价 (W)
- 纤维化 (Fib)
- 余纤维化 (Cof)

满足：
- 2-out-of-3
- 提升性质
- 因子化

### 与无穷范畴的关系

```

C[W⁻¹] 的无穷版本 ↔ N(C)[W⁻¹]

```

---
*生成时间: 2026年4月*
*领域: 无穷范畴 / 高等代数拓扑 / 同伦论*
