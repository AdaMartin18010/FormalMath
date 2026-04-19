---
msc_primary: 00

  - 00A99
title: 同伦类型论：泛等公理推导推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 同伦类型论：泛等公理推导推理树

## 概述

本推理树展示泛等公理（Univalence Axiom）的推导及其深远影响，这是同伦类型论的核心创新，将结构等同与等价等同起来。

## 推理树

```mermaid
graph TD
    A[泛等公理] --> B[类型等同]
    B --> B1[ judgmental ≡ ]<-->B2[定义等同]
    B --> B3[propositional =]<-->B4[恒等类型]
    
    B --> C[类型宇宙]
    C --> C1[U: 小类型的类型]<-->C2[宇宙层级]
    C --> C3[编码-解码方法]<-->C4[El: U → Type]
    
    A --> D[等价概念]
    D --> D1[f: A → B]<-->D2[拟逆/双逆]
    D --> D3[isEquivf]<-->D4[ contractible fibers ]
    D --> D5[A ≃ B]<-->D6[Σf:A→B.isEquivf]
    
    D --> E[等价性质]
    E --> E1[自反性]<-->E2[id_A : A ≃ A]
    E --> E3[对称性]<-->E4[(A ≃ B) → (B ≃ A)]
    E --> E5[传递性]<-->E6[(A ≃ B) → (B ≃ C) → (A ≃ C)]
    
    A --> F[泛等公理UA]
    F --> F1[(A =_U B) ≃ (A ≃ B)]<-->F2[等同↔等价]
    F --> F3[idtoeqv]<-->F4[等同→等价]
    F --> F5[ua]<-->F6[等价→等同]
    
    G[UA的推论] --> G1[结构不变性]<-->G2[等价类型同结构]
    G --> G3[同构即等同]<-->G4[群同构→群等同]
    G --> G5[同伦不变性]<-->G6[可合同类型性质]
    
    H[函数外延] --> H1[ funext ]<-->H2[从UA推导]
    H --> H3[(Πx. fx = gx) → f = g]<-->H4[点相等→函数相等]
    
    I[高阶归纳类型] --> I1[高维生成子]<-->I2[点,路径,路径之路径]
    I --> I3[圆S¹]<-->I4[base, loop]
    I --> I5[球面Sⁿ]<-->I6[n维环路]
    I --> I7[推(pushout)]<-->I8[同伦余极限]
    
    J[应用] --> J1[代数拓扑]<-->J2[形式化π_nSⁿ=Z]
    J --> J3[范畴论]<-->J4[Rezk完备]
    J --> J5[集合论]<-->J6[泛等基础]
    
    K[模型] --> K1[Kapulkin-Lumsdaine]<-->K2[单纯集合模型]
    K --> K3[Coquand]<-->K4[Cubical类型论]
    K --> K5[Shulman]<-->K6[各种∞-Topos]
    
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

## 等价详解

### 1. 准逆定义

f: A → B有准逆，如果存在g: B → A使得：

```

g ∘ f ~ id_A
f ∘ g ~ id_B

```

### 2. 等价的标准定义

f: A → B是等价，如果对所有b:B，纤维contractible：

```

isequiv(f) := Π(b:B). isContr(fib_f(b))

```

其中 fib_f(b) := Σ(a:A). (f(a) = b)

### 3. 等价类型

```

A ≃ B := Σ(f:A→B). isequiv(f)

```

## 泛等公理

### 陈述

对于宇宙U中的类型A, B：

```

(A =_U B) ≃ (A ≃ B)

```

即类型等同等价于类型等价。

### 映射

**idtoeqv**: (A = B) → (A ≃ B)

```

idtoeqv(p) := transport^El(p)

```

**ua**: (A ≃ B) → (A = B)

```

ua(e) 是泛等公理提供的逆

```

### 计算规则

```

transport^C(ua(f), x) = e_*^C(x)

```

其中e_*^C是利用等价e在C中的重解释。

## 重要推论

### 1. 函数外延性

从UA可推导：

```

funext: (Π(x:A). f(x) = g(x)) → (f = g)

```

### 2. 结构不变性

等价类型承载相同的代数结构：

```

(A ≃ B) → (GroupStr(A) ≃ GroupStr(B))

```

### 3. 同伦水平保持

```

(A ≃ B) → (is-n-type(A) ↔ is-n-type(B))

```

## 高阶归纳类型示例

### 圆 S¹

```

inductive S¹: Type

| base: S¹
| loop: base = base

```

### 球面 S²

```

inductive S²: Type

| base: S²
| surf: refl_base = refl_base

```

---
*生成时间: 2026年4月*
*领域: 同伦类型论 / 泛等基础 / 数学基础*
