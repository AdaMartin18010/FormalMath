# 同调群长正合列推理树

## 概述

本推理树展示同调代数中长正合列的构造，以及它在代数拓扑中的重要应用。

## 推理树

```mermaid
graph TD
    A[长正合列] --> B[代数版本]
    B --> B1[链复形的短正合列]
    B1 --> B2[0 -> A -> B -> C -> 0]
    B2 --> B3[诱导同调长正合列]
    
    A --> C[拓扑版本]
    C --> C1[空间对的同调]
    C1 --> C2[A ⊂ X 子空间]
    C2 --> C3[HnX,A]
    
    C3 --> D[正合列结构]
    D --> D1[... -> HnA -> HnX -> HnX,A -> Hn-1A -> ...]
    
    D1 --> E[连接同态]
    E --> E1[∂: HnX,A -> Hn-1A]
    E1 --> E2[几何意义: 边界]
    
    F[构造方法] --> F1[之字形引理]
    F1 --> F2[追图法]
    F2 --> F3[从短正合列构造长正合列]
    
    G[应用] --> G1[计算同调群]
    G1 --> G2[降维策略]
    G2 --> G3[从Hn-1求Hn]
    
    G --> G4[切除定理证明]
    G4 --> G5[同调论公理]
    
    G --> G6[Mayer-Vietoris]
    G6 --> G7[作为空间对的特例]
    
    H[相对同调] --> H1[X,A vs X/A]
    H1 --> H2[若A闭且邻域形变收缩]
    H2 --> H3[HnX,A ≅ HnX/A]
    
    I[三元组正合列] --> I1[A ⊂ B ⊂ X]
    I1 --> I2[... -> HnB,A -> HnX,A -> HnX,B -> ...]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style B fill:#bbf,stroke:#333
    style C fill:#bfb,stroke:#333
    style D fill:#f96,stroke:#333
    style E fill:#fbb,stroke:#333
    style F fill:#bbf,stroke:#333
    style G fill:#bfb,stroke:#333
    style H fill:#bfb,stroke:#333
    style I fill:#bfb,stroke:#333
```

## 长正合列详解

### 代数版本

给定链复形的短正合列：
```
0 -> A• -> B• -> C• -> 0
```

诱导同调长正合列：
```
... -> Hn(A) -> Hn(B) -> Hn(C) -> Hn-1(A) -> Hn-1(B) -> ...
```

### 拓扑版本：空间对的同调

对于空间对 (X, A)，有长正合列：
```
... -> Hn(A) -> Hn(X) -> Hn(X,A) -> Hn-1(A) -> ...
```

其中：
- Hn(A) -> Hn(X) 是包含映射诱导
- Hn(X) -> Hn(X,A) 是相对化映射
- ∂: Hn(X,A) -> Hn-1(A) 是连接同态

### 连接同态的几何意义

对于相对闭链 [c] ∈ Hn(X,A)：
- ∂[c] = [∂c] ∈ Hn-1(A)
- 几何上就是取边界（落在A中）

## 应用

### 1. 计算策略
- 利用短正合列降维计算
- 已知 Hn-1(A) 可推出 Hn(X,A)

### 2. 重要推论
- 若 A ↪ X 诱导同构，则 Hn(X,A) = 0
- 若 X 可缩，则 Hn(X,A) ≅ Hn-1(A)

### 3. 三元组正合列
对于 A ⊂ B ⊂ X：
```
... -> Hn(B,A) -> Hn(X,A) -> Hn(X,B) -> Hn-1(B,A) -> ...
```

---
*生成时间: 2026年4月*
*领域: 代数拓扑 / 同调代数*
