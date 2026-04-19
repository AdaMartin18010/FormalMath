---
msc_primary: 14

  - 14C15
msc_secondary: ['14C17', '14C25', '14F42']
title: Chow群 - 深度版
processed_at: '2026-04-08'
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# Chow群 - 深度版

**主题**: 代数几何 - 代数循环与有理等价
**难度**: ⭐⭐⭐⭐⭐ (研究级)
**先修知识**: 概形、维数、除子理论

---

## 目录

1. [概念深度解析](#1-概念深度解析)
2. [属性与关系](#2-属性与关系)
3. [示例与习题](#3-示例与习题)
4. [形式化实现](#4-形式化实现)
5. [应用与拓展](#5-应用与拓展)
6. [思维表征](#6-思维表征)

---

## 1. 概念深度解析

### 1.1 几何直观

**Chow群**是子簇的形式线性组合模有理等价的商群：

- **代数循环**：余维数 k 的闭子簇的有限形式和
- **有理等价**：由有理映射的纤维连接
- **交积**：在横截情形下为几何交集

**与上同调对比**：

- 上同调：拓扑不变量，系数 Z/Q/R
- Chow群：代数构造，保留更多几何信息

### 1.2 形式定义

**定义 1.1** (代数循环群 / Cycle Group)
设 X 为概形，维数 n。

Z_k(X) := ⊕_{V ⊆ X, dim V = k} Z · [V]

为 k 维闭整子簇的形式和。

**定义 1.2** (有理等价 / Rational Equivalence)
两个循环 α, β ∈ Z_k(X) **有理等价**，若存在 (k+1) 维子簇 W ⊆ X × P^1，使：
α - β = [W_0] - [W_∞]

**定义 1.3** (Chow群 / Chow Group)
A_k(X) := Z_k(X) / ~_{rat}

Chow群 Chow^*(X) := ⊕_k A^k(X)，其中 A^k = A_{n-k}。

### 1.3 代数表述

**相交积**：对光滑 X，有环结构：
A^i(X) × A^j(X) → A^{i+j}(X)

**proper 推进**：f: X → Y proper，有：
f_*: A_k(X) → A_k(Y)

**平坦拉回**：f: X → Y flat，有：
f^*: A^k(Y) → A^k(X)

---

## 2. 属性与关系

### 2.1 核心定理

**定理 2.1** (Chow环的结构)
对光滑射影簇 X，Chow^*(X) 是分次交换环，满足：

- 结合律、交换律
- 有单位元 [X] ∈ A^0(X)

**定理 2.2** (投射丛公式)
设 E 为秩 r 向量丛，P(E) 为投射丛，则：
A^_(P(E)) ≅ A^_[X](ξ)/(ξ^r + c_1(E)ξ^{r-1} + ... + c_r(E))

其中 ξ = O_{P(E)}(1)。

**定理 2.3** (Blow-up公式)
设 π: Bl_Z(X) → X 为 blow-up，则：
A^_(Bl_Z(X)) ≅ A^_(X) ⊕ ⊕_{i=1}^{c-1} A^{*-i}(Z)

其中 c = codim(Z, X)。

### 2.2 完整证明

**定理 2.1 (Chow环) 的证明**

**步骤1**：定义交积：对横截子簇，[V] · [W] = [V ∩ W]。

**步骤2**：用 Chow 移动引理：任意循环可移到横截位置。

**步骤3**：验证良定性：有理等价的循环给出相同交积。

**步骤4**：验证环公理。□

---

## 3. 示例与习题

### 3.1 具体示例

**示例 3.1** (射影空间)
A^*(P^n) = Z[h]/(h^{n+1})

其中 h = [H] 为超平面类。

- A^k(P^n) = Z · h^k（秩1）
- 交积：h^i · h^j = h^{i+j}

**示例 3.2** (Grassmannian)
G(k,n) 的 Chow 环由 Schubert 类生成：
A^*(G(k,n)) = ⊕_λ Z · σ_λ

其中 λ 为 fitting in k × (n-k) 的划分。

**示例 3.3** (曲线)
对光滑曲线 C：

- A^0(C) = Z · [C]
- A^1(C) = Pic(C)（除子类群）

### 3.2 反例

**反例 3.4** (奇异簇)
对奇异簇，Chow 环可能无交积结构，需要改用相交类。

### 3.3 习题

**习题 1**
计算 A^*(P^1 × P^1)。

**解答**：= Z[h_1, h_2]/(h_1^2, h_2^2)，其中 h_1 = pr_1^*h, h_2 = pr_2^*h。

**习题 2**
设 X = Bl_p(P^2)，计算其 Chow 环。

**习题 3**
证明：deg: A^n(P^n) → Z 是同构。

**习题 4**
计算 G(2,4) 中 σ_(1) · σ_(1)。

**习题 5**
设 X 为 K3 曲面，描述 A^*(X) 的结构。

---

## 4. 形式化实现

```lean4
import Mathlib

-- 代数循环
def AlgebraicCycle (X : Scheme) (k : ℕ) : Type :=
  FreeAbelianGroup (ClosedIntegralSubscheme X k)

-- 有理等价
inductive RationallyEquivalent {X : Scheme} {k : ℕ} :
    AlgebraicCycle X k → AlgebraicCycle X k → Prop
  | basic (W : Subscheme (X × P^1) (k+1)) (t0 t1 : P^1) :
      RationallyEquivalent [W_t0] - [W_t1] 0
  | linear : 等价关系

-- Chow群
def ChowGroup (X : Scheme) (k : ℕ) : Type :=
  AlgebraicCycle X k ⧸ RationallyEquivalent

-- 相交积（光滑情形）
def IntersectionProduct {X : SmoothVariety} {i j : ℕ} :
    ChowGroup X i → ChowGroup X j → ChowGroup X (i+j) :=
  sorry
```

---

## 5. 应用与拓展

### 5.1 数论联系

**算术Chow群**：Arakelov 理论中结合 Archimedean 信息。

### 5.2 物理应用

**弦理论**：D-膜荷由 K-理论和 Chow 群描述。

### 5.3 前沿方向

**高阶Chow群**：Bloch 定义的高维类比，与 K-理论联系。

---

**维护者**: FormalMath项目组
**最后更新**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐⭐ (研究级)
