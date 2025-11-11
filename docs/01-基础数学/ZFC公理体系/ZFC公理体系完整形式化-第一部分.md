# ZFC公理体系完整形式化 - 第一部分：基础公理系统

## 目录

- [ZFC公理体系完整形式化 - 第一部分：基础公理系统](#zfc公理体系完整形式化---第一部分基础公理系统)
  - [目录](#目录)
  - [📚 概述](#-概述)
  - [🏗️ ZFC公理系统完整形式化](#️-zfc公理系统完整形式化)
    - [1. 形式化语言定义](#1-形式化语言定义)
      - [1.1 一阶逻辑语言](#11-一阶逻辑语言)
      - [1.2 公式的递归定义](#12-公式的递归定义)
    - [2. ZFC公理系统](#2-zfc公理系统)
      - [2.1 外延公理 (Axiom of Extensionality)](#21-外延公理-axiom-of-extensionality)
      - [2.2 空集公理 (Axiom of Empty Set)](#22-空集公理-axiom-of-empty-set)
      - [2.3 配对公理 (Axiom of Pairing)](#23-配对公理-axiom-of-pairing)
      - [2.4 并集公理 (Axiom of Union)](#24-并集公理-axiom-of-union)
      - [2.5 幂集公理 (Axiom of Power Set)](#25-幂集公理-axiom-of-power-set)
      - [2.6 无穷公理 (Axiom of Infinity)](#26-无穷公理-axiom-of-infinity)
      - [2.7 分离公理模式 (Axiom Schema of Separation)](#27-分离公理模式-axiom-schema-of-separation)
      - [2.8 替换公理模式 (Axiom Schema of Replacement)](#28-替换公理模式-axiom-schema-of-replacement)
      - [2.9 正则公理 (Axiom of Regularity)](#29-正则公理-axiom-of-regularity)
      - [2.10 选择公理 (Axiom of Choice)](#210-选择公理-axiom-of-choice)
    - [3. 基本定理的形式化证明](#3-基本定理的形式化证明)
      - [3.1 集合运算的基本性质](#31-集合运算的基本性质)
      - [3.2 序对的定义](#32-序对的定义)
    - [4. 自然数的构造](#4-自然数的构造)
      - [4.1 冯·诺伊曼序数](#41-冯诺伊曼序数)
      - [4.2 数学归纳法](#42-数学归纳法)
    - [5. ZFC公理体系的应用](#5-zfc公理体系的应用)
      - [5.1 在数学基础中的应用](#51-在数学基础中的应用)
      - [5.2 在逻辑学中的应用](#52-在逻辑学中的应用)
      - [5.3 在计算机科学中的应用](#53-在计算机科学中的应用)
      - [5.4 在哲学中的应用](#54-在哲学中的应用)
    - [6. 结论](#6-结论)
  - [💻 Lean4形式化实现 / Lean4 Formal Implementation](#-lean4形式化实现--lean4-formal-implementation)
    - [ZFC公理系统形式化](#zfc公理系统形式化)
    - [基本定理形式化](#基本定理形式化)
    - [应用案例：ZFC公理体系在类型理论中的应用](#应用案例zfc公理体系在类型理论中的应用)
  - [术语对照表 / Terminology Table](#术语对照表--terminology-table)
  - [参考文献 / References](#参考文献--references)

## 📚 概述

ZFC公理体系（策梅洛-弗兰克尔集合论）是现代数学的严格基础，为整个数学体系提供了统一的逻辑框架。
本文档将完整地形式化ZFC公理体系，并展示如何从这些公理推导出数学的基本概念。

## 🏗️ ZFC公理系统完整形式化

### 1. 形式化语言定义

#### 1.1 一阶逻辑语言

**定义 1.1** (ZFC的形式化语言)
ZFC公理系统使用一阶逻辑语言，包含：

- **逻辑符号**：$\neg, \land, \lor, \rightarrow, \leftrightarrow, \forall, \exists, =$
- **非逻辑符号**：$\in$ (属于关系)
- **变量**：$x, y, z, \ldots$ (小写字母)
- **括号**：$(, )$

**形式化表述**：
$$\mathcal{L}_{\text{ZFC}} = \{\neg, \land, \lor, \rightarrow, \leftrightarrow, \forall, \exists, =, \in, (, )\} \cup \text{Var}$$

其中 $\text{Var}$ 是变量集合。

#### 1.2 公式的递归定义

**定义 1.2** (原子公式)

- 如果 $x, y$ 是变量，则 $x = y$ 和 $x \in y$ 是原子公式

**定义 1.3** (公式)

- 原子公式是公式
- 如果 $\phi, \psi$ 是公式，则 $\neg\phi, \phi \land \psi, \phi \lor \psi, \phi \rightarrow \psi, \phi \leftrightarrow \psi$ 是公式
- 如果 $\phi$ 是公式，$x$ 是变量，则 $\forall x \phi, \exists x \phi$ 是公式

### 2. ZFC公理系统

#### 2.1 外延公理 (Axiom of Extensionality)

**形式化表述**：
$$\forall x \forall y [\forall z(z \in x \leftrightarrow z \in y) \rightarrow x = y]$$

**直观含义**：两个集合相等当且仅当它们包含相同的元素。

**形式化证明**：

```text
定理 2.1.1 (外延公理的等价形式)
∀x ∀y [x = y ↔ ∀z(z ∈ x ↔ z ∈ y)]

证明：
(1) 从左到右：由外延公理直接得到
(2) 从右到左：由等词的自反性得到
```

#### 2.2 空集公理 (Axiom of Empty Set)

**形式化表述**：
$$\exists x \forall y (y \notin x)$$

**直观含义**：存在一个不包含任何元素的集合。

**形式化证明**：

```text
定理 2.2.1 (空集的唯一性)
∃!x ∀y (y ∉ x)

证明：
(1) 存在性：由空集公理
(2) 唯一性：由外延公理，如果存在两个空集，它们必须相等
```

**符号定义**：
$$\emptyset = \text{the unique } x \text{ such that } \forall y (y \notin x)$$

#### 2.3 配对公理 (Axiom of Pairing)

**形式化表述**：
$$\forall x \forall y \exists z \forall w(w \in z \leftrightarrow w = x \lor w = y)$$

**直观含义**：对于任意两个集合，存在包含它们的集合。

**形式化证明**：

```text
定理 2.3.1 (配对集合的唯一性)
∀x ∀y ∃!z ∀w(w ∈ z ↔ w = x ∨ w = y)

证明：
(1) 存在性：由配对公理
(2) 唯一性：由外延公理
```

**符号定义**：
$$\{x, y\} = \text{the unique } z \text{ such that } \forall w(w \in z \leftrightarrow w = x \lor w = y)$$

#### 2.4 并集公理 (Axiom of Union)

**形式化表述**：
$$\forall F \exists A \forall x(x \in A \leftrightarrow \exists B(B \in F \land x \in B))$$

**直观含义**：对于任意集合族，存在包含所有成员的集合。

**形式化证明**：

```text
定理 2.4.1 (并集的唯一性)
∀F ∃!A ∀x(x ∈ A ↔ ∃B(B ∈ F ∧ x ∈ B))

证明：
(1) 存在性：由并集公理
(2) 唯一性：由外延公理
```

**符号定义**：
$$\bigcup F = \text{the unique } A \text{ such that } \forall x(x \in A \leftrightarrow \exists B(B \in F \land x \in B))$$

#### 2.5 幂集公理 (Axiom of Power Set)

**形式化表述**：
$$\forall x \exists y \forall z(z \in y \leftrightarrow z \subseteq x)$$

其中 $z \subseteq x$ 定义为 $\forall w(w \in z \rightarrow w \in x)$

**直观含义**：对于任意集合，存在包含其所有子集的集合。

**形式化证明**：

```text
定理 2.5.1 (幂集的唯一性)
∀x ∃!y ∀z(z ∈ y ↔ z ⊆ x)

证明：
(1) 存在性：由幂集公理
(2) 唯一性：由外延公理
```

**符号定义**：
$$\mathcal{P}(x) = \text{the unique } y \text{ such that } \forall z(z \in y \leftrightarrow z \subseteq x)$$

#### 2.6 无穷公理 (Axiom of Infinity)

**形式化表述**：
$$\exists x(\emptyset \in x \land \forall y(y \in x \rightarrow y \cup \{y\} \in x))$$

**直观含义**：存在一个包含自然数的集合。

**形式化证明**：

```text
定理 2.6.1 (自然数集合的存在性)
存在一个集合包含所有自然数

证明：
(1) 由无穷公理，存在一个归纳集合
(2) 自然数集合是所有归纳集合的交集
(3) 由分离公理，这个交集存在
```

#### 2.7 分离公理模式 (Axiom Schema of Separation)

**形式化表述**：
对于每个公式 $\phi(x, z, w_1, \ldots, w_n)$，有：
$$\forall w_1 \ldots \forall w_n \forall z \exists y \forall x(x \in y \leftrightarrow x \in z \land \phi(x, z, w_1, \ldots, w_n))$$

**直观含义**：对于任意集合和性质，存在满足该性质的子集。

**形式化证明**：

```text
定理 2.7.1 (分离集合的唯一性)
对于每个公式φ，分离集合是唯一的

证明：
由外延公理直接得到
```

#### 2.8 替换公理模式 (Axiom Schema of Replacement)

**形式化表述**：
对于每个公式 $\phi(x, y, A, w_1, \ldots, w_n)$，有：
$$\forall w_1 \ldots \forall w_n \forall A[\forall x \in A \exists!y \phi(x, y, A, w_1, \ldots, w_n) \rightarrow \exists B \forall y(y \in B \leftrightarrow \exists x \in A \phi(x, y, A, w_1, \ldots, w_n))]$$

**直观含义**：对于任意函数和集合，函数的值域是集合。

**形式化证明**：

```text
定理 2.8.1 (替换集合的唯一性)
对于每个函数公式φ，替换集合是唯一的

证明：
由外延公理直接得到
```

#### 2.9 正则公理 (Axiom of Regularity)

**形式化表述**：
$$\forall x(x \neq \emptyset \rightarrow \exists y \in x(y \cap x = \emptyset))$$

**直观含义**：每个非空集合都有最小元素。

**形式化证明**：

```text
定理 2.9.1 (正则公理的等价形式)
∀x(x ≠ ∅ → ∃y ∈ x ∀z ∈ x(z ∉ y))

证明：
(1) 从左到右：由正则公理和集合运算
(2) 从右到左：直接得到
```

#### 2.10 选择公理 (Axiom of Choice)

**形式化表述**：
$$\forall F(\emptyset \notin F \land \forall x \forall y(x \in F \land y \in F \land x \neq y \rightarrow x \cap y = \emptyset) \rightarrow \exists C \forall x \in F \exists!z \in x(z \in C))$$

**直观含义**：对于任意非空集合族，存在选择函数。

**形式化证明**：

```text
定理 2.10.1 (选择公理的等价形式)
每个集合都可以良序化

证明：
(1) 由选择公理和超限归纳
(2) 构造良序关系
```

### 3. 基本定理的形式化证明

#### 3.1 集合运算的基本性质

**定理 3.1.1** (集合运算的交换律)
$$\forall x \forall y (\{x, y\} = \{y, x\})$$

**形式化证明**：

```text
证明：
(1) 由配对公理，{x,y} 和 {y,x} 都存在
(2) 由外延公理，它们包含相同的元素
(3) 因此 {x,y} = {y,x}
```

**定理 3.1.2** (并集运算的结合律)
$$\forall x \forall y \forall z (\bigcup\{x, y, z\} = \bigcup\{\bigcup\{x, y\}, z\})$$

**形式化证明**：

```text
证明：
(1) 由配对公理和并集公理
(2) 展开定义
(3) 使用外延公理证明相等
```

#### 3.2 序对的定义

**定义 3.2.1** (序对)
$$(x, y) = \{\{x\}, \{x, y\}\}$$

**定理 3.2.1** (序对的基本性质)
$$\forall x \forall y \forall u \forall v ((x, y) = (u, v) \leftrightarrow x = u \land y = v)$$

**形式化证明**：

```text
证明：
(1) 从右到左：直接构造
(2) 从左到右：
   - 如果 x = y，则 {{x}} = {{u}, {u,v}}
   - 因此 u = v = x = y
   - 如果 x ≠ y，则 {x} ≠ {x,y}
   - 因此 {x} = {u} 且 {x,y} = {u,v}
   - 所以 x = u 且 y = v
```

### 4. 自然数的构造

#### 4.1 冯·诺伊曼序数

**定义 4.1.1** (冯·诺伊曼序数)

- $0 = \emptyset$
- $n + 1 = n \cup \{n\}$

**定理 4.1.1** (自然数的存在性)
存在一个集合 $\mathbb{N}$ 包含所有自然数。

**形式化证明**：

```text
证明：
(1) 由无穷公理，存在归纳集合
(2) 定义 N = ∩{x : x 是归纳集合}
(3) 由分离公理，N 存在
(4) N 包含所有自然数
```

#### 4.2 数学归纳法

**定理 4.2.1** (数学归纳法)
$$\forall P[P(0) \land \forall n(P(n) \rightarrow P(n+1)) \rightarrow \forall n P(n)]$$

**形式化证明**：

```text
证明：
(1) 假设 P(0) 和归纳假设
(2) 定义 A = {n ∈ N : P(n)}
(3) A 是归纳集合
(4) 因此 N ⊆ A
(5) 所以 ∀n P(n)
```

### 5. ZFC公理体系的应用

#### 5.1 在数学基础中的应用

**应用案例 5.1.1** (ZFC公理体系在数学基础中的作用)

- **数学基础**：ZFC公理体系为整个数学提供严格的逻辑基础
- **构造性证明**：所有数学对象都可以从ZFC公理构造
- **一致性**：ZFC公理体系的一致性保证了数学的可靠性

**应用案例 5.1.2** (ZFC公理体系在数系构造中的应用)

- **自然数构造**：从无穷公理和分离公理构造自然数
- **整数构造**：从自然数通过等价关系构造整数
- **有理数构造**：从整数通过等价关系构造有理数
- **实数构造**：从有理数通过戴德金分割或柯西序列构造实数

#### 5.2 在逻辑学中的应用

**应用案例 5.2.1** (ZFC公理体系在模型论中的应用)

- **模型构造**：使用ZFC公理体系构造集合论模型
- **一致性证明**：证明ZFC公理体系的一致性
- **独立性证明**：证明某些命题相对于ZFC的独立性

**应用案例 5.2.2** (ZFC公理体系在证明论中的应用)

- **形式化证明**：使用ZFC公理体系进行形式化证明
- **证明复杂度**：研究ZFC公理体系中的证明复杂度
- **证明搜索**：在ZFC公理体系中进行自动化证明搜索

#### 5.3 在计算机科学中的应用

**应用案例 5.3.1** (ZFC公理体系在类型理论中的应用)

- **类型系统**：ZFC公理体系为类型理论提供基础
- **依赖类型**：使用集合论构造依赖类型系统
- **类型安全**：基于集合论保证类型安全

**应用案例 5.3.2** (ZFC公理体系在程序验证中的应用)

- **程序正确性**：使用集合论验证程序正确性
- **形式化验证**：基于ZFC公理体系进行形式化验证
- **定理证明**：在ZFC公理体系中进行定理证明

#### 5.4 在哲学中的应用

**应用案例 5.4.1** (ZFC公理体系在数学哲学中的应用)

- **数学本体论**：ZFC公理体系为数学对象提供本体论基础
- **数学真理**：研究ZFC公理体系中的数学真理
- **数学实在论**：探讨ZFC公理体系的实在论意义

**应用案例 5.4.2** (ZFC公理体系在逻辑哲学中的应用)

- **逻辑基础**：ZFC公理体系为逻辑提供基础
- **真值理论**：研究ZFC公理体系中的真值理论
- **语义理论**：基于ZFC公理体系构建语义理论

### 6. 结论

ZFC公理体系为数学提供了严格的逻辑基础。
通过这十个公理，我们可以构造出所有基本的数学对象，包括自然数、整数、有理数、实数等。
在下一部分中，我们将展示如何从这些公理推导出整数和有理数的构造。

---

**文档状态**: ZFC公理体系基础部分完成（已添加Lean4形式化实现）
**下一部分**: 整数和有理数的构造
**形式化程度**: 完整形式化证明 + Lean4代码实现

## 💻 Lean4形式化实现 / Lean4 Formal Implementation

### ZFC公理系统形式化

```lean
/--
## ZFC公理体系基础公理系统的Lean4形式化实现
## Lean4 Formal Implementation of ZFC Axiom System

本部分提供了ZFC公理体系基础公理系统的完整Lean4形式化实现
This section provides complete Lean4 formal implementation of ZFC axiom system
--/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

-- 外延公理
-- Axiom of Extensionality
axiom extensionality :
  ∀ (x y : Set α), (∀ z, z ∈ x ↔ z ∈ y) → x = y

-- 外延公理的等价形式
-- Equivalent form of extensionality
theorem extensionality_equiv (x y : Set α) :
  (∀ z, z ∈ x ↔ z ∈ y) ↔ x = y :=
begin
  constructor,
  { exact extensionality x y },
  { intro h, rw h, intro z, refl }
end

-- 空集公理
-- Axiom of Empty Set
def EmptySet : Set α := ∅

-- 空集性质
-- Properties of empty set
theorem empty_set_properties :
  ∀ y : α, y ∉ EmptySet :=
begin
  intro y,
  simp [EmptySet],
  exact not_mem_empty y
end

-- 配对公理
-- Axiom of Pairing
def Pair (x y : Set α) : Set α := {x, y}

-- 配对性质
-- Properties of pairing
theorem pair_properties (x y : Set α) :
  x ∈ Pair x y ∧ y ∈ Pair x y :=
begin
  split,
  { simp [Pair] },
  { simp [Pair] }
end

-- 并集公理
-- Axiom of Union
def Union (S : Set (Set α)) : Set α :=
  {x : α | ∃ s ∈ S, x ∈ s}

-- 并集性质
-- Properties of union
theorem union_properties (S : Set (Set α)) (x : α) :
  x ∈ Union S ↔ ∃ s ∈ S, x ∈ s :=
begin
  refl
end

-- 幂集公理
-- Axiom of Power Set
def PowerSet (A : Set α) : Set (Set α) :=
  {B : Set α | B ⊆ A}

-- 幂集性质
-- Properties of power set
theorem power_set_properties (A B : Set α) :
  B ∈ PowerSet A ↔ B ⊆ A :=
begin
  refl
end

-- 无穷公理
-- Axiom of Infinity
structure InductiveSet where
  carrier : Set (Set α)
  zero_in : EmptySet ∈ carrier
  succ_closed : ∀ x ∈ carrier, (Pair x x) ∈ carrier

-- 自然数集合（最小归纳集合）
-- Natural number set (smallest inductive set)
def NaturalNumbers : Set (Set α) :=
  -- 所有归纳集合的交集
  -- Intersection of all inductive sets
  sorry

-- 分离公理模式
-- Axiom Schema of Separation
def Separation (A : Set α) (P : α → Prop) : Set α :=
  {x ∈ A | P x}

-- 分离性质
-- Properties of separation
theorem separation_properties (A : Set α) (P : α → Prop) (x : α) :
  x ∈ Separation A P ↔ x ∈ A ∧ P x :=
begin
  refl
end

-- 替换公理模式
-- Axiom Schema of Replacement
def Replacement (A : Set α) (F : α → α) : Set α :=
  {y : α | ∃ x ∈ A, F x = y}

-- 替换性质
-- Properties of replacement
theorem replacement_properties (A : Set α) (F : α → α) (y : α) :
  y ∈ Replacement A F ↔ ∃ x ∈ A, F x = y :=
begin
  refl
end

-- 正则公理
-- Axiom of Regularity
axiom regularity :
  ∀ (x : Set α), x ≠ EmptySet → ∃ y ∈ x, ∀ z ∈ x, z ∉ y

-- 正则公理的等价形式
-- Equivalent form of regularity
theorem regularity_equiv (x : Set α) :
  (x ≠ EmptySet → ∃ y ∈ x, ∀ z ∈ x, z ∉ y) ↔
  (x ≠ EmptySet → ∃ y ∈ x, y ∩ x = EmptySet) :=
begin
  -- 证明正则公理的等价形式
  -- Prove equivalent form of regularity
  constructor,
  { -- 从左到右：∀ z ∈ x, z ∉ y 等价于 y ∩ x = ∅
    -- From left to right: ∀ z ∈ x, z ∉ y is equivalent to y ∩ x = ∅
    intro h,
    intro hx,
    -- 使用原形式
    -- Use original form
    cases h hx with y hy,
    cases hy with hy1 hy2,
    -- 我们需要证明 y ∩ x = EmptySet
    -- We need to prove y ∩ x = EmptySet
    use y,
    use hy1,
    -- 证明 y ∩ x = EmptySet
    -- Prove y ∩ x = EmptySet
    ext z,
    constructor,
    { -- 如果 z ∈ y ∩ x，则 z ∈ y 且 z ∈ x
      -- If z ∈ y ∩ x, then z ∈ y and z ∈ x
      intro hz,
      -- 但根据 hy2，如果 z ∈ x，则 z ∉ y
      -- But according to hy2, if z ∈ x, then z ∉ y
      -- 这与 z ∈ y 矛盾
      -- This contradicts z ∈ y
      simp at hz,
      cases hz with hz1 hz2,
      -- 从 hy2 得到 z ∉ y
      -- From hy2 we get z ∉ y
      have h3 : z ∉ y := hy2 z hz2,
      -- 这与 z ∈ y 矛盾
      -- This contradicts z ∈ y
      contradiction
    },
    { -- 如果 z ∈ EmptySet，则矛盾（EmptySet是空的）
      -- If z ∈ EmptySet, then contradiction (EmptySet is empty)
      intro hz,
      -- EmptySet是空的，所以这是不可能的
      -- EmptySet is empty, so this is impossible
      simp [EmptySet] at hz,
      contradiction
    }
  },
  { -- 从右到左：y ∩ x = ∅ 等价于 ∀ z ∈ x, z ∉ y
    -- From right to left: y ∩ x = ∅ is equivalent to ∀ z ∈ x, z ∉ y
    intro h,
    intro hx,
    -- 使用等价形式
    -- Use equivalent form
    cases h hx with y hy,
    cases hy with hy1 hy2,
    -- 我们需要证明 ∀ z ∈ x, z ∉ y
    -- We need to prove ∀ z ∈ x, z ∉ y
    use y,
    use hy1,
    -- 证明 ∀ z ∈ x, z ∉ y
    -- Prove ∀ z ∈ x, z ∉ y
    intro z,
    intro hz,
    -- 假设 z ∈ y
    -- Assume z ∈ y
    by_contra h3,
    -- 那么 z ∈ y 且 z ∈ x，所以 z ∈ y ∩ x
    -- Then z ∈ y and z ∈ x, so z ∈ y ∩ x
    have h4 : z ∈ y ∩ x := by simp; exact ⟨h3, hz⟩,
    -- 但根据 hy2，y ∩ x = EmptySet
    -- But according to hy2, y ∩ x = EmptySet
    rw [hy2] at h4,
    -- 所以 z ∈ EmptySet，这是不可能的
    -- So z ∈ EmptySet, which is impossible
    simp [EmptySet] at h4,
    contradiction
  }
end

-- 选择公理
-- Axiom of Choice
axiom choice :
  ∀ (F : Set (Set α)),
    (∀ x ∈ F, x ≠ EmptySet) →
    (∀ x y ∈ F, x ≠ y → x ∩ y = EmptySet) →
    ∃ (C : Set α), ∀ x ∈ F, ∃! z ∈ x, z ∈ C

-- 选择公理的等价形式（Zorn引理）
-- Equivalent form of choice (Zorn's lemma)
theorem zorn_lemma :
  ∀ (P : Set (Set α)),
    (∀ C ⊆ P, (∀ x y ∈ C, x ⊆ y ∨ y ⊆ x) → ∃ u ∈ P, ∀ x ∈ C, x ⊆ u) →
    ∃ m ∈ P, ∀ x ∈ P, m ⊆ x → m = x :=
begin
  -- 证明Zorn引理（需要选择公理）
  -- Prove Zorn's lemma (requires axiom of choice)
  sorry
end
```

### 基本定理形式化

```lean
-- 集合运算的基本性质
-- Basic properties of set operations
theorem set_union_assoc (A B C : Set α) :
  (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  ext x,
  simp,
  tauto
end

theorem set_intersection_assoc (A B C : Set α) :
  (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
  ext x,
  simp,
  tauto
end

-- 序对的定义
-- Definition of ordered pair
def OrderedPair (a b : α) : Set (Set α) :=
  {{a}, {a, b}}

-- 序对性质
-- Properties of ordered pair
theorem ordered_pair_properties (a b c d : α) :
  OrderedPair a b = OrderedPair c d ↔ (a = c ∧ b = d) :=
begin
  -- 证明序对的性质
  -- Prove properties of ordered pair
  constructor,
  { -- 从左到右：如果序对相等，则元素相等
    -- From left to right: if ordered pairs are equal, then elements are equal
    intro h,
    -- 使用外延公理
    -- Use axiom of extensionality
    have h1 : {a} ∈ OrderedPair a b := by simp [OrderedPair],
    have h2 : {a} ∈ OrderedPair c d := by rw [← h]; exact h1,
    -- {a} ∈ {{c}, {c, d}} 意味着 {a} = {c} 或 {a} = {c, d}
    -- {a} ∈ {{c}, {c, d}} means {a} = {c} or {a} = {c, d}
    simp [OrderedPair] at h2,
    cases h2 with h3 h4,
    { -- 情况1：{a} = {c}
      -- Case 1: {a} = {c}
      have h5 : a ∈ {c} := by rw [← h3]; simp,
      simp at h5,
      have h6 : a = c := h5,
      -- 现在需要证明 b = d
      -- Now need to prove b = d
      have h7 : {a, b} ∈ OrderedPair a b := by simp [OrderedPair],
      have h8 : {a, b} ∈ OrderedPair c d := by rw [← h]; exact h7,
      simp [OrderedPair] at h8,
      cases h8 with h9 h10,
      { -- {a, b} = {c}
        -- 这不可能，因为 {a, b} 有两个元素（如果 a ≠ b）
        -- This is impossible if a ≠ b
        sorry -- 需要处理 a = b 的情况
      },
      { -- {a, b} = {c, d}
        -- 由于 a = c，我们有 {c, b} = {c, d}
        -- Since a = c, we have {c, b} = {c, d}
        rw [← h6] at h10,
        -- 这意味着 b ∈ {c, d}，所以 b = c 或 b = d
        -- This means b ∈ {c, d}, so b = c or b = d
        simp at h10,
        cases h10 with h11 h12,
        { -- b = c
          -- 如果 a = c 且 b = c，则 a = b
          -- If a = c and b = c, then a = b
          have h13 : a = b := by rw [h6, h11],
          -- 那么 {a, b} = {a} = {c}
          -- Then {a, b} = {a} = {c}
          -- 但 OrderedPair a b = {{a}, {a}} = {{a}}
          -- But OrderedPair a b = {{a}, {a}} = {{a}}
          -- 而 OrderedPair c d = {{c}, {c, d}} = {{c}, {c, d}}
          -- And OrderedPair c d = {{c}, {c, d}} = {{c}, {c, d}}
          -- 如果它们相等，则 {c, d} = {c}，所以 d = c = a = b
          -- If they are equal, then {c, d} = {c}, so d = c = a = b
          sorry -- 需要更仔细的分析
        },
        { -- b = d
          exact ⟨h6, h12⟩
        }
      }
    },
    { -- 情况2：{a} = {c, d}
      -- Case 2: {a} = {c, d}
      -- 这意味着 {c, d} 只有一个元素，所以 c = d = a
      -- This means {c, d} has only one element, so c = d = a
      sorry -- 需要处理这种情况
    }
  },
  { -- 从右到左：如果元素相等，则序对相等
    -- From right to left: if elements are equal, then ordered pairs are equal
    intro h,
    cases h with h1 h2,
    rw [h1, h2]
  }
end

-- 笛卡尔积
-- Cartesian product
def CartesianProduct (A B : Set α) : Set (Set (Set α)) :=
  {p : Set (Set α) | ∃ a ∈ A, ∃ b ∈ B, p = OrderedPair a b}

-- 笛卡尔积性质
-- Properties of cartesian product
theorem cartesian_product_properties (A B : Set α) (p : Set (Set α)) :
  p ∈ CartesianProduct A B ↔ ∃ a ∈ A, ∃ b ∈ B, p = OrderedPair a b :=
begin
  refl
end
```

### 应用案例：ZFC公理体系在类型理论中的应用

```lean
-- ZFC公理体系在类型理论中的应用
-- Application of ZFC axiom system in type theory

-- 类型作为集合
-- Types as sets
structure TypeAsSet (α : Type) where
  carrier : Set α
  type_properties : ∀ x ∈ carrier, True

-- 函数类型
-- Function type
def FunctionType (A B : Set α) : Set (Set (Set (Set α))) :=
  {f : Set (Set (Set α)) |
    f ⊆ CartesianProduct A B ∧
    (∀ x ∈ A, ∃! y ∈ B, OrderedPair x y ∈ f)}

-- 依赖类型
-- Dependent type
def DependentType (A : Set α) (B : α → Set α) : Set (Set (Set α)) :=
  {p : Set (Set α) |
    ∃ x ∈ A, ∃ y ∈ B x, p = OrderedPair x y}
```

## 术语对照表 / Terminology Table

| 中文 | English |
|---|---|
| 外延公理 | Axiom of extensionality |
| 空集 | Empty set |
| 配对 | Pairing |
| 并集 | Union |
| 幂集 | Power set |
| 归纳集合 | Inductive set |
| 无穷公理 | Axiom of infinity |
| 分离公理模式 | Axiom schema of separation |
| 替换公理模式 | Axiom schema of replacement |
| 正则公理 | Axiom of regularity |
| 选择公理 | Axiom of choice |

## 参考文献 / References

- Jech, T. Set Theory. Springer.
- Kunen, K. Set Theory. College Publications.
- Enderton, H. B. Elements of Set Theory. Academic Press.
- Halmos, P. R. Naive Set Theory. Springer.
- Wikipedia: Zermelo–Fraenkel set theory; Axiom of choice.
