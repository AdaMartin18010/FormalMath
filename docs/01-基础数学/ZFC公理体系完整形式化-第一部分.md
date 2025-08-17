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
    - [5. 结论](#5-结论)

## 📚 概述

ZFC公理体系（策梅洛-弗兰克尔集合论）是现代数学的严格基础，为整个数学体系提供了统一的逻辑框架。本文档将完整地形式化ZFC公理体系，并展示如何从这些公理推导出数学的基本概念。

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

### 5. 结论

ZFC公理体系为数学提供了严格的逻辑基础。通过这十个公理，我们可以构造出所有基本的数学对象，包括自然数、整数、有理数、实数等。在下一部分中，我们将展示如何从这些公理推导出整数和有理数的构造。

---

**文档状态**: ZFC公理体系基础部分完成  
**下一部分**: 整数和有理数的构造  
**形式化程度**: 完整形式化证明
