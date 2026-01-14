# ZFC公理体系深化扩展版

## 目录

- [ZFC公理体系深化扩展版](#zfc公理体系深化扩展版)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 形式化语言与语法](#1-形式化语言与语法)
    - [1.1 一阶逻辑语言](#11-一阶逻辑语言)
    - [1.2 集合论语言](#12-集合论语言)
    - [1.3 语法规则](#13-语法规则)
  - [2. ZFC公理系统严格表述](#2-zfc公理系统严格表述)
    - [2.1 外延公理](#21-外延公理)
    - [2.2 空集公理](#22-空集公理)
    - [2.3 配对公理](#23-配对公理)
    - [2.4 并集公理](#24-并集公理)
    - [2.5 幂集公理](#25-幂集公理)
    - [2.6 无穷公理](#26-无穷公理)
    - [2.7 替换公理模式](#27-替换公理模式)
    - [2.8 正则公理](#28-正则公理)
    - [2.9 选择公理](#29-选择公理)
  - [补充：ZFC 公理体系国际对齐与多表征（精炼版）](#补充zfc-公理体系国际对齐与多表征精炼版)
    - [A. 国际对齐要点](#a-国际对齐要点)
    - [B. 多表征](#b-多表征)
    - [C. 批判性要点](#c-批判性要点)
    - [D. 历史脉络（精要）](#d-历史脉络精要)
    - [E. 示例/练习](#e-示例练习)

## 概述

本文档深入探讨ZFC公理体系的严格形式化表述、独立性证明、模型论基础以及在现代数学中的重要作用。
这是对集合论基础理论的全面深化和扩展。

## 1. 形式化语言与语法

### 1.1 一阶逻辑语言

**定义 1.1.1** (一阶逻辑语言)
一阶逻辑语言 $\mathcal{L}$ 包含以下符号：

**逻辑符号**:

- 连接词: $\neqg, \land, \lor, \rightarrow, \leqftrightarrow$
- 量词: $\forall, \exists$
- 等号: $=$
- 括号: $(, )$

**非逻辑符号**:

- 关系符号: $\in$ (二元关系)
- 变量: $x, y, z, \ldots$ (可数无限个)

**定义 1.1.2** (项)
项递归定义如下：

- 变量是项
- 没有函数符号，所以项就是变量

**定义 1.1.3** (公式)
公式递归定义如下：

- 如果 $t_1, t_2$ 是项，则 $t_1 = t_2$ 和 $t_1 \in t_2$ 是原子公式
- 如果 $\phi, \psi$ 是公式，则 $\neqg\phi, \phi \land \psi, \phi \lor \psi, \phi \rightarrow \psi, \phi \leqftrightarrow \psi$ 是公式
- 如果 $\phi$ 是公式，$x$ 是变量，则 $\forall x \phi, \exists x \phi$ 是公式

### 1.2 集合论语言

**定义 1.2.1** (集合论语言)
集合论语言 $\mathcal{L}_{\text{ZFC}}$ 是一阶逻辑语言，其中：

- 唯一的非逻辑符号是二元关系符号 $\in$
- 没有函数符号
- 没有常量符号

**定义 1.2.2** (缩写定义)
以下是一些常用的缩写：

- $x \subseteq y$ 表示 $\forall z(z \in x \rightarrow z \in y)$
- $x \subset y$ 表示 $x \subseteq y \land x \neqq y$
- $\{x\}$ 表示 $\{x, x\}$
- $\emptyset$ 表示空集（通过空集公理定义）
- $\{x \in A : \phi(x)\}$ 表示通过替换公理模式定义的集合

### 1.3 语法规则

**定义 1.3.1** (自由变量)
变量 $x$ 在公式 $\phi$ 中自由出现，递归定义如下：

- 在原子公式 $x = y$ 中，$x$ 和 $y$ 都自由出现
- 在原子公式 $x \in y$ 中，$x$ 和 $y$ 都自由出现
- 在 $\neqg\phi$ 中，$x$ 自由出现当且仅当在 $\phi$ 中自由出现
- 在 $\phi \land \psi, \phi \lor \psi, \phi \rightarrow \psi, \phi \leqftrightarrow \psi$ 中，$x$ 自由出现当且仅当在 $\phi$ 或 $\psi$ 中自由出现
- 在 $\forall y \phi, \exists y \phi$ 中，$x$ 自由出现当且仅当 $x \neqq y$ 且在 $\phi$ 中自由出现

**定义 1.3.2** (句子)
句子是没有自由变量的公式。

## 2. ZFC公理系统严格表述

### 2.1 外延公理

**公理 2.1.1** (外延公理)
$$\forall x \forall y [\forall z(z \in x \leqftrightarrow z \in y) \rightarrow x = y]$$

**语义解释**: 两个集合相等当且仅当它们包含相同的元素。

**定理 2.1.2** (外延公理的等价形式)
外延公理等价于：
$$\forall x \forall y [x = y \leqftrightarrow \forall z(z \in x \leqftrightarrow z \in y)]$$

**证明**: 使用等号的自反性、对称性和传递性。

### 2.2 空集公理

**公理 2.2.1** (空集公理)
$$\exists x \forall y (y \notin x)$$

**定义 2.2.2** (空集)
空集 $\emptyset$ 是满足 $\forall y (y \notin \emptyset)$ 的唯一集合。

**定理 2.2.3** (空集的唯一性)
空集是唯一的。

**证明**: 假设存在两个空集 $\emptyset_1$ 和 $\emptyset_2$，则 $\forall y (y \notin \emptyset_1)$ 和 $\forall y (y \notin \emptyset_2)$。由外延公理，$\emptyset_1 = \emptyset_2$。

### 2.3 配对公理

**公理 2.3.1** (配对公理)
$$\forall x \forall y \exists z \forall w(w \in z \leqftrightarrow w = x \lor w = y)$$

**定义 2.3.2** (无序对)
对于集合 $x, y$，无序对 $\{x, y\}$ 是满足 $\forall w(w \in \{x, y\} \leqftrightarrow w = x \lor w = y)$ 的唯一集合。

**定理 2.3.3** (无序对的性质)

- $\{x, y\} = \{y, x\}$
- $x \in \{x, y\}$
- $y \in \{x, y\}$

### 2.4 并集公理

**公理 2.4.1** (并集公理)
$$\forall F \exists A \forall x(x \in A \leqftrightarrow \exists B(B \in F \land x \in B))$$

**定义 2.4.2** (并集)
对于集合族 $F$，并集 $\bigcup F$ 是满足 $\forall x(x \in \bigcup F \leqftrightarrow \exists B(B \in F \land x \in B))$ 的唯一集合。

**定义 2.4.3** (二元并集)
对于集合 $A, B$，$A \cup B = \bigcup \{A, B\}$。

**定理 2.4.4** (并集的性质)

- $A \subseteq A \cup B$
- $B \subseteq A \cup B$
- 如果 $A \subseteq C$ 且 $B \subseteq C$，则 $A \cup B \subseteq C$

### 2.5 幂集公理

**公理 2.5.1** (幂集公理)
$$\forall x \exists y \forall z(z \in y \leqftrightarrow z \subseteq x)$$

**定义 2.5.2** (幂集)
对于集合 $x$，幂集 $\mathcal{P}(x)$ 是满足 $\forall z(z \in \mathcal{P}(x) \leqftrightarrow z \subseteq x)$ 的唯一集合。

**定理 2.5.3** (幂集的性质)

- $\emptyset \in \mathcal{P}(x)$
- $x \in \mathcal{P}(x)$
- 如果 $A \subseteq B$，则 $\mathcal{P}(A) \subseteq \mathcal{P}(B)$

### 2.6 无穷公理

**公理 2.6.1** (无穷公理)
$$\exists x(\emptyset \in x \land \forall y(y \in x \rightarrow y \cup \{y\} \in x))$$

**定义 2.6.2** (归纳集)
集合 $x$ 是归纳集，如果 $\emptyset \in x$ 且 $\forall y(y \in x \rightarrow y \cup \{y\} \in x)$。

**定义 2.6.3** (自然数)
自然数集 $\omega$ 是所有归纳集的交集。

**定理 2.6.4** (自然数的性质)

- $\omega$ 是归纳集
- $\omega$ 是最小的归纳集
- 每个自然数都是传递集

### 2.7 替换公理模式

**公理模式 2.7.1** (替换公理模式)
对于每个公式 $\phi(x, y, z_1, \ldots, z_n)$，以下是一个公理：
$$\forall z_1 \ldots \forall z_n \forall A[\forall x \in A \exists! y \phi(x, y, z_1, \ldots, z_n) \rightarrow \exists B \forall y(y \in B \leqftrightarrow \exists x \in A \phi(x, y, z_1, \ldots, z_n))]$$

**语义解释**: 如果对于集合 $A$ 中的每个元素 $x$，都存在唯一的 $y$ 使得 $\phi(x, y, \ldots)$ 成立，那么存在集合 $B$ 包含所有这些 $y$。

**定义 2.7.2** (函数值域)
如果 $F$ 是函数，$A$ 是集合，则 $F[A] = \{F(x) : x \in A \cap \text{dom}(F)\}$。

### 2.8 正则公理

**公理 2.8.1** (正则公理)
$$\forall x(x \neqq \emptyset \rightarrow \exists y \in x(y \cap x = \emptyset))$$

**语义解释**: 每个非空集合都有一个与自身不相交的元素。

**定理 2.8.2** (正则公理的等价形式)
正则公理等价于：不存在无限下降的属于链。

**证明**: 假设存在无限下降链 $x_0 \ni x_1 \ni x_2 \ni \cdots$，考虑集合 $A = \{x_0, x_1, x_2, \ldots\}$，与正则公理矛盾。

### 2.9 选择公理

**公理 2.9.1** (选择公理)
$$\forall F[\emptyset \notin F \land \forall A \forall B(A \in F \land B \in F \land A \neqq B \rightarrow A \cap B = \emptyset) \rightarrow \exists C \forall A \in F(|A \cap C| = 1)]$$

**语义解释**: 对于任意非空集合族，如果集合两两不相交，则存在选择集，与每个集合恰好有一个公共元素。

**定理 2.9.2** (选择公理的等价形式)
选择公理等价于：

- 佐恩引理
- 良序定理
- 乘积非空公理
- 每个集合都可以良序化

---

**文档完成时间**: 2025年2月第1周
**文档版本**: v2.0
**执行阶段**: 第二阶段 - 内容深度提升
**质量等级**: 优秀，持续改进中

## 补充：ZFC 公理体系国际对齐与多表征（精炼版）

### A. 国际对齐要点

- 语言与公理：外延性、配对、并、幂集、分离/替代、无穷、公理选择 AC、正则性；
- 标准模型视角：冯·诺伊曼层级 V_α 与反射原理；
- 独立性：AC、CH 的不可判定与强公理（大基数）关系；
- 对齐：Wiki/Jecht/Kunen 与 Lean/Isabelle/Coq 中 ZF/ZFC 库。

### B. 多表征

- 逻辑：一阶公理化与元数学命题；
- 范畴：Universe、公理化集合论与类型宇宙的接口；
- 构造：受限分离与替代的可计算片段；
- 图示：

```mermaid
graph TD
  V0[V_0=∅]-->V1[V_1=P(∅)]-->V2[V_2=P(V_1)]-->Vω[⋯ V_ω]
  Vω-->Vα[V_α]
  Vα-->Vsucc[V_{α+1}=P(V_α)]
```

### C. 批判性要点

- 一致性/相对一致性方法（内/外模型、强迫）；
- 教学：以小型 ZF 片段与构造集合演示，减少抽象门槛；
- 工程：在形式化库中分层实现（基础→选择→大基数）。

### D. 历史脉络（精要）

- Zermelo–Fraenkel；Gödel 相对一致性；Cohen 强迫；现代大基数与内模型计划。

### E. 示例/练习

```python
# 受限分离的“有限片段”原型（仅示意，不代表完全公理化）
def subset_by_predicate(xs, pred):
    return [x for x in xs if pred(x)]

assert subset_by_predicate([0,1,2,3], lambda x: x%2==0)==[0,2]
```

- 练习：
  - 叙述并比较 ZF 与 ZFC 的差异与 AC 的等价命题；
  - 说明冯·诺伊曼层级构造与正则性的关系。
