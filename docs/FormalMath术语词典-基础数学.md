# FormalMath术语词典 - 基础数学

## 统一数学术语标准定义

---

## 📋 词典概述

本词典为FormalMath项目的基础数学术语提供统一、准确、标准化的定义。所有术语都遵循国际数学标准，确保在项目中的一致使用。

**词典原则**：

- **准确性**：术语定义准确无误
- **一致性**：术语使用保持一致
- **完整性**：覆盖基础数学所有重要术语
- **国际化**：符合国际数学标准

---

## 🔢 集合论术语 / Set Theory Terms

### 基本概念 / Basic Concepts

#### 集合 / Set

**中文定义**：集合是具有某种特定性质的事物的总体，这些事物称为该集合的元素。
**英文定义**：A set is a collection of distinct objects, considered as an object in its own right.
**符号表示**：$A, B, C, \ldots$
**示例**：$A = \{1, 2, 3\}$ 表示包含元素1、2、3的集合

#### 元素 / Element

**中文定义**：集合中的个体称为该集合的元素。
**英文定义**：An element is a member of a set.
**符号表示**：$a \in A$ 表示a是集合A的元素
**示例**：$1 \in \{1, 2, 3\}$ 表示1是集合$\{1, 2, 3\}$的元素

#### 子集 / Subset

**中文定义**：如果集合A的每个元素都是集合B的元素，则称A是B的子集。
**英文定义**：A set A is a subset of a set B if every element of A is also an element of B.
**符号表示**：$A \subseteq B$
**示例**：$\{1, 2\} \subseteq \{1, 2, 3\}$

#### 真子集 / Proper Subset

**中文定义**：如果A是B的子集且A不等于B，则称A是B的真子集。
**英文定义**：A set A is a proper subset of a set B if A is a subset of B and A is not equal to B.
**符号表示**：$A \subset B$
**示例**：$\{1, 2\} \subset \{1, 2, 3\}$

### 集合运算 / Set Operations

#### 并集 / Union

**中文定义**：两个集合的并集是包含两个集合所有元素的集合。
**英文定义**：The union of two sets is the set of all elements that are in either set.
**符号表示**：$A \cup B = \{x \mid x \in A \text{ or } x \in B\}$
**示例**：$\{1, 2\} \cup \{2, 3\} = \{1, 2, 3\}$

#### 交集 / Intersection

**中文定义**：两个集合的交集是同时属于两个集合的元素的集合。
**英文定义**：The intersection of two sets is the set of all elements that are in both sets.
**符号表示**：$A \cap B = \{x \mid x \in A \text{ and } x \in B\}$
**示例**：$\{1, 2\} \cap \{2, 3\} = \{2\}$

#### 差集 / Set Difference

**中文定义**：集合A与B的差集是A中不属于B的元素的集合。
**英文定义**：The set difference of A and B is the set of all elements in A that are not in B.
**符号表示**：$A \setminus B = \{x \mid x \in A \text{ and } x \notin B\}$
**示例**：$\{1, 2, 3\} \setminus \{2, 3\} = \{1\}$

#### 补集 / Complement

**中文定义**：在全集U中，集合A的补集是U中不属于A的元素的集合。
**英文定义**：The complement of a set A with respect to a universal set U is the set of all elements in U that are not in A.
**符号表示**：$A^c = U \setminus A$
**示例**：在全集$\{1, 2, 3, 4\}$中，$\{1, 2\}^c = \{3, 4\}$

### 特殊集合 / Special Sets

#### 空集 / Empty Set

**中文定义**：不包含任何元素的集合称为空集。
**英文定义**：The empty set is the set that contains no elements.
**符号表示**：$\emptyset$ 或 $\{\}$
**性质**：空集是任何集合的子集

#### 全集 / Universal Set

**中文定义**：在特定讨论范围内包含所有可能元素的集合称为全集。
**英文定义**：The universal set is the set that contains all objects under consideration.
**符号表示**：$U$ 或 $\Omega$
**示例**：在讨论自然数时，全集可以是所有自然数的集合

#### 幂集 / Power Set

**中文定义**：集合A的幂集是A的所有子集组成的集合。
**英文定义**：The power set of a set A is the set of all subsets of A.
**符号表示**：$\mathcal{P}(A)$ 或 $2^A$
**示例**：$\mathcal{P}(\{1, 2\}) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$

#### 笛卡尔积 / Cartesian Product

**中文定义**：两个集合A和B的笛卡尔积是所有有序对(a,b)的集合，其中a∈A，b∈B。
**英文定义**：The Cartesian product of two sets A and B is the set of all ordered pairs (a,b) where a∈A and b∈B.
**符号表示**：$A \times B = \{(a,b) \mid a \in A \text{ and } b \in B\}$
**示例**：$\{1, 2\} \times \{a, b\} = \{(1,a), (1,b), (2,a), (2,b)\}$

### 关系 / Relations

#### 关系 / Relation

**中文定义**：集合A到集合B的关系是A×B的一个子集。
**英文定义**：A relation from set A to set B is a subset of A×B.
**符号表示**：$R \subseteq A \times B$
**示例**：$R = \{(1,a), (2,b)\}$ 是$\{1,2\}$到$\{a,b\}$的关系

#### 等价关系 / Equivalence Relation

**中文定义**：在集合A上的关系R如果满足自反性、对称性和传递性，则称为等价关系。
**英文定义**：An equivalence relation on a set A is a relation that is reflexive, symmetric, and transitive.
**性质**：

- 自反性：$\forall a \in A, (a,a) \in R$
- 对称性：$\forall a,b \in A, (a,b) \in R \implies (b,a) \in R$
- 传递性：$\forall a,b,c \in A, (a,b) \in R \land (b,c) \in R \implies (a,c) \in R$

#### 偏序关系 / Partial Order

**中文定义**：在集合A上的关系R如果满足自反性、反对称性和传递性，则称为偏序关系。
**英文定义**：A partial order on a set A is a relation that is reflexive, antisymmetric, and transitive.
**性质**：

- 自反性：$\forall a \in A, (a,a) \in R$
- 反对称性：$\forall a,b \in A, (a,b) \in R \land (b,a) \in R \implies a = b$
- 传递性：$\forall a,b,c \in A, (a,b) \in R \land (b,c) \in R \implies (a,c) \in R$

#### 全序关系 / Total Order

**中文定义**：偏序关系如果还满足完全性（任意两个元素都可比较），则称为全序关系。
**英文定义**：A total order is a partial order that is also total (any two elements are comparable).
**性质**：$\forall a,b \in A, (a,b) \in R \lor (b,a) \in R$

### 函数 / Functions

#### 函数 / Function

**中文定义**：从集合A到集合B的函数f是A×B的一个子集，满足对A中的每个元素a，存在唯一的b∈B使得(a,b)∈f。
**英文定义**：A function f from set A to set B is a subset of A×B such that for each element a in A, there exists exactly one element b in B with (a,b) in f.
**符号表示**：$f: A \to B$
**示例**：$f(x) = x^2$ 是从实数集到实数集的函数

#### 定义域 / Domain

**中文定义**：函数f的定义域是A中所有元素的集合。
**英文定义**：The domain of a function f is the set of all elements in A.
**符号表示**：$\text{dom}(f) = A$

#### 值域 / Range

**中文定义**：函数f的值域是B中所有被f映射到的元素的集合。
**英文定义**：The range of a function f is the set of all elements in B that are mapped to by f.
**符号表示**：$\text{ran}(f) = \{f(a) \mid a \in A\}$

#### 单射 / Injective Function

**中文定义**：函数f如果满足不同的输入对应不同的输出，则称为单射。
**英文定义**：A function f is injective if different inputs correspond to different outputs.
**数学表述**：$\forall a_1, a_2 \in A, f(a_1) = f(a_2) \implies a_1 = a_2$

#### 满射 / Surjective Function

**中文定义**：函数f如果满足B中的每个元素都被映射到，则称为满射。
**英文定义**：A function f is surjective if every element in B is mapped to by f.
**数学表述**：$\forall b \in B, \exists a \in A, f(a) = b$

#### 双射 / Bijective Function

**中文定义**：函数f如果既是单射又是满射，则称为双射。
**英文定义**：A function f is bijective if it is both injective and surjective.
**性质**：双射函数存在逆函数

---

## 🔢 数系术语 / Number System Terms

### 自然数 / Natural Numbers

#### 自然数 / Natural Number

**中文定义**：自然数是用于计数的数，从1开始的正整数。
**英文定义**：Natural numbers are the numbers used for counting, starting from 1.
**符号表示**：$\mathbb{N} = \{1, 2, 3, \ldots\}$
**性质**：自然数集在加法下封闭

#### 皮亚诺公理 / Peano Axioms

**中文定义**：自然数的公理化定义，包括五个基本公理。
**英文定义**：The Peano axioms are the five basic axioms that define the natural numbers.
**公理内容**：

1. 0是自然数
2. 每个自然数都有唯一的后继
3. 0不是任何自然数的后继
4. 不同的自然数有不同的后继
5. 数学归纳原理

### 整数 / Integers

#### 整数 / Integer

**中文定义**：整数包括自然数、0和负整数。
**英文定义**：Integers include natural numbers, zero, and negative integers.
**符号表示**：$\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, \ldots\}$
**性质**：整数集在加法、减法和乘法下封闭

#### 正整数 / Positive Integer

**中文定义**：大于0的整数称为正整数。
**英文定义**：Positive integers are integers greater than zero.
**符号表示**：$\mathbb{Z}^+ = \{1, 2, 3, \ldots\}$

#### 负整数 / Negative Integer

**中文定义**：小于0的整数称为负整数。
**英文定义**：Negative integers are integers less than zero.
**符号表示**：$\mathbb{Z}^- = \{-1, -2, -3, \ldots\}$

### 有理数 / Rational Numbers

#### 有理数 / Rational Number

**中文定义**：有理数是可以表示为两个整数之比的数。
**英文定义**：Rational numbers are numbers that can be expressed as the ratio of two integers.
**符号表示**：$\mathbb{Q} = \{\frac{a}{b} \mid a, b \in \mathbb{Z}, b \neq 0\}$
**性质**：有理数集在加法、减法、乘法、除法下封闭

#### 分数 / Fraction

**中文定义**：分数是有理数的一种表示形式，由分子和分母组成。
**英文定义**：A fraction is a representation of a rational number as a ratio of two integers.
**符号表示**：$\frac{a}{b}$ 其中a是分子，b是分母

### 实数 / Real Numbers

#### 实数 / Real Number

**中文定义**：实数是包括有理数和无理数的数系。
**英文定义**：Real numbers include rational and irrational numbers.
**符号表示**：$\mathbb{R}$
**性质**：实数集是完备的有序域

#### 无理数 / Irrational Number

**中文定义**：无理数是不能表示为两个整数之比的实数。
**英文定义**：Irrational numbers are real numbers that cannot be expressed as the ratio of two integers.
**示例**：$\pi, \sqrt{2}, e$

#### 代数数 / Algebraic Number

**中文定义**：代数数是某个有理系数多项式的根。
**英文定义**：An algebraic number is a root of a polynomial with rational coefficients.
**示例**：$\sqrt{2}$ 是 $x^2 - 2 = 0$ 的根

#### 超越数 / Transcendental Number

**中文定义**：超越数不是任何有理系数多项式的根。
**英文定义**：A transcendental number is not a root of any polynomial with rational coefficients.
**示例**：$\pi, e$

### 复数 / Complex Numbers

#### 复数 / Complex Number

**中文定义**：复数是形如a+bi的数，其中a,b是实数，i是虚数单位。
**英文定义**：Complex numbers are numbers of the form a+bi where a,b are real numbers and i is the imaginary unit.
**符号表示**：$\mathbb{C} = \{a + bi \mid a, b \in \mathbb{R}\}$
**性质**：复数集是代数闭域

#### 虚数单位 / Imaginary Unit

**中文定义**：虚数单位i满足i² = -1。
**英文定义**：The imaginary unit i satisfies i² = -1.
**符号表示**：$i = \sqrt{-1}$

#### 实部 / Real Part

**中文定义**：复数a+bi的实部是a。
**英文定义**：The real part of a complex number a+bi is a.
**符号表示**：$\text{Re}(a + bi) = a$

#### 虚部 / Imaginary Part

**中文定义**：复数a+bi的虚部是b。
**英文定义**：The imaginary part of a complex number a+bi is b.
**符号表示**：$\text{Im}(a + bi) = b$

#### 共轭复数 / Complex Conjugate

**中文定义**：复数a+bi的共轭复数是a-bi。
**英文定义**：The complex conjugate of a+bi is a-bi.
**符号表示**：$\overline{a + bi} = a - bi$

### 基数与序数 / Cardinal and Ordinal Numbers

#### 基数 / Cardinal Number

**中文定义**：基数表示集合中元素的数量。
**英文定义**：Cardinal numbers represent the number of elements in a set.
**符号表示**：$|A|$ 表示集合A的基数
**示例**：$|\{1, 2, 3\}| = 3$

#### 序数 / Ordinal Number

**中文定义**：序数表示元素在有序集合中的位置。
**英文定义**：Ordinal numbers represent the position of elements in an ordered set.
**示例**：第一、第二、第三等

#### 无穷大 / Infinity

**中文定义**：无穷大表示比任何有限数都大的概念。
**英文定义**：Infinity represents a concept larger than any finite number.
**符号表示**：$\infty$
**性质**：无穷大不是实数

#### 无穷小 / Infinitesimal

**中文定义**：无穷小表示比任何正实数都小的概念。
**英文定义**：Infinitesimal represents a concept smaller than any positive real number.
**性质**：无穷小不是实数

---

## 🔍 逻辑术语 / Logic Terms

### 命题逻辑 / Propositional Logic

#### 命题 / Proposition

**中文定义**：命题是可以判断真假的陈述句。
**英文定义**：A proposition is a statement that can be determined to be true or false.
**示例**："2+2=4" 是一个真命题

#### 真值 / Truth Value

**中文定义**：命题的真值是真或假。
**英文定义**：The truth value of a proposition is true or false.
**符号表示**：T（真）或F（假）

#### 逻辑连接词 / Logical Connectives

**中文定义**：逻辑连接词是用于连接命题的符号。
**英文定义**：Logical connectives are symbols used to connect propositions.

##### 否定 / Negation

**中文定义**：否定连接词表示"非"。
**英文定义**：The negation connective represents "not".
**符号表示**：$\neg p$ 或 $\sim p$

##### 合取 / Conjunction

**中文定义**：合取连接词表示"且"。
**英文定义**：The conjunction connective represents "and".
**符号表示**：$p \land q$

##### 析取 / Disjunction

**中文定义**：析取连接词表示"或"。
**英文定义**：The disjunction connective represents "or".
**符号表示**：$p \lor q$

##### 蕴含 / Implication

**中文定义**：蕴含连接词表示"如果...那么..."。
**英文定义**：The implication connective represents "if...then...".
**符号表示**：$p \implies q$

##### 等价 / Equivalence

**中文定义**：等价连接词表示"当且仅当"。
**英文定义**：The equivalence connective represents "if and only if".
**符号表示**：$p \iff q$

### 谓词逻辑 / Predicate Logic

#### 谓词 / Predicate

**中文定义**：谓词是包含变量的命题函数。
**英文定义**：A predicate is a propositional function containing variables.
**示例**：P(x) = "x是偶数"

#### 量词 / Quantifiers

##### 全称量词 / Universal Quantifier

**中文定义**：全称量词表示"对所有"。
**英文定义**：The universal quantifier represents "for all".
**符号表示**：$\forall x$

##### 存在量词 / Existential Quantifier

**中文定义**：存在量词表示"存在"。
**英文定义**：The existential quantifier represents "there exists".
**符号表示**：$\exists x$

##### 唯一存在量词 / Unique Existential Quantifier

**中文定义**：唯一存在量词表示"存在唯一"。
**英文定义**：The unique existential quantifier represents "there exists exactly one".
**符号表示**：$\exists! x$

### 逻辑概念 / Logical Concepts

#### 矛盾 / Contradiction

**中文定义**：矛盾是永远为假的命题。
**英文定义**：A contradiction is a proposition that is always false.
**示例**：$p \land \neg p$

#### 重言式 / Tautology

**中文定义**：重言式是永远为真的命题。
**英文定义**：A tautology is a proposition that is always true.
**示例**：$p \lor \neg p$

#### 推理 / Inference

**中文定义**：推理是从已知命题推出新命题的过程。
**英文定义**：Inference is the process of deriving new propositions from known ones.
**示例**：从"所有人都会死"和"苏格拉底是人"推出"苏格拉底会死"

#### 证明 / Proof

**中文定义**：证明是通过逻辑推理验证命题为真的过程。
**英文定义**：A proof is the process of verifying that a proposition is true through logical reasoning.
**方法**：直接证明、反证法、数学归纳法等

#### 公理 / Axiom

**中文定义**：公理是不需要证明的基本假设。
**英文定义**：An axiom is a basic assumption that does not require proof.
**示例**：欧几里得几何的公理

#### 定理 / Theorem

**中文定义**：定理是通过证明得到的真命题。
**英文定义**：A theorem is a true proposition obtained through proof.
**示例**：勾股定理

#### 引理 / Lemma

**中文定义**：引理是为证明主要定理而使用的辅助命题。
**英文定义**：A lemma is an auxiliary proposition used to prove a main theorem.
**特点**：通常比定理简单

#### 推论 / Corollary

**中文定义**：推论是从定理直接推出的简单结论。
**英文定义**：A corollary is a simple conclusion directly derived from a theorem.
**特点**：通常不需要额外证明

---

## 📊 术语使用规范

### 术语定义格式

#### 标准定义格式

每个术语应包含以下要素：

1. **中文定义**：准确、简洁的中文定义
2. **英文定义**：对应的英文定义
3. **符号表示**：相关的数学符号
4. **示例**：具体的使用示例
5. **性质**：重要的性质或特点

#### 术语分类标准

- 按数学分支分类
- 按概念层次分类
- 按使用频率分类

### 术语一致性要求

#### 使用原则

1. **统一性**：同一术语在整个项目中保持一致的表述
2. **准确性**：术语定义准确无误
3. **完整性**：术语定义包含必要的信息
4. **国际化**：符合国际数学标准

#### 检查清单

- [ ] 术语定义是否准确
- [ ] 中英文对照是否完整
- [ ] 符号表示是否正确
- [ ] 示例是否恰当
- [ ] 是否与项目其他部分一致

---

**词典创建时间**: 2025年1月  
**词典版本**: v1.0  
**维护状态**: 持续更新中  
**适用范围**: FormalMath项目所有文档
