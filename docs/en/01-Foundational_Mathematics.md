# Foundational Mathematics (基础数学)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 20 core concepts in foundational mathematics.

---

## 1. Set (集合)

### English Definition
A set is a well-defined collection of distinct objects, considered as an object in its own right. Sets are one of the most fundamental concepts in mathematics.

### 中文定义
集合是由确定的不同对象组成的一个整体，这些对象称为集合的元素。集合是数学中最基本的概念之一。

### Notation
- $A, B, C$: sets
- $a \in A$: element $a$ belongs to set $A$
- $a \notin A$: element $a$ does not belong to set $A$
- $\emptyset$ or $\varnothing$: empty set
- $|A|$ or $\#A$: cardinality of set $A$

### Example
- $A = \{1, 2, 3\}$ is a set containing three elements
- $\mathbb{N} = \{1, 2, 3, \ldots\}$ is the set of natural numbers
- $\emptyset$ is the empty set containing no elements

---

## 2. Subset (子集)

### English Definition
A set $A$ is a subset of set $B$, denoted $A \subseteq B$, if every element of $A$ is also an element of $B$. If $A \subseteq B$ and $A \neq B$, then $A$ is a proper subset of $B$, denoted $A \subset B$.

### 中文定义
如果集合$A$的每个元素都属于集合$B$，则称$A$是$B$的子集，记作$A \subseteq B$。如果$A \subseteq B$且$A \neq B$，则称$A$是$B$的真子集，记作$A \subset B$。

### Notation
- $A \subseteq B$: $A$ is a subset of $B$
- $A \subset B$: $A$ is a proper subset of $B$
- $\mathcal{P}(A)$ or $2^A$: power set of $A$ (set of all subsets)

### Example
- $\{1, 2\} \subseteq \{1, 2, 3\}$
- $\{1, 2, 3\} \subseteq \{1, 2, 3\}$ (every set is a subset of itself)
- $\mathcal{P}(\{1, 2\}) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$

---

## 3. Union (并集)

### English Definition
The union of two sets $A$ and $B$, denoted $A \cup B$, is the set of all elements that are in $A$, in $B$, or in both. For a collection of sets $\{A_i\}_{i \in I}$, the union is $\bigcup_{i \in I} A_i$.

### 中文定义
两个集合$A$和$B$的并集，记作$A \cup B$，是所有属于$A$或属于$B$的元素的集合。对于集合族$\{A_i\}_{i \in I}$，其并集记作$\bigcup_{i \in I} A_i$。

### Notation
- $A \cup B = \{x : x \in A \text{ or } x \in B\}$
- $\bigcup_{i \in I} A_i = \{x : \exists i \in I, x \in A_i\}$

### Example
- $\{1, 2\} \cup \{2, 3\} = \{1, 2, 3\}$
- $\bigcup_{n=1}^{\infty} \{n\} = \mathbb{N}$

---

## 4. Intersection (交集)

### English Definition
The intersection of two sets $A$ and $B$, denoted $A \cap B$, is the set of all elements that are in both $A$ and $B$. Two sets are disjoint if their intersection is empty.

### 中文定义
两个集合$A$和$B$的交集，记作$A \cap B$，是所有同时属于$A$和$B$的元素的集合。如果两个集合的交集为空集，则称它们不相交。

### Notation
- $A \cap B = \{x : x \in A \text{ and } x \in B\}$
- $\bigcap_{i \in I} A_i = \{x : \forall i \in I, x \in A_i\}$
- $A \cap B = \emptyset$: $A$ and $B$ are disjoint

### Example
- $\{1, 2, 3\} \cap \{2, 3, 4\} = \{2, 3\}$
- $\{1, 2\} \cap \{3, 4\} = \emptyset$ (disjoint sets)

---

## 5. Complement (补集)

### English Definition
Given a universal set $U$ and a subset $A \subseteq U$, the complement of $A$ (relative to $U$), denoted $A^c$ or $A'$, is the set of all elements in $U$ that are not in $A$.

### 中文定义
给定全集$U$和子集$A \subseteq U$，$A$（相对于$U$）的补集，记作$A^c$或$A'$，是$U$中所有不属于$A$的元素的集合。

### Notation
- $A^c = \{x \in U : x \notin A\}$
- $B \setminus A = \{x \in B : x \notin A\}$: set difference

### Example
- If $U = \{1, 2, 3, 4, 5\}$ and $A = \{1, 2\}$, then $A^c = \{3, 4, 5\}$
- $\{1, 2, 3\} \setminus \{2\} = \{1, 3\}$

---

## 6. Cartesian Product (笛卡尔积)

### English Definition
The Cartesian product of sets $A$ and $B$, denoted $A \times B$, is the set of all ordered pairs $(a, b)$ where $a \in A$ and $b \in B$. The $n$-fold product is denoted $A^n$.

### 中文定义
集合$A$和$B$的笛卡尔积，记作$A \times B$，是所有有序对$(a, b)$的集合，其中$a \in A$且$b \in B$。$n$重笛卡尔积记作$A^n$。

### Notation
- $A \times B = \{(a, b) : a \in A, b \in B\}$
- $A^n = A \times A \times \cdots \times A$ ($n$ times)

### Example
- $\{1, 2\} \times \{a, b\} = \{(1, a), (1, b), (2, a), (2, b)\}$
- $\mathbb{R}^2 = \mathbb{R} \times \mathbb{R}$ is the Euclidean plane

---

## 7. Relation (关系)

### English Definition
A relation $R$ from set $A$ to set $B$ is a subset of the Cartesian product $A \times B$. If $(a, b) \in R$, we write $aRb$ and say "$a$ is related to $b$".

### 中文定义
从集合$A$到集合$B$的关系$R$是笛卡尔积$A \times B$的一个子集。如果$(a, b) \in R$，我们记作$aRb$，并称"$a$与$b$有关系"。

### Notation
- $R \subseteq A \times B$: relation from $A$ to $B$
- $aRb$: $a$ is related to $b$
- $\text{dom}(R) = \{a : \exists b, (a, b) \in R\}$: domain
- $\text{ran}(R) = \{b : \exists a, (a, b) \in R\}$: range

### Example
- $<$ on $\mathbb{N}$: $\{(1, 2), (1, 3), (2, 3), \ldots\}$
- $=$ on any set: $\{(a, a) : a \in A\}$

---

## 8. Equivalence Relation (等价关系)

### English Definition
An equivalence relation on a set $A$ is a relation $\sim$ that is reflexive ($a \sim a$ for all $a$), symmetric (if $a \sim b$ then $b \sim a$), and transitive (if $a \sim b$ and $b \sim c$ then $a \sim c$).

### 中文定义
集合$A$上的等价关系$\sim$是一个满足以下三个性质的关系：自反性（对所有$a$有$a \sim a$）、对称性（若$a \sim b$则$b \sim a$）、传递性（若$a \sim b$且$b \sim c$则$a \sim c$）。

### Notation
- $a \sim b$: $a$ is equivalent to $b$
- $[a] = \{x : x \sim a\}$: equivalence class of $a$
- $A/\!\sim$: quotient set (set of all equivalence classes)

### Example
- Congruence modulo $n$: $a \equiv b \pmod{n}$ if $n | (a - b)$
- Similarity of triangles in geometry

---

## 9. Function/Map (函数/映射)

### English Definition
A function (or map) $f: A \to B$ is a relation from $A$ to $B$ such that for each $a \in A$, there exists exactly one $b \in B$ with $(a, b) \in f$. We write $f(a) = b$.

### 中文定义
函数（或映射）$f: A \to B$是从$A$到$B$的一个关系，使得对每个$a \in A$，存在唯一的$b \in B$使得$(a, b) \in f$。我们记作$f(a) = b$。

### Notation
- $f: A \to B$: function from $A$ to $B$
- $f(a)$: image of $a$ under $f$
- $f^{-1}(b) = \{a : f(a) = b\}$: preimage of $b$
- $\text{Im}(f) = \{f(a) : a \in A\}$: image of $f$

### Example
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x^2$
- Identity function: $\text{id}_A: A \to A$, $\text{id}_A(a) = a$

---

## 10. Injective Function (单射函数)

### English Definition
A function $f: A \to B$ is injective (one-to-one) if distinct elements of $A$ map to distinct elements of $B$: if $f(a_1) = f(a_2)$ then $a_1 = a_2$.

### 中文定义
函数$f: A \to B$是单射（或一一映射），如果$A$中不同元素映射到$B$中不同元素：若$f(a_1) = f(a_2)$，则$a_1 = a_2$。

### Notation
- $f: A \hookrightarrow B$: injective function
- $|A| \leq |B|$ if there exists an injection from $A$ to $B$

### Example
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = 2x + 1$ is injective
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x^2$ is not injective (since $f(-1) = f(1) = 1$)

---

## 11. Surjective Function (满射函数)

### English Definition
A function $f: A \to B$ is surjective (onto) if every element of $B$ is the image of at least one element of $A$: for all $b \in B$, there exists $a \in A$ such that $f(a) = b$.

### 中文定义
函数$f: A \to B$是满射（或映上映射），如果$B$中每个元素都至少是$A$中某个元素的像：对所有$b \in B$，存在$a \in A$使得$f(a) = b$。

### Notation
- $f: A \twoheadrightarrow B$: surjective function
- $|A| \geq |B|$ if there exists a surjection from $A$ to $B$

### Example
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x^3$ is surjective
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x^2$ is not surjective (negative numbers have no real square root)

---

## 12. Bijective Function (双射函数)

### English Definition
A function $f: A \to B$ is bijective if it is both injective and surjective. A bijection establishes a one-to-one correspondence between sets.

### 中文定义
函数$f: A \to B$是双射，如果它既是单射又是满射。双射建立了集合之间的一一对应关系。

### Notation
- $f: A \xrightarrow{\sim} B$: bijective function
- $|A| = |B|$ if there exists a bijection between $A$ and $B$

### Example
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x + 1$ is bijective
- Any linear function $f(x) = ax + b$ with $a \neq 0$ is bijective on $\mathbb{R}$

---

## 13. Natural Numbers (自然数)

### English Definition
The natural numbers $\mathbb{N} = \{1, 2, 3, \ldots\}$ (or $\{0, 1, 2, \ldots\}$ in some conventions) are the counting numbers used for enumeration. They satisfy the Peano axioms.

### 中文定义
自然数$\mathbb{N} = \{1, 2, 3, \ldots\}$（在某些约定中为$\{0, 1, 2, \ldots\}$）是用于计数的数。它们满足皮亚诺公理。

### Notation
- $\mathbb{N}$: set of natural numbers
- Peano axioms define the structure of natural numbers
- Successor function: $S(n) = n + 1$

### Example
- $1, 2, 3, \ldots$ are natural numbers
- $\mathbb{N}$ is well-ordered: every non-empty subset has a least element

---

## 14. Mathematical Induction (数学归纳法)

### English Definition
Mathematical induction is a proof technique for statements about natural numbers: prove the base case $P(1)$, then prove that $P(n) \implies P(n+1)$ for all $n \geq 1$.

### 中文定义
数学归纳法是证明关于自然数命题的一种方法：先证明基例$P(1)$成立，然后证明对所有$n \geq 1$，若$P(n)$成立则$P(n+1)$也成立。

### Notation
- Base case: $P(1)$ is true
- Inductive step: $P(n) \implies P(n+1)$
- Inductive hypothesis: assume $P(n)$ is true

### Example
- Prove $\sum_{k=1}^{n} k = \frac{n(n+1)}{2}$ by induction
- Base: $n=1$, LHS = 1, RHS = $\frac{1 \cdot 2}{2} = 1$ ✓
- Inductive step: assume true for $n$, prove for $n+1$

---

## 15. Integers (整数)

### English Definition
The integers $\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, \ldots\}$ extend the natural numbers to include negative numbers and zero, forming a commutative ring under addition and multiplication.

### 中文定义
整数$\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, \ldots\}$扩展了自然数，包含负数和零，在加法和乘法下构成一个交换环。

### Notation
- $\mathbb{Z}$: set of integers (from German "Zahlen")
- $\mathbb{Z}^+$: positive integers
- $\mathbb{Z}^-$: negative integers

### Example
- $-5, 0, 42$ are integers
- $\mathbb{Z}$ is closed under addition, subtraction, and multiplication

---

## 16. Rational Numbers (有理数)

### English Definition
The rational numbers $\mathbb{Q} = \{p/q : p, q \in \mathbb{Z}, q \neq 0\}$ are ratios of integers. They form a field, dense in the real numbers.

### 中文定义
有理数$\mathbb{Q} = \{p/q : p, q \in \mathbb{Z}, q \neq 0\}$是整数的比值。它们构成一个域，在实数中稠密。

### Notation
- $\mathbb{Q}$: set of rational numbers (from "quotient")
- $\frac{p}{q}$ or $p/q$: rational number with numerator $p$ and denominator $q$

### Example
- $\frac{1}{2}, -\frac{3}{4}, 5 = \frac{5}{1}$ are rational
- Between any two rationals, there exists another rational

---

## 17. Real Numbers (实数)

### English Definition
The real numbers $\mathbb{R}$ complete the rational numbers by filling in the "gaps" (Dedekind cuts or Cauchy sequences). They form a complete ordered field.

### 中文定义
实数$\mathbb{R}$通过填补"空隙"（戴德金分割或柯西序列）完备化了有理数。它们构成一个完备的有序域。

### Notation
- $\mathbb{R}$: set of real numbers
- $\mathbb{R}^+$: positive real numbers
- $\mathbb{R}^n$: $n$-dimensional Euclidean space

### Example
- $\sqrt{2}, \pi, e$ are real (but not rational)
- Every non-empty bounded subset of $\mathbb{R}$ has a supremum (completeness)

---

## 18. Complex Numbers (复数)

### English Definition
The complex numbers $\mathbb{C} = \{a + bi : a, b \in \mathbb{R}, i^2 = -1\}$ extend the real numbers by including the imaginary unit $i$. They form an algebraically closed field.

### 中文定义
复数$\mathbb{C} = \{a + bi : a, b \in \mathbb{R}, i^2 = -1\}$通过引入虚数单位$i$扩展了实数。它们构成一个代数闭域。

### Notation
- $\mathbb{C}$: set of complex numbers
- $z = a + bi$: complex number with real part $a$ and imaginary part $b$
- $\bar{z} = a - bi$: complex conjugate
- $|z| = \sqrt{a^2 + b^2}$: modulus

### Example
- $3 + 4i$, $2 - i$ are complex numbers
- $|3 + 4i| = \sqrt{9 + 16} = 5$

---

## 19. Counting Principle (计数原理)

### English Definition
Basic counting principles include: the Addition Principle (if $A$ and $B$ are disjoint, $|A \cup B| = |A| + |B|$), the Multiplication Principle ($|A \times B| = |A| \cdot |B|$), and the Subtraction Principle ($|A \setminus B| = |A| - |B|$ when $B \subseteq A$).

### 中文定义
基本计数原理包括：加法原理（若$A$和$B$不相交，则$|A \cup B| = |A| + |B|$）、乘法原理（$|A \times B| = |A| \cdot |B|$）、减法原理（当$B \subseteq A$时，$|A \setminus B| = |A| - |B|$）。

### Notation
- $|A|$: cardinality of set $A$
- $P(n, k) = \frac{n!}{(n-k)!}$: permutations
- $C(n, k) = \binom{n}{k} = \frac{n!}{k!(n-k)!}$: combinations

### Example
- Ways to arrange 5 books: $5! = 120$
- Ways to choose 3 from 10: $\binom{10}{3} = 120$

---

## 20. Power Set (幂集)

### English Definition
The power set of a set $A$, denoted $\mathcal{P}(A)$ or $2^A$, is the set of all subsets of $A$. If $A$ has $n$ elements, then $\mathcal{P}(A)$ has $2^n$ elements.

### 中文定义
集合$A$的幂集，记作$\mathcal{P}(A)$或$2^A$，是$A$的所有子集组成的集合。如果$A$有$n$个元素，则$\mathcal{P}(A)$有$2^n$个元素。

### Notation
- $\mathcal{P}(A) = \{X : X \subseteq A\}$
- $2^A$: alternative notation for power set
- $|\mathcal{P}(A)| = 2^{|A|}$

### Example
- $\mathcal{P}(\{1, 2\}) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$
- $\mathcal{P}(\emptyset) = \{\emptyset\}$ (the empty set has one subset: itself)

---

*End of Foundational Mathematics Concepts*
