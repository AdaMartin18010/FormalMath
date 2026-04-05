---
title: Logic and Foundations (逻辑与基础)
msc_primary: 00A99
processed_at: '2026-04-05'
---
# Logic and Foundations (逻辑与基础)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 30 core concepts in mathematical logic and foundations.

---

## 1. First-Order Logic (一阶逻辑)

**MSC Code:** 03B10, 03Cxx

### English Definition
First-order logic is a formal system with quantifiers $\forall$ and $\exists$ ranging over elements of a domain (not sets of elements). It includes logical connectives ($\neg$, $\wedge$, $\vee$, $\rightarrow$, $\leftrightarrow$), equality, and predicate/relation symbols.

### 中文定义
一阶逻辑是形式系统，量词$\forall$和$\exists$遍历域的元素（而非元素的集合）。它包括逻辑连接词（$\neg$、$\wedge$、$\vee$、$\rightarrow$、$\leftrightarrow$）、等式和谓词/关系符号。

### Notation
- Variables: $x, y, z, \ldots$
- Predicates: $P(x), Q(x,y)$
- Formulas: $\varphi, \psi$
- $\models$: semantic entailment
- $\vdash$: syntactic derivability

### Example
- $\forall x (P(x) \rightarrow Q(x))$: all $P$ are $Q$
- $\exists x \forall y (x \cdot y = y)$: existence of identity
- Group axioms in first-order language

---

## 2. Propositional Logic (命题逻辑)

**MSC Code:** 03B05

### English Definition
Propositional logic studies formulas built from atomic propositions using connectives. It has completeness (tautologies are provable) and decidability (truth tables decide satisfiability). It forms the foundation of digital circuit design.

### 中文定义
命题逻辑研究用连接词从原子命题构建的公式。它具有完备性（重言式可证）和可判定性（真值表判定可满足性）。它构成数字电路设计的基础。

### Notation
- Atomic propositions: $p, q, r$
- Truth values: $\top$ (true), $\bot$ (false)
- Connectives: $\neg$, $\wedge$, $\vee$, $\rightarrow$, $\leftrightarrow$
- Tautology: always true
- Contradiction: always false

### Example
- Modus ponens: $p$, $p \rightarrow q$ $\vdash$ $q$
- De Morgan's laws: $\neg(p \wedge q) \equiv \neg p \vee \neg q$
- DNF, CNF: normal forms

---

## 3. Completeness Theorem (完备性定理)

**MSC Code:** 03C35, 03Fxx

### English Definition
Gödel's completeness theorem states that a formula is provable in first-order logic iff it is valid (true in all models). Equivalently, every consistent theory has a model. This connects syntax and semantics.

### 中文定义
哥德尔完备性定理表明公式在一阶逻辑中可证当且仅当它有效（在所有模型中为真）。等价地，每个一致理论都有模型。这联系语法和语义。

### Notation
- $\Gamma \vdash \varphi$ iff $\Gamma \models \varphi$
- Consistent: no contradiction derivable
- Henkin construction for model building

### Example
- First-order logic is complete
- Second-order logic is incomplete
- Non-standard models of arithmetic

---

## 4. Incompleteness Theorem (不完备性定理)

**MSC Code:** 03F40

### English Definition
Gödel's incompleteness theorems: (1) Any consistent formal system $F$ containing arithmetic contains statements neither provable nor disprovable. (2) $F$ cannot prove its own consistency.

### 中文定义
哥德尔不完备性定理：(1) 任何包含算术的一致形式系统$F$包含既不可证也不可否证的命题。(2) $F$不能证明自身的一致性。

### Notation
- Gödel sentence $G$: "I am not provable"
- Diagonalization
- Provability predicate $\text{Prov}_F(x)$

### Example
- Con(PA) is not provable in PA
- Goodstein's theorem: true but unprovable in PA
- Paris-Harrington theorem

---

## 5. Set Theory (集合论)

**MSC Code:** 03Exx

### English Definition
Set theory is the foundation of mathematics, studying sets and their properties. Zermelo-Fraenkel set theory with Choice (ZFC) is the standard axiomatization. Key concepts include ordinals, cardinals, and the cumulative hierarchy.

### 中文定义
集合论是数学的基础，研究集合及其性质。带选择的策梅洛-弗兰克尔集合论（ZFC）是标准公理化。关键概念包括序数、基数和累积层次。

### Notation
- $\in$: membership
- $\emptyset$: empty set
- $\mathcal{P}(X)$: power set
- Ordinals: $\alpha, \beta, \gamma$
- Cardinals: $\kappa, \lambda, \mu$

### Example
- Russell's paradox: $\{x : x \notin x\}$
- ZFC axioms: Extensionality, Pairing, Union, Power Set, Infinity, Replacement, Foundation, Choice
- Axiom of Choice and equivalents

---

## 6. Axiom of Choice (选择公理)

**MSC Code:** 03E25

### English Definition
The Axiom of Choice (AC) states that for any collection of non-empty sets, there exists a choice function selecting one element from each. It is independent of ZF and equivalent to Zorn's Lemma and the Well-Ordering Theorem.

### 中文定义
选择公理（AC）表明对任何非空集族，存在选择函数从每个集中选一个元素。它独立于ZF且等价于佐恩引理和良序定理。

### Notation
- Choice function: $f(X) \in X$
- AC $\Leftrightarrow$ Zorn's Lemma $\Leftrightarrow$ Well-Ordering Theorem
- Dependent Choice (DC)

### Example
- Every vector space has a basis
- Tychonoff's theorem
- Banach-Tarski paradox
- Non-measurable sets

---

## 7. Zorn's Lemma (佐恩引理)

**MSC Code:** 03E25

### English Definition
Zorn's Lemma: If every chain in a partially ordered set has an upper bound, then the set has a maximal element. It is equivalent to AC and widely used in algebra (existence of bases, maximal ideals).

### 中文定义
佐恩引理：如果偏序集中每个链都有上界，则该集有极大元。它等价于AC并广泛用于代数（基的存在、极大理想）。

### Notation
- Chain: totally ordered subset
- Upper bound
- Maximal element

### Example
- Every vector space has a basis
- Every ring has a maximal ideal
- Hahn-Banach theorem

---

## 8. Cardinal Number (基数)

**MSC Code:** 03E10

### English Definition
Cardinals measure the size of sets. Two sets have the same cardinality if there exists a bijection. Infinite cardinals include $\aleph_0$ (countable), $\aleph_1$, $\aleph_2$, etc. The Continuum Hypothesis concerns $2^{\aleph_0}$.

### 中文定义
基数度量集合的大小。如果存在双射则两集有相同基数。无穷基数包括$\aleph_0$（可数）、$\aleph_1$、$\aleph_2$等。连续统假设涉及$2^{\aleph_0}$。

### Notation
- $\aleph_0 = |\mathbb{N}|$
- $\mathfrak{c} = 2^{\aleph_0} = |\mathbb{R}|$
- $\kappa^+ =$ successor cardinal
- $\kappa + \lambda$, $\kappa \cdot \lambda$, $\kappa^\lambda$: cardinal arithmetic

### Example
- $|\mathbb{N}| = |\mathbb{Q}| = \aleph_0$
- $|\mathbb{R}| = |\mathcal{P}(\mathbb{N})| = 2^{\aleph_0}$
- CH: $2^{\aleph_0} = \aleph_1$ (independent of ZFC)

---

## 9. Ordinal Number (序数)

**MSC Code:** 03E10

### English Definition
Ordinals generalize natural numbers to infinite well-ordered sets. Each ordinal is the set of all smaller ordinals. They classify well-orderings and support transfinite induction and recursion.

### 中文定义
序数将自然数推广到无穷良序集。每个序数是所有更小序数的集合。它们分类良序并支持超限归纳和递归。

### Notation
- $\omega = \{0, 1, 2, \ldots\}$: first infinite ordinal
- $\omega + 1$, $\omega \cdot 2$, $\omega^2$: limit ordinals
- $\alpha + 1$: successor ordinal
- Limit ordinal: no predecessor

### Example
- Finite ordinals: natural numbers
- $\omega$, $\omega + 1$, $\omega + 2$, $\ldots$
- $\epsilon_0 = \omega^{\omega^{\omega^{\cdot^{\cdot^{\cdot}}}}}$: first fixed point of $\alpha \mapsto \omega^\alpha$

---

## 10. Continuum Hypothesis (连续统假设)

**MSC Code:** 03E50

### English Definition
The Continuum Hypothesis (CH) states $2^{\aleph_0} = \aleph_1$: there is no cardinal strictly between $\aleph_0$ and $2^{\aleph_0}$. It is independent of ZFC (proved by Gödel and Cohen).

### 中文定义
连续统假设（CH）表明$2^{\aleph_0} = \aleph_1$：$\aleph_0$和$2^{\aleph_0}$之间没有严格中间基数。它独立于ZFC（由哥德尔和科恩证明）。

### Notation
- CH: $2^{\aleph_0} = \aleph_1$
- GCH: $2^{\aleph_\alpha} = \aleph_{\alpha+1}$ for all $\alpha$
- Forcing: Cohen's method

### Example
- ZFC $\not\vdash$ CH (Cohen)
- ZFC $\not\vdash$ $\neg$CH (Godel)
- Large cardinals and CH

---

## 11. Forcing (力迫法)

**MSC Code:** 03E35, 03E40

### English Definition
Forcing, developed by Cohen, is a method for proving independence results in set theory. It adds "generic" sets to models of ZFC to create new models where specific statements are true or false.

### 中文定义
力迫法由科恩发展，是集合论中证明独立性结果的方法。它向ZFC模型添加"一般"集以创造新模型，使特定命题为真或为假。

### Notation
- Partial order $(P, \leq)$: forcing notion
- Generic filter $G$
- $M[G]$: generic extension
- Names for objects in extension

### Example
- Adding Cohen reals: $2^{\aleph_0} > \aleph_1$
- Suslin hypothesis
- Proper forcing

---

## 12. Large Cardinal (大基数)

**MSC Code:** 03E55, 03E60

### English Definition
Large cardinal axioms assert the existence of cardinals with strong properties (inaccessible, measurable, compact, etc.). They form a hierarchy of consistency strength and have applications in descriptive set theory.

### 中文定义
大基数公理断言具有强性质的基数存在（不可达、可测、紧等）。它们形成一致性强度的层次，在描述集合论中有应用。

### Notation
- Inaccessible: regular strong limit
- Measurable: $\kappa$-complete ultrafilter
- Woodin cardinals
- Determinacy from large cardinals

### Example
- Inaccessible cardinals cannot be proved in ZFC
- Measurable cardinals imply $V \neq L$
- Projective determinacy from Woodin cardinals

---

## 13. Model Theory (模型论)

**MSC Code:** 03Cxx

### English Definition
Model theory studies the relationship between formal theories and their models (structures satisfying the theory). Key results include the compactness theorem, Löwenheim-Skolem theorems, and Morley's categoricity theorem.

### 中文定义
模型论研究形式理论与其模型（满足理论的结构）之间的关系。主要结果包括紧致性定理、勒文海姆-斯科伦定理和莫利的范畴性定理。

### Notation
- Structure $\mathcal{M} = (M, \ldots)$
- $\mathcal{M} \models \varphi$: $\mathcal{M}$ satisfies $\varphi$
- $\text{Th}(\mathcal{M})$: theory of $\mathcal{M}$
- Elementary equivalence: $\mathcal{M} \equiv \mathcal{N}$

### Example
- Compactness: if every finite subset has a model, so does all
- Löwenheim-Skolem: infinite models of all infinite cardinals
- Categorical theories

---

## 14. Compactness Theorem (紧致性定理)

**MSC Code:** 03C07

### English Definition
The compactness theorem states that a set of first-order sentences has a model iff every finite subset has a model. It implies the existence of non-standard models and is foundational for model theory.

### 中文定义
紧致性定理表明一阶语句集有模型当且仅当每个有限子集有模型。它推出非标准模型的存在，是模型论的基础。

### Notation
- $\Sigma$ has model $\Leftrightarrow$ every finite $\Sigma_0 \subset \Sigma$ has model
- Topological proof via ultraproducts
- Applications to non-standard analysis

### Example
- Non-standard models of arithmetic
- Four color theorem for infinite graphs
- Ax-Kochen theorem

---

## 15. Elementary Equivalence (初等等价)

**MSC Code:** 03C07

### English Definition
Structures $\mathcal{M}$ and $\mathcal{N}$ are elementarily equivalent ($\mathcal{M} \equiv \mathcal{N}$) if they satisfy the same first-order sentences. Isomorphic structures are elementarily equivalent, but not conversely.

### 中文定义
结构$\mathcal{M}$和$\mathcal{N}$初等等价（$\mathcal{M} \equiv \mathcal{N}$）如果它们满足相同的一阶语句。同构结构初等等价，但反之不成立。

### Notation
- $\mathcal{M} \equiv \mathcal{N}$: elementarily equivalent
- $\mathcal{M} \cong \mathcal{N}$: isomorphic
- Elementary substructure: $\mathcal{M} \preceq \mathcal{N}$

### Example
- $(\mathbb{Q}, <) \equiv (\mathbb{R}, <)$ as ordered sets
- $(\mathbb{N}, +, \cdot) \not\equiv (\mathbb{N}^*, +, \cdot)$ for non-standard $\mathbb{N}^*$
- Elementary chains

---

## 16. Ultraproduct (超积)

**MSC Code:** 03C20

### English Definition
An ultraproduct is a construction combining structures using an ultrafilter. Łoś's theorem states that a first-order formula holds in the ultraproduct iff it holds in "most" factors. This gives algebraic proofs of compactness.

### 中文定义
超积是使用超滤子结合结构的构造。洛斯定理表明一阶公式在超积中成立当且仅当它在"大多数"因子中成立。这给出紧致性的代数证明。

### Notation
- Ultrafilter $\mathcal{U}$ on index set $I$
- $\prod_{i \in I} \mathcal{M}_i / \mathcal{U}$: ultraproduct
- Łoś's theorem

### Example
- Non-standard reals as ultrapower of $\mathbb{R}$
- Ax's theorem on polynomial maps
- Keisler-Shelah isomorphism theorem

---

## 17. Proof Theory (证明论)

**MSC Code:** 03Fxx

### English Definition
Proof theory studies formal proofs as mathematical objects. It analyzes the structure of proofs, proof transformations (cut elimination), and the consistency strength of theories. Ordinal analysis assigns ordinals to theories.

### 中文定义
证明论将形式证明作为数学对象研究。它分析证明的结构、证明变换（切消）和理论的一致性强度。序数分析给理论分配序数。

### Notation
- Sequent calculus
- Cut elimination
- Proof nets
- Ordinal analysis: $\|\text{Theory}\|$

### Example
- Gentzen's consistency proof of PA using $\epsilon_0$
- Cut elimination theorem
- Curry-Howard correspondence

---

## 18. Cut Elimination (切消)

**MSC Code:** 03F05

### English Definition
Cut elimination (Gentzen's Hauptsatz) transforms proofs so that the cut rule (modus ponens) is not used. The resulting cut-free proofs have the subformula property, enabling consistency proofs and automated reasoning.

### 中文定义
切消（根岑主定理）变换证明使得不使用切规则（假言推理）。所得的无切证明具有子公式性质，实现一致性证明和自动推理。

### Notation
- Cut rule: from $\Gamma \vdash A$ and $\Delta, A \vdash B$ infer $\Gamma, \Delta \vdash B$
- Cut-free proof
- Subformula property

### Example
- Gentzen's sequent calculus LK
- Proof complexity
- Linear logic and proof nets

---

## 19. Constructive Mathematics (构造数学)

**MSC Code:** 03F50, 03F55

### English Definition
Constructive mathematics requires proofs to provide explicit constructions or algorithms. It rejects the law of excluded middle for infinite sets and uses intuitionistic logic. Bishop's constructive analysis is a major development.

### 中文定义
构造数学要求证明提供显式构造或算法。它拒绝对无穷集使用排中律并使用直觉主义逻辑。毕晓普的构造分析是主要发展。

### Notation
- $\exists x P(x)$ requires construction of $x$
- $A \vee B$ requires deciding which holds
- BHK interpretation
- Realizability

### Example
- Every function is continuous (Brouwer)
- Intermediate value theorem: constructive version
- Martin-Löf type theory

---

## 20. Intuitionistic Logic (直觉主义逻辑)

**MSC Code:** 03B20, 03F55

### English Definition
Intuitionistic logic rejects the law of excluded middle ($P \vee \neg P$) and double negation elimination. A proposition is true only if proved, false only if refuted. It corresponds to constructive mathematics via BHK interpretation.

### 中文定义
直觉主义逻辑拒斥排中律（$P \vee \neg P$）和双重否定消去。命题仅当被证明时为真，仅当被反驳时为假。它通过BHK解释对应于构造数学。

### Notation
- $\nvdash P \vee \neg P$
- $\neg\neg P \nvdash P$ (but $P \vdash \neg\neg P$)
- Kripke semantics
- Heyting algebras

### Example
- Weak counterexamples (Brouwer)
- $\neg\neg\exists x P(x) \nvdash \exists x P(x)$
- Curry-Howard correspondence

---

## 21. Type Theory (类型论)

**MSC Code:** 03B15, 03B35

### English Definition
Type theory replaces the membership relation $\in$ with typing judgments $t : A$ (term $t$ has type $A$). It serves as foundation for computer proof assistants (Coq, Lean, Agda) and programming languages.

### 中文定义
类型论用类型判断$t : A$（项$t$具有类型$A$）代替隶属关系$\in$。它是计算机证明助手（Coq、Lean、Agda）和编程语言的基础。

### Notation
- $t : A$: term $t$ of type $A$
- $\Pi x:A. B(x)$: dependent product (universal quantification)
- $\Sigma x:A. B(x)$: dependent sum (existential quantification)
- Identity type: $Id_A(a, b)$ or $a =_A b$

### Example
- Simple type theory: Church, simply typed lambda calculus
- Martin-Löf type theory
- Homotopy type theory (HoTT)

---

## 22. Lambda Calculus (λ演算)

**MSC Code:** 03B40, 68N18

### English Definition
Lambda calculus is a formal system for expressing computation through function abstraction and application. It is Turing-complete and forms the foundation of functional programming languages.

### 中文定义
λ演算是通过函数抽象和应用表达计算的形式系统。它是图灵完备的，构成函数式编程语言的基础。

### Notation
- $\lambda x. M$: abstraction
- $M N$: application
- $(\lambda x. M) N \to_\beta M[x := N]$: $\beta$-reduction
- $\alpha$-conversion, $\eta$-conversion

### Example
- Church numerals: $\underline{n} = \lambda f. \lambda x. f^n x$
- Fixed point combinator: $Y = \lambda f. (\lambda x. f (x x)) (\lambda x. f (x x))$
- SKI combinators

---

## 23. Curry-Howard Correspondence (柯里-霍华德对应)

**MSC Code:** 03B35, 03B70

### English Definition
The Curry-Howard correspondence (propositions-as-types) identifies proofs with programs and propositions with types. Implication corresponds to function types, conjunction to product types, disjunction to sum types.

### 中文定义
柯里-霍华德对应（命题即类型）将证明与程序、命题与类型对应。蕴含对应函数类型，合取对应积类型，析取对应和类型。

### Notation
- Proof $\leftrightarrow$ Program
- Proposition $\leftrightarrow$ Type
- Normalization $\leftrightarrow$ Computation
- $A \rightarrow B$: function type

### Example
- Modus ponens $\leftrightarrow$ function application
- Proof by contradiction $\leftrightarrow$ continuations
- Type systems for programming languages

---

## 24. Homotopy Type Theory (同伦类型论)

**MSC Code:** 03B15, 55U40

### English Definition
Homotopy Type Theory (HoTT) extends Martin-Löf type theory by interpreting identity types as paths. It provides a synthetic foundation for homotopy theory and introduces the Univalence Axiom.

### 中文定义
同伦类型论（HoTT）通过将恒等类型解释为路径来延拓马丁-勒夫类型论。它为同伦论提供综合基础并引入单值性公理。

### Notation
- Identity type: $x =_A y$ (paths from $x$ to $y$)
- $\text{refl}_x$: constant path
- Path induction
- Univalence Axiom: $(A =_\mathcal{U} B) \simeq (A \simeq B)$

### Example
- Higher inductive types (HITs)
- Synthetic homotopy theory
- Calculating $\pi_n(S^k)$ in HoTT

---

## 25. Univalence Axiom (单值性公理)

**MSC Code:** 03B15, 55U40

### English Definition
The Univalence Axiom (Voevodsky) states that equivalent types are equal: $(A =_\mathcal{U} B) \simeq (A \simeq B)$. It implies function extensionality and is consistent with Martin-Löf type theory.

### 中文定义
单值性公理（沃耶沃茨基）表明等价类型相等：$(A =_\mathcal{U} B) \simeq (A \simeq B)$。它推出函数外延性并与马丁-勒夫类型论一致。

### Notation
- $\mathcal{U}$: universe of types
- $A \simeq B$: equivalence of types
- $=_{\mathcal{U}}$: identity in universe
- Transport along paths

### Example
- Function extensionality from univalence
- Structure identity principle
- Category theory in HoTT

---

## 26. Computability Theory (可计算性理论)

**MSC Code:** 03Dxx

### English Definition
Computability theory studies which functions can be computed algorithmically. Models include Turing machines, lambda calculus, and recursive functions. The Church-Turing thesis asserts these are equivalent.

### 中文定义
可计算性理论研究哪些函数可被算法计算。模型包括图灵机、λ演算和递归函数。丘奇-图灵论题断言这些是等价的。

### Notation
- Turing machine: $(Q, \Sigma, \Gamma, \delta, q_0, q_{accept}, q_{reject})$
- Computable/recursive function
- Halting problem
- $K = \{n : \varphi_n(n) \downarrow\}$: diagonal halting set

### Example
- Universal Turing machine
- Halting problem is undecidable
- Rice's theorem

---

## 27. Turing Machine (图灵机)

**MSC Code:** 03D10, 68Q05

### English Definition
A Turing machine is an abstract computational device with infinite tape, finite state control, and read/write head. It provides the foundation for computability theory and complexity theory.

### 中文定义
图灵机是具有无穷带、有限状态控制和读写头的抽象计算设备。它提供可计算性理论和复杂性理论的基础。

### Notation
- Tape alphabet $\Gamma$, input alphabet $\Sigma$
- Transition function $\delta: Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$
- Configuration: instantaneous description

### Example
- Machine for addition
- Universal Turing machine
- Busy beaver function

---

## 28. Halting Problem (停机问题)

**MSC Code:** 03D10, 68Q05

### English Definition
The halting problem asks whether a given program halts on given input. Turing proved it is undecidable: no algorithm can solve it for all inputs. It is the canonical undecidable problem.

### 中文定义
停机问题问给定程序在给定输入上是否停机。图灵证明它是不可判定的：没有算法能解决所有输入的情形。它是典型的不可判定问题。

### Notation
- $H = \{(M, x) : M \text{ halts on } x\}$
- Diagonalization proof
- Many-one reduction

### Example
- Proof by contradiction: machine that does opposite
- Undecidability of Post correspondence problem
- Rice's theorem: all non-trivial semantic properties undecidable

---

## 29. Computable Function (可计算函数)

**MSC Code:** 03D20, 03Dxx

### English Definition
A computable (recursive) function is one that can be computed by a Turing machine (equivalently: lambda calculus, recursive functions, register machines). The Church-Turing thesis identifies these with algorithmically computable functions.

### 中文定义
可计算（递归）函数是可被图灵机计算的函数（等价地：λ演算、递归函数、寄存器机）。丘奇-图灵论题将它们与算法可计算函数对应。

### Notation
- $\varphi_e$: partial computable function with index $e$
- Primitive recursive functions
- General recursive functions
- $\mu$-operator

### Example
- Addition, multiplication: primitive recursive
- Ackermann function: total computable, not primitive recursive
- Every total computable function is $\varphi_e$ for some $e$

---

## 30. Reverse Mathematics (逆数学)

**MSC Code:** 03B30, 03F35

### English Definition
Reverse mathematics determines which set-existence axioms are necessary to prove mathematical theorems. The base system RCA$_0$ proves many results; stronger systems like ACA$_0$, ATR$_0$, $\Pi^1_1$-CA$_0$ are required for others.

### 中文定义
逆数学确定哪些集合存在公理对证明数学定理是必要的。基础系统RCA$_0$证明许多结果；更强的系统如ACA$_0$、ATR$_0$、$\Pi^1_1$-CA$_0$对其他定理是必需的。

### Notation
- RCA$_0$: recursive comprehension
- ACA$_0$: arithmetical comprehension
- ATR$_0$: arithmetical transfinite recursion
- Big Five systems

### Example
- Bolzano-Weierstrass: equivalent to ACA$_0$
- Heine-Borel: equivalent to WKL$_0$
- Kruskal's tree theorem: ATR$_0$

---

*End of Logic and Foundations Concepts*
