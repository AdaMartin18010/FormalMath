---
title: Number Theory and Advanced Algebra (数论与高等代数)
msc_primary: 00

  - 00A99
processed_at: '2026-04-05'
---
# Number Theory and Advanced Algebra (数论与高等代数)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 50 core concepts in number theory and advanced algebra.

---

## 1. Algebraic Number (代数数)

**MSC Code:** @, 11R04

### English Definition
An algebraic number is a complex number $\alpha$ that is a root of a non-zero polynomial with rational coefficients. Equivalently, $\alpha$ is algebraic if $[\mathbb{Q}(\alpha):\mathbb{Q}] < \infty$.

### 中文定义
代数数是复数$\alpha$，是有理系数非零多项式的根。等价地，$\alpha$是代数的如果$[\mathbb{Q}(\alpha):\mathbb{Q}] < \infty$。

### Notation
- $\overline{\mathbb{Q}}$: field of algebraic numbers
- $[K:\mathbb{Q}]$: degree of field extension
- Minimal polynomial of $\alpha$

### Example
- $\sqrt{2}$: root of $x^2 - 2 = 0$
- $\zeta_n = e^{2\pi i/n}$: primitive $n$-th root of unity
- Transcendental: $e$, $\pi$ (not algebraic)

---

## 2. Algebraic Integer (代数整数)

**MSC Code:** 11R04

### English Definition
An algebraic integer is a complex number that is a root of a monic polynomial with integer coefficients. The set of algebraic integers in a number field $K$ forms a ring $\mathcal{O}_K$.

### 中文定义
代数整数是首一整系数多项式的根的复数。数域$K$中代数整数的集合形成环$\mathcal{O}_K$。

### Notation
- $\mathcal{O}_K$: ring of integers of number field $K$
- $\mathcal{O}_\mathbb{Q} = \mathbb{Z}$
- Norm $N(\alpha) = \prod_{\sigma} \sigma(\alpha)$

### Example
- $\sqrt{2}$: algebraic integer (root of $x^2 - 2$)
- $\frac{1+\sqrt{5}}{2}$: algebraic integer (root of $x^2 - x - 1$)
- $\frac{1}{2}$: not an algebraic integer

---

## 3. Number Field (数域)

**MSC Code:** @

### English Definition
A number field is a finite field extension $K/\mathbb{Q}$. It has the form $K = \mathbb{Q}(\alpha_1, \ldots, \alpha_n)$ for algebraic numbers $\alpha_i$. The degree $[K:\mathbb{Q}]$ is finite.

### 中文定义
数域是有限域扩张$K/\mathbb{Q}$。它具有形式$K = \mathbb{Q}(\alpha_1, \ldots, \alpha_n)$，其中$\alpha_i$是代数数。次数$[K:\mathbb{Q}]$有限。

### Notation
- $[K:\mathbb{Q}] = n$: degree of number field
- $\sigma_1, \ldots, \sigma_n: K \hookrightarrow \mathbb{C}$: embeddings
- $r_1$ real embeddings, $r_2$ pairs of complex embeddings: $r_1 + 2r_2 = n$

### Example
- Quadratic field: $\mathbb{Q}(\sqrt{d})$ for squarefree $d$
- Cyclotomic field: $\mathbb{Q}(\zeta_n)$, degree $\varphi(n)$
- $\mathbb{Q}(\sqrt[3]{2})$: pure cubic field, degree 3

---

## 4. Ring of Integers (整数环)

**MSC Code:** 11R04

### English Definition
The ring of integers $\mathcal{O}_K$ of a number field $K$ is the set of all algebraic integers in $K$. It is a Dedekind domain: Noetherian, integrally closed, and every non-zero prime ideal is maximal.

### 中文定义
数域$K$的整数环$\mathcal{O}_K$是$K$中所有代数整数的集合。它是戴德金整环：诺特、整闭、每个非零素理想极大。

### Notation
- $\mathcal{O}_K$: ring of integers
- Discriminant $\Delta_K$ of number field
- $\mathcal{O}_K \cong \mathbb{Z}^n$ as additive group

### Example
- $\mathcal{O}_{\mathbb{Q}(\sqrt{5})} = \mathbb{Z}[\frac{1+\sqrt{5}}{2}]$
- $\mathcal{O}_{\mathbb{Q}(\sqrt{-5})} = \mathbb{Z}[\sqrt{-5}]$ (not UFD)
- $\mathcal{O}_{\mathbb{Q}(\zeta_p)} = \mathbb{Z}[\zeta_p]$ for prime $p$

---

## 5. Ideal Class Group (理想类群)

**MSC Code:** 11R29

### English Definition
The ideal class group $\text{Cl}(K)$ of a number field $K$ is the group of fractional ideals modulo principal fractional ideals. It measures the failure of $\mathcal{O}_K$ to be a PID. It is always finite.

### 中文定义
数域$K$的理想类群$\text{Cl}(K)$是分式理想模主分式理想的群。它度量$\mathcal{O}_K$不是主理想整环的失败。它总是有限的。

### Notation
- $h_K = |\text{Cl}(K)|$: class number
- $\text{Cl}(K) = 1 \iff \mathcal{O}_K$ is UFD
- Ideal class $[\mathfrak{a}] \in \text{Cl}(K)$

### Example
- $\text{Cl}(\mathbb{Q}) = 1$
- $\text{Cl}(\mathbb{Q}(\sqrt{-5})) = \mathbb{Z}/2\mathbb{Z}$
- $\text{Cl}(\mathbb{Q}(\sqrt{-163})) = 1$ (Heegner number)

---

## 6. Discriminant (判别式)

**MSC Code:** 11R29

### English Definition
The discriminant $\Delta_K$ of a number field $K$ measures ramification. For $K = \mathbb{Q}(\alpha)$ with minimal polynomial $f$, $\Delta_K$ involves the product of differences of roots squared.

### 中文定义
数域$K$的判别式$\Delta_K$度量分歧。对于$K = \mathbb{Q}(\alpha)$，其极小多项式为$f$，$\Delta_K$涉及根的差乘积的平方。

### Notation
- $\Delta_K = \det(\text{Tr}_{K/\mathbb{Q}}(\alpha_i\alpha_j))$
- $\Delta(f) = \prod_{i<j}(\alpha_i - \alpha_j)^2$
- Prime $p$ ramifies in $K \iff p \mid \Delta_K$

### Example
- $\Delta_{\mathbb{Q}(\sqrt{d})} = d$ if $d \equiv 1 \pmod{4}$
- $\Delta_{\mathbb{Q}(\sqrt{-1})} = -4$
- $\Delta_{\mathbb{Q}(\zeta_p)} = (-1)^{(p-1)/2}p^{p-2}$

---

## 7. Dirichlet's Unit Theorem (狄利克雷单位定理)

**MSC Code:** 11R27

### English Definition
The unit group $\mathcal{O}_K^\times$ of a number field $K$ with $r_1$ real and $r_2$ complex embeddings is $\mathcal{O}_K^\times \cong \mu_K \times \mathbb{Z}^{r_1+r_2-1}$, where $\mu_K$ is the finite group of roots of unity in $K$.

### 中文定义
数域$K$的单位群$\mathcal{O}_K^\times$，有$r_1$个实嵌入和$r_2$对复嵌入，则$\mathcal{O}_K^\times \cong \mu_K \times \mathbb{Z}^{r_1+r_2-1}$，其中$\mu_K$是$K$中单位根的有限群。

### Notation
- Rank of unit group: $r_1 + r_2 - 1$
- Regulator: volume of fundamental domain
- Fundamental units: generators of free part

### Example
- $\mathbb{Q}$: $\mathbb{Z}^\times = \{\pm 1\}$
- $\mathbb{Q}(\sqrt{2})$: units $\pm(1+\sqrt{2})^n$
- Real quadratic: rank 1 unit group

---

## 8. Dedekind Zeta Function (戴德金ζ函数)

**MSC Code:** 11R42

### English Definition
The Dedekind zeta function $\zeta_K(s)$ of a number field $K$ is $\zeta_K(s) = \sum_{\mathfrak{a} \subseteq \mathcal{O}_K} N(\mathfrak{a})^{-s} = \prod_{\mathfrak{p}} (1 - N(\mathfrak{p})^{-s})^{-1}$, convergent for $\text{Re}(s) > 1$.

### 中文定义
数域$K$的戴德金ζ函数为$\zeta_K(s) = \sum_{\mathfrak{a} \subseteq \mathcal{O}_K} N(\mathfrak{a})^{-s} = \prod_{\mathfrak{p}} (1 - N(\mathfrak{p})^{-s})^{-1}$，在$\text{Re}(s) > 1$收敛。

### Notation
- $N(\mathfrak{a}) = |\mathcal{O}_K/\mathfrak{a}|$: ideal norm
- Analytic continuation to $\mathbb{C} \setminus \{1\}$
- $\text{Res}_{s=1}\zeta_K(s) = \frac{2^{r_1}(2\pi)^{r_2}h_K R_K}{w_K\sqrt{|\Delta_K|}}$

### Example
- $\zeta_\mathbb{Q}(s) = \zeta(s)$: Riemann zeta
- $\zeta_{\mathbb{Q}(i)}(s) = \zeta(s)L(s, \chi_{-4})$
- Analytic class number formula

---

## 9. Local Field (局部域)

**MSC Code:** @

### English Definition
A local field is a locally compact topological field with respect to a non-discrete topology. Examples include $\mathbb{R}$, $\mathbb{C}$ (archimedean) and finite extensions of $\mathbb{Q}_p$ or $\mathbb{F}_q((t))$ (non-archimedean).

### 中文定义
局部域是相对于非离散拓扑的局部紧拓扑域。例子包括$\mathbb{R}$、$\mathbb{C}$（阿基米德）和$\mathbb{Q}_p$或$\mathbb{F}_q((t))$的有限扩张（非阿基米德）。

### Notation
- $\mathbb{Q}_p$: $p$-adic numbers
- $\mathbb{Z}_p$: $p$-adic integers
- $|\cdot|_p$: $p$-adic absolute value
- $\mathcal{O}_K$: valuation ring

### Example
- $\mathbb{R}$, $\mathbb{C}$: archimedean local fields
- $\mathbb{Q}_p$: non-archimedean local field
- $\mathbb{F}_q((t))$: local function field

---

## 10. p-adic Number (p进数)

**MSC Code:** @

### English Definition
The field of $p$-adic numbers $\mathbb{Q}_p$ is the completion of $\mathbb{Q}$ with respect to the $p$-adic absolute value $|x|_p = p^{-v_p(x)}$. Elements have expansions $x = \sum_{n \geq N} a_n p^n$ with $a_n \in \{0, \ldots, p-1\}$.

### 中文定义
$p$进数域$\mathbb{Q}_p$是$\mathbb{Q}$关于$p$进绝对值$|x|_p = p^{-v_p(x)}$的完备化。元素有展开式$x = \sum_{n \geq N} a_n p^n$，其中$a_n \in \{0, \ldots, p-1\}$。

### Notation
- $|x|_p$: $p$-adic absolute value (ultrametric)
- $\mathbb{Z}_p = \{x \in \mathbb{Q}_p : |x|_p \leq 1\}$: $p$-adic integers
- $v_p(x) = -\log_p|x|_p$: $p$-adic valuation

### Example
- $-1 = \sum_{n=0}^\infty (p-1)p^n$ in $\mathbb{Z}_p$
- $\frac{1}{1-p} = \sum_{n=0}^\infty p^n$ in $\mathbb{Z}_p$
- Hensel's lemma: lifting roots mod $p^n$

---

## 11. Adele (阿代尔)

**MSC Code:** 11R56

### English Definition
The adele ring $\mathbb{A}_K$ of a number field $K$ is the restricted product $\prod'_{v} K_v$ over all places $v$, consisting of tuples $(x_v)$ with $x_v \in \mathcal{O}_v$ for almost all $v$. It is a locally compact ring.

### 中文定义
数域$K$的阿代尔环$\mathbb{A}_K$是所有位$v$上的限制积$\prod'_{v} K_v$，由满足几乎所有$v$有$x_v \in \mathcal{O}_v$的元组$(x_v)$组成。它是局部紧环。

### Notation
- $\mathbb{A}_\mathbb{Q} = \mathbb{R} \times \prod'_p \mathbb{Q}_p$
- $\mathbb{I}_K = \mathbb{A}_K^\times$: idele group
- $K \hookrightarrow \mathbb{A}_K$: diagonal embedding (discrete and cocompact)

### Example
- Strong approximation theorem
- $\mathbb{A}_\mathbb{Q}/\mathbb{Q}$ is compact
- Tate's thesis: functional equation via adeles

---

## 12. Idele (伊代尔)

**MSC Code:** 11R56

### English Definition
The idele group $\mathbb{I}_K = \mathbb{A}_K^\times$ is the group of units of the adele ring. It contains the subgroup of principal ideles $K^\times$ (diagonally embedded). The idele class group $\mathbb{I}_K/K^\times$ is central in class field theory.

### 中文定义
伊代尔群$\mathbb{I}_K = \mathbb{A}_K^\times$是阿代尔环的单位群。它包含主伊代尔子群$K^\times$（对角嵌入）。伊代尔类群$\mathbb{I}_K/K^\times$在类域论中居核心地位。

### Notation
- $|\cdot|_\mathbb{A}$: idele norm (product of local norms)
- $\mathbb{I}_K^1 = \ker|\cdot|_\mathbb{A}$: norm-1 ideles
- $\mathbb{I}_K/K^\times \cdot K_\infty^\times \cong \text{Cl}(K)$

### Example
- $\mathbb{I}_\mathbb{Q} = \mathbb{R}^\times \times \prod'_p \mathbb{Q}_p^\times$
- Global reciprocity law: $\mathbb{I}_K/\overline{K^\times} \cong \text{Gal}(K^{ab}/K)$
- Hilbert class field via ideles

---

## 13. Class Field Theory (类域论)

**MSC Code:** 11R37

### English Definition
Class field theory describes abelian extensions of number fields. For $L/K$ abelian, there is a reciprocity isomorphism $\text{Gal}(L/K) \cong \mathbb{I}_K/(K^\times \cdot N_{L/K}(\mathbb{I}_L))$. The Hilbert class field has Galois group $\text{Cl}(K)$.

### 中文定义
类域论描述数域的阿贝尔扩张。对于$L/K$阿贝尔，存在互反同构$\text{Gal}(L/K) \cong \mathbb{I}_K/(K^\times \cdot N_{L/K}(\mathbb{I}_L))$。希尔伯特类域的伽罗瓦群为$\text{Cl}(K)$。

### Notation
- $(a, L/K)$: Artin symbol
- $H_K$: Hilbert class field (maximal unramified abelian extension)
- Ray class field: generalization with conductor

### Example
- $\mathbb{Q}(\sqrt{-5}(\sqrt{5}))$: Hilbert class field of $\mathbb{Q}(\sqrt{-5})$
- Cyclotomic fields over $\mathbb{Q}$: ray class fields
- Kronecker-Weber: every abelian extension of $\mathbb{Q}$ in cyclotomic

---

## 14. Elliptic Curve (椭圆曲线)

**MSC Code:** 11G05, 14H52

### English Definition
An elliptic curve $E$ over a field $K$ is a smooth projective genus-1 curve with a specified point $O$ (identity). It has a Weierstrass model $y^2 = x^3 + ax + b$ with non-zero discriminant $\Delta = -16(4a^3 + 27b^2)$.

### 中文定义
域$K$上的椭圆曲线$E$是指定基点$O$（单位元）的光滑射影亏格1曲线。它有魏尔斯特拉斯模型$y^2 = x^3 + ax + b$，判别式$\Delta = -16(4a^3 + 27b^2) \neq 0$。

### Notation
- $E(K)$: group of $K$-rational points
- $y^2 = x^3 + ax + b$: Weierstrass equation
- $j$-invariant: $j(E) = 1728\frac{4a^3}{4a^3+27b^2}$

### Example
- $y^2 = x^3 - x$ over $\mathbb{Q}$
- $E(\mathbb{C}) \cong \mathbb{C}/\Lambda$ for lattice $\Lambda$
- $E(\mathbb{F}_p)$: finite group of points

---

## 15. Mordell-Weil Theorem (莫德尔-魏尔定理)

**MSC Code:** 11G10

### English Definition
For an elliptic curve $E$ over a number field $K$, the group $E(K)$ of rational points is finitely generated: $E(K) \cong E(K)_{tors} \times \mathbb{Z}^r$. The non-negative integer $r$ is the rank of $E$ over $K$.

### 中文定义
对于数域$K$上的椭圆曲线$E$，有理点群$E(K)$有限生成：$E(K) \cong E(K)_{tors} \times \mathbb{Z}^r$。非负整数$r$是$E$在$K$上的秩。

### Notation
- $r = \text{rank}(E/K)$: Mordell-Weil rank
- $E(K)_{tors}$: torsion subgroup (finite, bounded by Mazur's theorem for $\mathbb{Q}$)
- Height function: measuring point complexity

### Example
- $E: y^2 = x^3 - x$ has rank 0 over $\mathbb{Q}$
- $E: y^2 = x^3 - 2$ has rank 0, torsion trivial
- Congruent number problem: ranks of quadratic twists

---

## 16. L-function (L函数)

**MSC Code:** @, @

### English Definition
An L-function is a Dirichlet series $L(s) = \sum_{n=1}^\infty a_n n^{-s}$ with Euler product, analytic continuation, and functional equation. Examples include Riemann zeta, Dirichlet L-functions, and Hasse-Weil L-functions of varieties.

### 中文定义
L函数是狄利克雷级数$L(s) = \sum_{n=1}^\infty a_n n^{-s}$，具有欧拉乘积、解析延拓和函数方程。例子包括黎曼ζ、狄利克雷L函数和簇的哈塞-魏尔L函数。

### Notation
- $L(s, \chi) = \sum_n \chi(n)n^{-s}$: Dirichlet L-function
- $L(E, s)$: Hasse-Weil L-function of elliptic curve
- $L(s, \pi)$: automorphic L-function

### Example
- $\zeta(s) = L(s, \chi_0)$: Riemann zeta
- $L(s, \chi_{-4}) = \sum_n \chi_{-4}(n)n^{-s}$: Dirichlet character mod 4
- BSD conjecture: $L(E, 1)$ and rank of $E$

---

## 17. Modular Form (模形式)

**MSC Code:** 11F11, @

### English Definition
A modular form of weight $k$ for $SL(2, \mathbb{Z})$ is a holomorphic function $f: \mathbb{H} \to \mathbb{C}$ satisfying $f\left(\frac{az+b}{cz+d}\right) = (cz+d)^k f(z)$ for $\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in SL(2, \mathbb{Z})$, holomorphic at $\infty$.

### 中文定义
$SL(2, \mathbb{Z})$的权$k$模形式是全纯函数$f: \mathbb{H} \to \mathbb{C}$，满足对$\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in SL(2, \mathbb{Z})$有$f\left(\frac{az+b}{cz+d}\right) = (cz+d)^k f(z)$，且在$\infty$处全纯。

### Notation
- $M_k$: space of modular forms of weight $k$
- $S_k$: cusp forms
- $q$-expansion: $f(z) = \sum_{n=0}^\infty a_n q^n$, $q = e^{2\pi i z}$

### Example
- $\Delta(z) = q\prod_{n=1}^\infty (1-q^n)^{24}$: weight 12 cusp form
- $E_k$: Eisenstein series
- $\theta$-series associated to quadratic forms

---

## 18. Hecke Operator (赫克算子)

**MSC Code:** 11F25

### English Definition
Hecke operators $T_n$ act on modular forms and preserve the spaces $M_k$ and $S_k$. They are self-adjoint with respect to the Petersson inner product and simultaneously diagonalizable. Eigenforms have Euler product L-functions.

### 中文定义
赫克算子$T_n$作用在模形式上并保持空间$M_k$和$S_k$。它们关于彼得松内积自伴且可同时对角化。特征形式具有欧拉乘积L函数。

### Notation
- $T_n: M_k \to M_k$ for $n \geq 1$
- $T_m T_n = T_{mn}$ when $(m,n) = 1$
- Eigenform: $T_n f = \lambda_n f$ for all $n$

### Example
- $\Delta$ is Hecke eigenform: $T_n \Delta = \tau(n) \Delta$
- Ramanujan $\tau$-function
- $L(f, s) = \sum_n a_n n^{-s}$ for eigenform has Euler product

---

## 19. Galois Representation (伽罗瓦表示)

**MSC Code:** 11F80, 11R32

### English Definition
A Galois representation is a continuous homomorphism $\rho: G_K \to GL(V)$ where $G_K = \text{Gal}(\overline{K}/K)$ and $V$ is a vector space over a topological field. They encode arithmetic information about $K$.

### 中文定义
伽罗瓦表示是连续同态$\rho: G_K \to GL(V)$，其中$G_K = \text{Gal}(\overline{K}/K)$，$V$是拓扑域上的向量空间。它们编码$K$的算术信息。

### Notation
- $G_\mathbb{Q} = \text{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$
- $\ell$-adic representation: $V$ over $\mathbb{Q}_\ell$
- $\rho: G_\mathbb{Q} \to GL_2(\mathbb{Q}_\ell)$ from elliptic curves

### Example
- Cyclotomic character: $\chi_\ell: G_\mathbb{Q} \to \mathbb{Z}_\ell^\times$
- Tate module $T_\ell(E)$: 2-dimensional $\ell$-adic representation
- Modularity: 2-dim odd representations come from modular forms

---

## 20. Modularity Theorem (模性定理)

**MSC Code:** 11G05, 11F80

### English Definition
The modularity theorem (Wiles-Taylor et al.) states that every elliptic curve over $\mathbb{Q}$ is modular: there exists a weight-2 cusp form $f$ such that $L(E, s) = L(f, s)$. This was the key to proving Fermat's Last Theorem.

### 中文定义
模性定理（怀尔斯-泰勒等）表明$\mathbb{Q}$上每条椭圆曲线是模性的：存在权2尖点形式$f$使得$L(E, s) = L(f, s)$。这是证明费马大定理的关键。

### Notation
- $E$ modular: $L(E, s) = L(f, s)$ for some $f \in S_2(\Gamma_0(N))$
- Conductor $N_E$: level of associated modular form
- Taniyama-Shimura-Weil conjecture: old name

### Example
- Semistable $E/\mathbb{Q}$ is modular (Wiles)
- Every $E/\mathbb{Q}$ is modular (BCDT)
- Frey curve: semistable with unusual properties

---

## 21. Arithmetic Geometry (算术几何)

**MSC Code:** @, @

### English Definition
Arithmetic geometry studies solutions of polynomial equations over arithmetic fields (number fields, finite fields, $p$-adic fields). It combines algebraic geometry with number theory, using schemes and cohomology.

### 中文定义
算术几何研究算术域（数域、有限域、$p$进域）上多项式方程的解。它结合代数几何与数论，使用概形和上同调。

### Notation
- Scheme over $\text{Spec}(\mathbb{Z})$: arithmetic scheme
- $X(\mathbb{F}_q)$: rational points over finite field
- Reduction mod $p$: connecting global and local

### Example
- Diophantine equations: rational/integer solutions
- Weil conjectures: zeta functions of varieties over $\mathbb{F}_q$
- Arakelov theory: arithmetic intersection theory

---

## 22. Diophantine Equation (丢番图方程)

**MSC Code:** @

### English Definition
A Diophantine equation is a polynomial equation $f(x_1, \ldots, x_n) = 0$ where integer or rational solutions are sought. The study includes local-global principles, bounds on solutions, and decidability questions.

### 中文定义
丢番图方程是多项式方程$f(x_1, \ldots, x_n) = 0$，寻求整数或有理解。研究包括局部-整体原则、解的界和可判定性问题。

### Notation
- $X(\mathbb{Z})$: integer points
- $X(\mathbb{Q})$: rational points
- Local-to-global principle: Hasse principle

### Example
- Pell's equation: $x^2 - Dy^2 = 1$
- Fermat: $x^n + y^n = z^n$ for $n \geq 3$
- $y^2 = x^3 + k$: Mordell equations

---

## 23. Group Representation (群表示)

**MSC Code:** @, @

### English Definition
A representation of group $G$ is a homomorphism $\rho: G \to GL(V)$ for vector space $V$. It encodes group structure as linear transformations, enabling character theory and harmonic analysis on groups.

### 中文定义
群$G$的表示是同态$\rho: G \to GL(V)$，其中$V$是向量空间。它将群结构编码为线性变换，实现特征标理论和群上的调和分析。

### Notation
- $(\rho, V)$ or just $V$: representation
- Character: $\chi_\rho(g) = \text{tr}(\rho(g))$
- $\text{Hom}_G(V, W)$: intertwining operators

### Example
- Trivial representation: $\rho(g) = I$ for all $g$
- Regular representation: $G$ acts on $\mathbb{C}[G]$
- Permutation representation: $G$ acts on set $X$

---

## 24. Character Theory (特征标理论)

**MSC Code:** 20C15

### English Definition
Character theory studies characters $\chi: G \to \mathbb{C}$ of group representations, which are class functions constant on conjugacy classes. Characters completely determine representations over $\mathbb{C}$ for finite groups.

### 中文定义
特征标理论研究群表示的特征标$\chi: G \to \mathbb{C}$，特征标是在共轭类上恒定的类函数。对有限群，特征标完全决定$\mathbb{C}$上的表示。

### Notation
- $\chi_V(g) = \text{tr}(\rho_V(g))$: character of $V$
- $\langle \chi, \psi \rangle = \frac{1}{|G|}\sum_g \chi(g)\overline{\psi(g)}$: inner product
- Irreducible characters form orthonormal basis

### Example
- Character table of $S_3$
- Orthogonality relations: $\langle \chi_i, \chi_j \rangle = \delta_{ij}$
- Burnside's $p^aq^b$ theorem via characters

---

## 25. Irreducible Representation (不可约表示)

**MSC Code:** 20C20

### English Definition
A representation $V$ is irreducible if it has no proper non-zero invariant subspaces. For finite groups over $\mathbb{C}$, every representation decomposes uniquely (up to isomorphism) as direct sum of irreducibles.

### 中文定义
表示$V$是不可约的如果它没有非零真不变子空间。对于$\mathbb{C}$上的有限群，每个表示唯一地（同构意义下）分解为不可约表示的直和。

### Notation
- $\text{Irr}(G)$: set of irreducible representations
- $\hat{G}$: dual group (for abelian $G$)
- Maschke's theorem: complete reducibility

### Example
- 1-dim representations of abelian groups
- Standard representation of $S_n$: $(n-1)$-dimensional
- Spin representations of $SO(n)$

---

## 26. Lie Group (李群)

**MSC Code:** 22E15, @

### English Definition
A Lie group is a group that is also a smooth manifold, with group operations (multiplication and inversion) being smooth maps. They are the continuous symmetry groups of geometry and physics.

### 中文定义
李群是同时也是光滑流形的群，群运算（乘法和取逆）是光滑映射。它们是几何和物理中的连续对称群。

### Notation
- $GL(n, \mathbb{R})$, $SL(n, \mathbb{R})$: matrix Lie groups
- $O(n)$, $SO(n)$: orthogonal groups
- $U(n)$, $SU(n)$: unitary groups
- $\mathfrak{g} = T_eG$: Lie algebra

### Example
- $(\mathbb{R}^n, +)$: abelian Lie group
- $S^1 = U(1)$: circle group
- $SU(2) \cong S^3$ as manifolds

---

## 27. Lie Algebra (李代数)

**MSC Code:** @

### English Definition
A Lie algebra is a vector space $\mathfrak{g}$ with bilinear bracket $[,]: \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$ satisfying antisymmetry $[X,Y] = -[Y,X]$ and Jacobi identity $[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0$.

### 中文定义
李代数是向量空间$\mathfrak{g}$，带有双线性括号$[,]: \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$，满足反对称性$[X,Y] = -[Y,X]$和雅可比恒等式$[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0$。

### Notation
- $[X,Y]$: Lie bracket
- $\text{ad}_X(Y) = [X,Y]$: adjoint action
- Killing form: $\kappa(X,Y) = \text{tr}(\text{ad}_X \circ \text{ad}_Y)$

### Example
- $\mathfrak{gl}(n) = M_n(\mathbb{R})$ with $[A,B] = AB - BA$
- $\mathfrak{so}(n) = \{A : A^T = -A\}$
- $\mathfrak{sl}(n) = \{A : \text{tr}(A) = 0\}$

---

## 28. Root System (根系)

**MSC Code:** 17B20, 17B22

### English Definition
A root system in Euclidean space $E$ is a finite set $\Phi$ of non-zero vectors (roots) satisfying: (1) $\Phi$ spans $E$; (2) reflections $s_\alpha$ preserve $\Phi$; (3) $\frac{2(\beta,\alpha)}{(\alpha,\alpha)} \in \mathbb{Z}$; (4) $\pm \alpha$ are the only scalar multiples.

### 中文定义
欧氏空间$E$中的根系是有限非零向量集$\Phi$（根），满足：(1) $\Phi$张成$E$；(2) 反射$s_\alpha$保持$\Phi$；(3) $\frac{2(\beta,\alpha)}{(\alpha,\alpha)} \in \mathbb{Z}$；(4) $\pm \alpha$是仅有的标量倍数。

### Notation
- Simple roots $\Delta = \{\alpha_1, \ldots, \alpha_n\}$
- Weyl group $W = \langle s_\alpha : \alpha \in \Phi \rangle$
- Cartan matrix: $C_{ij} = \frac{2(\alpha_i, \alpha_j)}{(\alpha_j, \alpha_j)}$

### Example
- $A_n$ type: roots of $\mathfrak{sl}_{n+1}$
- $D_n$, $E_6$, $E_7$, $E_8$: simply-laced
- $B_n$, $C_n$, $F_4$, $G_2$: multiply-laced

---

## 29. Semisimple Lie Algebra (半单李代数)

**MSC Code:** 17B20

### English Definition
A Lie algebra is semisimple if its Killing form is non-degenerate, equivalently if it is a direct sum of simple Lie algebras (non-abelian with no proper ideals). Classification by Dynkin diagrams.

### 中文定义
李代数是半单的如果其基灵形式非退化，等价于它是单李代数的直和（非阿贝尔且无真理想）。由邓肯图分类。

### Notation
- $\mathfrak{g} = \mathfrak{g}_1 \oplus \cdots \oplus \mathfrak{g}_k$: decomposition
- Cartan subalgebra $\mathfrak{h}$
- Root space decomposition: $\mathfrak{g} = \mathfrak{h} \oplus \bigoplus_{\alpha \in \Phi} \mathfrak{g}_\alpha$

### Example
- $\mathfrak{sl}_n$ for $n \geq 2$
- $\mathfrak{so}_n$ for $n \geq 3$
- $\mathfrak{sp}_{2n}$ for $n \geq 1$
- Exceptional: $\mathfrak{g}_2$, $\mathfrak{f}_4$, $\mathfrak{e}_6$, $\mathfrak{e}_7$, $\mathfrak{e}_8$

---

## 30. Universal Enveloping Algebra (泛包络代数)

**MSC Code:** 17B35

### English Definition
The universal enveloping algebra $U(\mathfrak{g})$ of Lie algebra $\mathfrak{g}$ is the associative algebra generated by $\mathfrak{g}$ with relations $XY - YX = [X,Y]$. It satisfies the universal property for Lie algebra representations.

### 中文定义
李代数$\mathfrak{g}$的泛包络代数$U(\mathfrak{g})$是由$\mathfrak{g}$生成的结合代数，满足关系$XY - YX = [X,Y]$。它满足李代数表示的泛性质。

### Notation
- $U(\mathfrak{g}) = T(\mathfrak{g})/(X \otimes Y - Y \otimes X - [X,Y])$
- PBW theorem: $\text{gr}(U(\mathfrak{g})) \cong S(\mathfrak{g})$
- Center $Z(U(\mathfrak{g}))$: generated by Casimir operators

### Example
- $U(\mathfrak{sl}_2)$: generators $e, f, h$ with $[h,e]=2e$, $[h,f]=-2f$, $[e,f]=h$
- Verma modules: induced from Borel subalgebra
- Harish-Chandra isomorphism: $Z(U(\mathfrak{g})) \cong S(\mathfrak{h})^W$

---

## 31. Highest Weight Theory (最高权理论)

**MSC Code:** 17B10, 22E47

### English Definition
For semisimple $\mathfrak{g}$, finite-dimensional irreducible representations are classified by dominant integral highest weights $\lambda$. The representation $V(\lambda)$ has unique highest weight vector $v_\lambda$ with $\mathfrak{n}^+ v_\lambda = 0$ and $hv_\lambda = \lambda(h)v_\lambda$.

### 中文定义
对于半单$\mathfrak{g}$，有限维不可约表示由支配整最高权$\lambda$分类。表示$V(\lambda)$有唯一最高权向量$v_\lambda$，满足$\mathfrak{n}^+ v_\lambda = 0$和$hv_\lambda = \lambda(h)v_\lambda$。

### Notation
- $V(\lambda)$: irreducible with highest weight $\lambda$
- Weight space decomposition: $V = \bigoplus_\mu V_\mu$
- Weyl character formula: $\chi_\lambda = \frac{\sum_{w \in W} \epsilon(w) e^{w(\lambda+\rho)}}{\sum_{w \in W} \epsilon(w) e^{w\rho}}$

### Example
- $V(k\omega_1)$ of $\mathfrak{sl}_2$: $(k+1)$-dimensional
- Standard representation of $\mathfrak{sl}_n$: fundamental weight $\omega_1$
- Adjoint representation: highest root

---

## 32. Category O (O范畴)

**MSC Code:** 17B10, @

### English Definition
Category $\mathcal{O}$ is the category of finitely-generated $U(\mathfrak{g})$-modules that are semisimple under $\mathfrak{h}$-action with locally nilpotent $\mathfrak{n}^+$-action and finite-dimensional weight spaces. It contains Verma modules and their quotients.

### 中文定义
范畴$\mathcal{O}$是有限生成$U(\mathfrak{g})$-模范畴，在$\mathfrak{h}$作用下半单，$\mathfrak{n}^+$作用局部幂零，权空间有限维。它包含韦模及其商。

### Notation
- $M(\lambda) = U(\mathfrak{g}) \otimes_{U(\mathfrak{b})} \mathbb{C}_\lambda$: Verma module
- $L(\lambda)$: simple quotient of $M(\lambda)$
- Projective objects, blocks, translation functors

### Example
- Verma module $M(\lambda)$: universal highest weight module
- $L(\lambda) = M(\lambda)$ iff $\lambda$ is dominant
- Kazhdan-Lusztig conjecture: characters of simples

---

## 33. Homological Algebra (同调代数)

**MSC Code:** @

### English Definition
Homological algebra studies chain complexes, homology, and derived functors in abelian categories. It provides tools like Ext and Tor to measure module extensions and torsion.

### 中文定义
同调代数研究阿贝尔范畴中的链复形、同调和导出函子。它提供如Ext和Tor的工具来度量模的扩张和挠。

### Notation
- Chain complex: $\cdots \to C_{n+1} \xrightarrow{d_{n+1}} C_n \xrightarrow{d_n} C_{n-1} \to \cdots$
- $H_n(C) = \ker d_n / \text{im} d_{n+1}$: homology
- $\text{Ext}^n$, $\text{Tor}_n$: derived functors

### Example
- $\text{Ext}^1_R(A,B)$: equivalence classes of extensions
- Projective resolutions
- Group cohomology: $H^n(G, M) = \text{Ext}^n_{\mathbb{Z}[G]}(\mathbb{Z}, M)$

---

## 34. Derived Category (导出范畴)

**MSC Code:** 18G80, 14F05

### English Definition
The derived category $D(\mathcal{A})$ of an abelian category $\mathcal{A}$ is obtained from chain complexes by formally inverting quasi-isomorphisms. It provides a framework for derived functors.

### 中文定义
阿贝尔范畴$\mathcal{A}$的导出范畴$D(\mathcal{A})$由链复形通过形式地逆拟同构得到。它为导出函子提供框架。

### Notation
- $D(\mathcal{A})$, $D^+(\mathcal{A})$, $D^b(\mathcal{A})$: bounded versions
- $[n]$: shift functor
- Distinguished triangles: replace exact sequences

### Example
- $D^b(\text{Coh}(X))$: derived category of coherent sheaves
- Fourier-Mukai transforms: equivalences of derived categories
- $Rf_*$: derived pushforward

---

## 35. Spectral Sequence (谱序列)

**MSC Code:** 18G40, @

### English Definition
A spectral sequence is a sequence of bigraded complexes $(E_r, d_r)$ with $d_r^2 = 0$ and $E_{r+1} = H(E_r, d_r)$. It converges to a graded object associated to a filtration.

### 中文定义
谱序列是双分次复形序列$(E_r, d_r)$，满足$d_r^2 = 0$且$E_{r+1} = H(E_r, d_r)$。它收敛于与滤过相关的分次对象。

### Notation
- $E_2^{p,q} \Rightarrow H^{p+q}$: convergence
- Leray spectral sequence: for composition of functors
- Grothendieck spectral sequence

### Example
- Leray-Serre: for fibration $F \to E \to B$
- Grothendieck: $R^iF \circ R^jG \Rightarrow R^{i+j}(F \circ G)$
- Hodge-de Rham spectral sequence

---

## 36. Group Cohomology (群上同调)

**MSC Code:** 20J06, 18G60

### English Definition
Group cohomology $H^n(G, M)$ for $G$-module $M$ is the right derived functor of invariants $M \mapsto M^G = \{m : gm = m \text{ for all } g\}$. It can be computed via bar resolution.

### 中文定义
群上同调$H^n(G, M)$对于$G$-模$M$是不变子$M \mapsto M^G = \{m : gm = m \text{ for all } g\}$的右导出函子。它可通过条形分解计算。

### Notation
- $H^n(G, M) = \text{Ext}^n_{\mathbb{Z}[G]}(\mathbb{Z}, M)$
- $H^2(G, M)$: classifies group extensions
- Cup product: $H^p \times H^q \to H^{p+q}$

### Example
- $H^1(G, M) = \text{Der}(G, M)/\text{InnDer}(G, M)$
- $H^2(G, \mathbb{C}^\times)$: Schur multiplier
- Tate cohomology for finite groups

---

## 37. Galois Cohomology (伽罗瓦上同调)

**MSC Code:** 11S25, @

### English Definition
Galois cohomology $H^n(G_K, M)$ for Galois group $G_K = \text{Gal}(\overline{K}/K)$ and discrete $G_K$-module $M$ generalizes classical constructions like Hilbert's Theorem 90 and class field theory.

### 中文定义
伽罗瓦上同调$H^n(G_K, M)$对于伽罗瓦群$G_K = \text{Gal}(\overline{K}/K)$和离散$G_K$-模$M$，推广了如希尔伯特定理90和类域论的经典构造。

### Notation
- $H^1(G_K, GL_n(\overline{K})) = 1$ (Hilbert 90)
- $H^1(G_K, E(\overline{K}))$: Selmer group, Tate-Shafarevich group
- Inflation-restriction exact sequence

### Example
- Hilbert's Theorem 90: $H^1(G_K, \overline{K}^\times) = 0$
- Brauer group: $\text{Br}(K) = H^2(G_K, \overline{K}^\times)$
- Local duality: Tate's local duality theorem

---

## 38. Brauer Group (布饶尔群)

**MSC Code:** 16K50, 12G05

### English Definition
The Brauer group $\text{Br}(K)$ of a field $K$ classifies central simple algebras over $K$ up to Morita equivalence. Equivalently, $\text{Br}(K) = H^2(G_K, \overline{K}^\times)$.

### 中文定义
域$K$的布饶尔群$\text{Br}(K)$分类中心单代数在$K$上的森田等价类。等价地，$\text{Br}(K) = H^2(G_K, \overline{K}^\times)$。

### Notation
- $[A] \in \text{Br}(K)$ for central simple algebra $A$
- $\text{Br}(K)[n]$: $n$-torsion elements
- Cyclic algebras: $(a, b)_\omega$

### Example
- $\text{Br}(\mathbb{C}) = 0$
- $\text{Br}(\mathbb{R}) = \mathbb{Z}/2\mathbb{Z}$ (Hamiltonians)
- $\text{Br}(\mathbb{Q}_p) = \mathbb{Q}/\mathbb{Z}$

---

## 39. Quadratic Form (二次型)

**MSC Code:** 11E04, 11E39

### English Definition
A quadratic form over field $K$ is a homogeneous degree-2 polynomial $q(x_1, \ldots, x_n) = \sum_{i \leq j} a_{ij} x_i x_j$. It corresponds to a symmetric bilinear form when $\text{char}(K) \neq 2$.

### 中文定义
域$K$上的二次型是二次齐次多项式$q(x_1, \ldots, x_n) = \sum_{i \leq j} a_{ij} x_i x_j$。当$\text{char}(K) \neq 2$时，它对应于对称双线性形式。

### Notation
- Witt ring $W(K)$: ring of quadratic forms
- Discriminant, Hasse invariant
- $q \cong \langle a_1, \ldots, a_n \rangle$: diagonal form

### Example
- Sum of squares: $\langle 1, 1, \ldots, 1 \rangle$
- Isotropic: $q(v) = 0$ for $v \neq 0$
- $x^2 + y^2 + z^2$ over $\mathbb{Q}$: anisotropic

---

## 40. Quaternions (四元数)

**MSC Code:** 11R52, 16H05

### English Definition
The quaternion algebra $\left(\frac{a,b}{K}\right)$ over field $K$ is the 4-dimensional algebra $K \oplus Ki \oplus Kj \oplus Kk$ with $i^2 = a$, $j^2 = b$, $ij = -ji = k$. Hamilton's quaternions $\mathbb{H} = \left(\frac{-1,-1}{\mathbb{R}}\right)$.

### 中文定义
域$K$上的四元数代数$\left(\frac{a,b}{K}\right)$是4维代数$K \oplus Ki \oplus Kj \oplus Kk$，满足$i^2 = a$，$j^2 = b$，$ij = -ji = k$。哈密顿四元数$\mathbb{H} = \left(\frac{-1,-1}{\mathbb{R}}\right)$。

### Notation
- $i, j, k$: quaternion units
- Conjugation: $\overline{q} = a - bi - cj - dk$
- Norm: $N(q) = q\overline{q}$

### Example
- $\mathbb{H}$: non-commutative division algebra
- $(2,3)_\mathbb{Q}$: quaternion algebra ramified at $\{2,3,\infty\}$
- Every central simple algebra over $\mathbb{R}$ is $\mathbb{R}$ or $\mathbb{H}$

---

## 41. Algebraic K-Theory (代数K理论)

**MSC Code:** @, @

### English Definition
Algebraic K-theory assigns to a ring $R$ groups $K_n(R)$ generalizing linear algebra constructions. $K_0$ classifies projective modules, $K_1$ involves invertible matrices, and higher $K$-groups are defined via Quillen's plus construction or Waldhausen's S-construction.

### 中文定义
代数K理论给环$R$赋予群$K_n(R)$，推广线性代数构造。$K_0$分类投射模，$K_1$涉及可逆矩阵，高阶K群由奎伦加构造或瓦尔德豪森S构造定义。

### Notation
- $K_0(R)$: Grothendieck group of projective modules
- $K_1(R) = GL(R)^{ab}$
- $K_2(R)$: Steinberg group relations
- Milnor K-theory: $K_n^M(F)$

### Example
- $K_0(\mathbb{Z}) = \mathbb{Z}$, $K_1(\mathbb{Z}) = \{\pm 1\}$
- $K_0(\mathbb{C}) = \mathbb{Z}$, $K_1(\mathbb{C}) = \mathbb{C}^\times$
- Quillen's computation: $K_i(\mathbb{F}_q)$ is finite cyclic

---

## 42. Motive ( motive/动机)

**MSC Code:** 14C15, 14F42

### English Definition
Grothendieck's theory of motives aims to unify cohomology theories for algebraic varieties. A motive is a "piece" of a variety cut out by correspondences, expected to be the heart of a tannakian category of mixed motives.

### 中文定义
格罗滕迪克的动机理论旨在统一代数簇的上同调理论。动机是代数簇被对应"切割"出的"碎片"，预期是混合动机的淡中范畴的核心。

### Notation
- Chow motives, Grothendieck motives
- $h(X)$: motive of variety $X$
- Lefschetz motive $\mathbb{L}$
- Tannakian category of motives

### Example
- $h(\mathbb{P}^1) = \mathbf{1} \oplus \mathbb{L}$
- Tate motive $\mathbb{Q}(1)$
- Standard conjectures: relate motives to cohomology

---

## 43. Étale Cohomology (平展上同调)

**MSC Code:** 14F20, @

### English Definition
Étale cohomology $H^n_{\acute{e}t}(X, \mathcal{F})$ is a Weil cohomology theory for algebraic varieties in any characteristic, defined using étale topology. It was key to proving the Weil conjectures.

### 中文定义
平展上同调$H^n_{\acute{e}t}(X, \mathcal{F})$是任何特征下代数簇的韦伊上同调理论，使用平展拓扑定义。它是证明韦伊猜想的关键。

### Notation
- $H^i_{\acute{e}t}(X, \mathbb{Q}_\ell)$: $\ell$-adic cohomology
- Poincaré duality, Lefschetz fixed-point formula
- Comparison theorem: $H^i_{\acute{e}t}(X, \mathbb{Q}_\ell) \cong H^i(X(\mathbb{C}), \mathbb{Q}) \otimes \mathbb{Q}_\ell$

### Example
- $H^1_{\acute{e}t}(E, \mathbb{Q}_\ell) = T_\ell(E) \otimes \mathbb{Q}$
- Weil conjectures via étale cohomology
- Artin comparison theorem

---

## 44. Weil Conjectures (韦伊猜想)

**MSC Code:** 14F20, 11G25

### English Definition
The Weil conjectures (proved by Deligne) concern the zeta function $Z(X, t)$ of variety $X$ over $\mathbb{F}_q$: rationality, functional equation, Riemann hypothesis analog ($|\alpha_i| = q^{j/2}$), and Betti number interpretation.

### 中文定义
韦伊猜想（由德利涅证明）涉及$\mathbb{F}_q$上簇$X$的zeta函数$Z(X, t)$：有理性、函数方程、黎曼假设类比（$|\alpha_i| = q^{j/2}$）和贝蒂数解释。

### Notation
- $Z(X, t) = \exp\left(\sum_{m=1}^\infty \frac{N_m}{m}t^m\right)$: zeta function
- $N_m = |X(\mathbb{F}_{q^m})|$
- $Z(X, t) = \frac{P_1(t)P_3(t)\cdots}{P_0(t)P_2(t)\cdots}$

### Example
- $Z(\mathbb{P}^n, t) = \frac{1}{(1-t)(1-qt)\cdots(1-q^nt)}$
- Elliptic curve: $Z(E, t) = \frac{1 - at + qt^2}{(1-t)(1-qt)}$
- RH analog: roots of $P_j$ have $|t| = q^{-j/2}$

---

## 45. Perfectoid Space (完美胚空间)

**MSC Code:** 14G22, @

### English Definition
Perfectoid spaces, introduced by Scholze, are a class of non-archimedean analytic spaces that tilt to characteristic $p$. They have revolutionized $p$-adic Hodge theory and the Langlands program.

### 中文定义
完美胚空间（由舒尔茨引入）是一类非阿基米德解析空间，倾斜到特征$p$。它们彻底改变了$p$进霍奇理论和朗兰兹纲领。

### Notation
- Tilting: $X \mapsto X^\flat$ (characteristic $p$)
- Untilting: going back to mixed characteristic
- Diamond: quotient of perfectoid space by pro-étale equivalence

### Example
- $\mathbb{Q}_p(p^{1/p^\infty})^{\wedge}$: perfectoid field
- Lubin-Tate space: infinite level is perfectoid
- Fargues-Fontaine curve

---

## 46. Langlands Program (朗兰兹纲领)

**MSC Code:** @, @

### English Definition
The Langlands program is a vast web of conjectures relating number theory, representation theory, and algebraic geometry. It predicts deep correspondences between automorphic representations and Galois representations.

### 中文定义
朗兰兹纲领是联系数论、表示论和代数几何的广阔猜想网。它预测自守表示与伽罗瓦表示之间的深刻对应。

### Notation
- Automorphic representation $\pi$ of $G(\mathbb{A})$
- $L$-function $L(s, \pi) = L(s, \rho)$
- Functoriality: liftings between groups

### Example
- $GL(1)$: abelian class field theory
- $GL(2)$: modular forms and elliptic curves
- Fundamental lemma (Ngô)

---

## 47. Automorphic Form (自守形式)

**MSC Code:** @, 22E50

### English Definition
An automorphic form on reductive group $G$ over number field $F$ is a function on $G(\mathbb{A}_F)$ satisfying transformation properties under $G(F)$, growth conditions, and differential equations (eigenfunction of Casimir).

### 中文定义
数域$F$上约化群$G$的自守形式是$G(\mathbb{A}_F)$上的函数，满足在$G(F)$下的变换性质、增长条件和微分方程（卡西米尔特征函数）。

### Notation
- $\mathcal{A}(G(F) \backslash G(\mathbb{A}))$: space of automorphic forms
- Cusp form: vanishing at infinity
- $L^2(G(F) \backslash G(\mathbb{A})^1)$: automorphic representation

### Example
- Modular forms: automorphic forms on $GL(2)$
- Siegel modular forms: on $Sp(2n)$
- Maass forms: non-holomorphic automorphic forms

---

## 48. Iwasawa Theory (岩泽理论)

**MSC Code:** 11R23

### English Definition
Iwasawa theory studies the behavior of arithmetic objects (class groups, Selmer groups) in $\mathbb{Z}_p$-extensions. Main conjectures relate $p$-adic $L$-functions to characteristic ideals of Galois modules.

### 中文定义
岩泽理论研究算术对象（类群、塞尔默群）在$\mathbb{Z}_p$-扩张中的行为。主猜想联系$p$进L函数与伽罗瓦模的特征理想。

### Notation
- $\mathbb{Z}_p$-extension: Galois group $\cong \mathbb{Z}_p$
- Cyclotomic $\mathbb{Z}_p$-extension: $\mathbb{Q}(\mu_{p^\infty})^+$
- Iwasawa algebra $\Lambda = \mathbb{Z}_p[[\Gamma]] \cong \mathbb{Z}_p[[T]]$

### Example
- $\mu$-invariant, $\lambda$-invariant of $p$-adic $L$-functions
- Main conjecture: $\text{char}(X) = (L_p)$
- Ferrero-Washington: $\mu = 0$ for cyclotomic $\mathbb{Z}_p$-extension

---

## 49. Shimura Variety (志村簇)

**MSC Code:** 11G18, 14G35

### English Definition
Shimura varieties are a class of moduli spaces with canonical models over number fields. They generalize modular curves and play a central role in the Langlands program and arithmetic geometry.

### 中文定义
志村簇是一类模空间，在数域上有典范模型。它们推广模曲线，在朗兰兹纲领和算术几何中起核心作用。

### Notation
- $(G, X)$: Shimura datum
- $Sh_K(G, X) = G(\mathbb{Q}) \backslash X \times G(\mathbb{A}_f) / K$
- Canonical model over reflex field

### Example
- Modular curves: $Sh(GL_2, \mathbb{H}^\pm)$
- Siegel modular varieties: $Sh(GSp_{2n}, \mathbb{H}_n)$
- CM points: special points with complex multiplication

---

## 50. Complex Multiplication (复乘法)

**MSC Code:** 11G15

### English Definition
An elliptic curve (or abelian variety) has complex multiplication if its endomorphism ring is larger than $\mathbb{Z}$. CM theory relates these curves to class field theory of imaginary quadratic fields.

### 中文定义
椭圆曲线（或阿贝尔簇）有复乘法如果其自同态环大于$\mathbb{Z}$。CM理论将这些曲线与虚二次域的类域论联系起来。

### Notation
- CM by $\mathcal{O}_K$: $\text{End}(E) \cong \mathcal{O}_K$ for imaginary quadratic $K$
- CM abelian variety: with CM by CM field
- Main theorem of CM: generating class fields

### Example
- $E: y^2 = x^3 - x$ has CM by $\mathbb{Z}[i]$
- $j$-invariants of CM curves are algebraic integers
- Weber functions: constructing ray class fields

---

*End of Number Theory and Advanced Algebra Concepts*
