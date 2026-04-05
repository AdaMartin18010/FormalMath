# Advanced Geometry and Topology (高级几何拓扑)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 50 core concepts in advanced geometry and topology.

---

## 1. Differentiable Manifold (微分流形)

**MSC Code:** 57Rxx, 58A05

### English Definition
A differentiable manifold $M$ of dimension $n$ is a topological manifold equipped with a smooth atlas: a collection of charts $(U_\alpha, \varphi_\alpha)$ where $\varphi_\alpha: U_\alpha \to \mathbb{R}^n$ are homeomorphisms to open subsets of $\mathbb{R}^n$, and transition maps $\varphi_\beta \circ \varphi_\alpha^{-1}$ are smooth ($C^\infty$).

### 中文定义
$n$维微分流形$M$是一个配有光滑图册的拓扑流形：图册由坐标卡$(U_\alpha, \varphi_\alpha)$组成，其中$\varphi_\alpha: U_\alpha \to \mathbb{R}^n$是同胚映射到$\mathbb{R}^n$的开子集，且转移映射$\varphi_\beta \circ \varphi_\alpha^{-1}$是光滑的（$C^\infty$）。

### Notation
- $(M, \mathcal{A})$: manifold with atlas $\mathcal{A}$
- $C^\infty(M)$: ring of smooth functions on $M$
- $T_pM$: tangent space at $p$

### Example
- $\mathbb{R}^n$ with the standard smooth structure
- $S^n \subset \mathbb{R}^{n+1}$: unit sphere with induced smooth structure
- $\mathbb{RP}^n$: real projective space

---

## 2. Tangent Bundle (切丛)

**MSC Code:** 57R25, 58A05

### English Definition
The tangent bundle $TM$ of a smooth manifold $M$ is the disjoint union of all tangent spaces $TM = \bigsqcup_{p \in M} T_pM$, equipped with a natural smooth manifold structure of dimension $2n$.

### 中文定义
光滑流形$M$的切丛$TM$是所有切空间的不交并$TM = \bigsqcup_{p \in M} T_pM$，配备自然的$2n$维光滑流形结构。

### Notation
- $\pi: TM \to M$: projection map $\pi(v) = p$ for $v \in T_pM$
- $(x^i, v^i)$: local coordinates on $TM$
- $\Gamma(TM) = \mathfrak{X}(M)$: space of vector fields

### Example
- $T\mathbb{R}^n = \mathbb{R}^n \times \mathbb{R}^n$
- $TS^1 \cong S^1 \times \mathbb{R}$ (trivial bundle)
- $TS^2$ is non-trivial (hairy ball theorem)

---

## 3. Cotangent Bundle (余切丛)

**MSC Code:** 58A10

### English Definition
The cotangent bundle $T^*M$ is the disjoint union of all cotangent spaces $T^*_pM = (T_pM)^*$, dual to tangent spaces. It has a canonical symplectic structure.

### 中文定义
余切丛$T^*M$是所有余切空间$T^*_pM = (T_pM)^*$的不交并，是切空间的对偶。它具有典范的辛结构。

### Notation
- $\omega = \sum dp_i \wedge dq^i$: canonical symplectic form
- $T^*M$: cotangent bundle (phase space in mechanics)
- $\Omega^1(M) = \Gamma(T^*M)$: space of 1-forms

### Example
- $T^*\mathbb{R}^n = \mathbb{R}^n \times (\mathbb{R}^n)^*$
- $T^*S^1 \cong S^1 \times \mathbb{R}$
- Phase space in Hamiltonian mechanics: $T^*Q$

---

## 4. Vector Bundle (向量丛)

**MSC Code:** 55R25, 57R22

### English Definition
A vector bundle $E$ over a manifold $M$ consists of a total space $E$, projection $\pi: E \to M$, and fibers $E_p = \pi^{-1}(p)$ that are vector spaces, locally trivial: each point has a neighborhood $U$ with $\pi^{-1}(U) \cong U \times \mathbb{R}^k$.

### 中文定义
流形$M$上的向量丛$E$由全空间$E$、投影$\pi: E \to M$和纤维$E_p = \pi^{-1}(p)$（向量空间）组成，局部平凡：每点有邻域$U$使得$\pi^{-1}(U) \cong U \times \mathbb{R}^k$。

### Notation
- $E \xrightarrow{\pi} M$: vector bundle over $M$
- $\Gamma(E)$: space of sections
- $\text{rank}(E)$: dimension of fibers

### Example
- Tangent bundle $TM$
- Cotangent bundle $T^*M$
- Möbius bundle over $S^1$ (non-trivial line bundle)

---

## 5. Fiber Bundle (纤维丛)

**MSC Code:** 55R10, 57R22

### English Definition
A fiber bundle $(E, \pi, M, F)$ consists of total space $E$, base $M$, projection $\pi: E \to M$, and fiber $F$, such that $\pi$ is locally trivial: for each $p \in M$, there exists $U \ni p$ with $\pi^{-1}(U) \cong U \times F$.

### 中文定义
纤维丛$(E, \pi, M, F)$由全空间$E$、底空间$M$、投影$\pi: E \to M$和纤维$F$组成，使得$\pi$局部平凡：对每点$p \in M$，存在$U \ni p$使得$\pi^{-1}(U) \cong U \times F$。

### Notation
- $F \hookrightarrow E \xrightarrow{\pi} M$: fiber bundle
- Structure group $G$: acts on fiber $F$
- Transition functions $g_{\alpha\beta}: U_\alpha \cap U_\beta \to G$

### Example
- Vector bundles (fibers are vector spaces)
- Principal bundles (fibers are Lie groups)
- Hopf fibration: $S^1 \hookrightarrow S^3 \to S^2$

---

## 6. Principal Bundle (主丛)

**MSC Code:** 55R10, 57Sxx

### English Definition
A principal $G$-bundle $P \xrightarrow{\pi} M$ is a fiber bundle with fiber $G$ (Lie group) and free right $G$-action preserving fibers, such that $P/G \cong M$.

### 中文定义
主$G$-丛$P \xrightarrow{\pi} M$是以李群$G$为纤维的纤维丛，配有保持纤维的自由右$G$-作用，使得$P/G \cong M$。

### Notation
- $P \times G \to P$: right action $(p, g) \mapsto p \cdot g$
- $P/G \cong M$: quotient by action gives base
- Connection form $\omega \in \Omega^1(P, \mathfrak{g})$

### Example
- Frame bundle $F(M)$: principal $GL(n)$-bundle
- Hopf fibration: principal $U(1)$-bundle over $S^2$
- Universal bundle $EG \to BG$

---

## 7. Characteristic Class (示性类)

**MSC Code:** 57R20, 55R40

### English Definition
Characteristic classes are cohomology classes associated to vector bundles that measure their twisting. They are natural with respect to pullbacks and classify bundles up to certain equivalences.

### 中文定义
示性类是与向量丛相关联的上同调类，用于度量丛的扭曲。它们关于拉回是自然的，并在特定等价意义下分类丛。

### Notation
- $c_k(E) \in H^{2k}(M; \mathbb{Z})$: Chern classes (complex)
- $p_k(E) \in H^{4k}(M; \mathbb{Z})$: Pontryagin classes
- $e(E) \in H^n(M; \mathbb{Z})$: Euler class
- $w_k(E) \in H^k(M; \mathbb{Z}_2)$: Stiefel-Whitney classes

### Example
- $c_1(L)$ for line bundle $L$: first Chern class
- $e(TM)$ for oriented $M$: Euler class
- $w_1$ detects orientability; $w_2$ for spin structures

---

## 8. Chern Class (陈类)

**MSC Code:** 57R20, 14F45

### English Definition
Chern classes $c_k(E) \in H^{2k}(M; \mathbb{Z})$ are characteristic classes for complex vector bundles. The total Chern class is $c(E) = 1 + c_1(E) + c_2(E) + \cdots$ with Whitney sum formula $c(E \oplus F) = c(E) \smile c(F)$.

### 中文定义
陈类$c_k(E) \in H^{2k}(M; \mathbb{Z})$是复向量丛的示性类。全陈类为$c(E) = 1 + c_1(E) + c_2(E) + \cdots$，满足惠特尼和公式$c(E \oplus F) = c(E) \smile c(F)$。

### Notation
- $c(E) = \det(I + \frac{i}{2\pi}\Omega)$: curvature formula
- $c_1(L) = [\frac{i}{2\pi}\Theta]$ for line bundle with curvature $\Theta$
- $\int_M c_n(E)$: top Chern number

### Example
- $c_1(T\mathbb{CP}^1) = 2[\omega_{FS}]$ where $\omega_{FS}$ is Fubini-Study form
- $c(TP^n) = (1+H)^{n+1}$ where $H$ is hyperplane class
- For complex line bundle: $c_1$ classifies up to isomorphism

---

## 9. Stiefel-Whitney Class (施蒂费尔-惠特尼类)

**MSC Code:** 57R20, 55R40

### English Definition
Stiefel-Whitney classes $w_k(E) \in H^k(M; \mathbb{Z}_2)$ are $\mathbb{Z}_2$-characteristic classes for real vector bundles. They provide obstructions to sections: $w_k(E) = 0$ iff $E$ has $n-k+1$ linearly independent sections over the $k$-skeleton.

### 中文定义
施蒂费尔-惠特尼类$w_k(E) \in H^k(M; \mathbb{Z}_2)$是实向量丛的$\mathbb{Z}_2$-示性类。它们给出截面的障碍：$w_k(E) = 0$当且仅当$E$在$k$-骨架上有$n-k+1$个线性无关截面。

### Notation
- $w(E) = 1 + w_1(E) + w_2(E) + \cdots$: total Stiefel-Whitney class
- $w_1(E)$: obstruction to orientability
- $w_2(E)$: obstruction to spin structure

### Example
- $w_1(TM) = 0 \iff M$ is orientable
- $w_2(TM) = 0 \iff M$ admits spin structure
- $w(\gamma^1) = 1 + a$ for tautological line bundle over $\mathbb{RP}^n$

---

## 10. Pontryagin Class (庞特里亚金类)

**MSC Code:** 57R20

### English Definition
Pontryagin classes $p_k(E) \in H^{4k}(M; \mathbb{Z})$ are characteristic classes for real vector bundles defined via complexification: $p_k(E) = (-1)^k c_{2k}(E \otimes \mathbb{C})$. They vanish in dimensions $4k+2$.

### 中文定义
庞特里亚金类$p_k(E) \in H^{4k}(M; \mathbb{Z})$是实向量丛的示性类，通过复化定义：$p_k(E) = (-1)^k c_{2k}(E \otimes \mathbb{C})$。它们在$4k+2$维消失。

### Notation
- $p(E) = 1 + p_1(E) + p_2(E) + \cdots$: total Pontryagin class
- $p_k(TM)$: Pontryagin classes of tangent bundle
- $\hat{A}$-genus: combination of Pontryagin classes

### Example
- $p_1(TS^4) = 0$ (sphere has no Pontryagin classes)
- $p_1(\mathbb{CP}^2) = 3H^2$ where $H$ is generator of $H^2$
- Signature theorem: $\sigma(M) = \frac{1}{45}(7p_2 - p_1^2)[M]$ for 4-manifolds

---

## 11. Homotopy Group (同伦群)

**MSC Code:** 55Qxx, 55Pxx

### English Definition
The $n$-th homotopy group $\pi_n(X, x_0)$ consists of homotopy classes of maps $f: (S^n, s_0) \to (X, x_0)$. For $n \geq 2$, $\pi_n$ is abelian. These groups classify maps from spheres up to homotopy.

### 中文定义
$n$维同伦群$\pi_n(X, x_0)$由映射$f: (S^n, s_0) \to (X, x_0)$的同伦类组成。对于$n \geq 2$，$\pi_n$是阿贝尔群。这些群在同伦意义下分类从球面到$X$的映射。

### Notation
- $\pi_n(X)$: $n$-th homotopy group
- $\pi_1(X)$: fundamental group
- Whitehead product: $[,]: \pi_m \times \pi_n \to \pi_{m+n-1}$

### Example
- $\pi_n(S^n) = \mathbb{Z}$ for all $n \geq 1$
- $\pi_3(S^2) = \mathbb{Z}$ (Hopf fibration)
- $\pi_4(S^3) = \mathbb{Z}_2$

---

## 12. Higher Homotopy Groups (高阶同伦群)

**MSC Code:** 55Qxx

### English Definition
Higher homotopy groups $\pi_n(X)$ for $n \geq 2$ are always abelian. They measure higher-dimensional holes in a space and are notoriously difficult to compute even for simple spaces like spheres.

### 中文定义
高阶同伦群$\pi_n(X)$（$n \geq 2$）总是阿贝尔群。它们度量空间的高维"洞"，即使对于球面这样简单的空间，计算也非常困难。

### Notation
- $\pi_n^S = \pi_{n+k}(S^k)$ for $k \geq n+2$: stable homotopy groups
- Suspension isomorphism: $\pi_n(X) \cong \pi_{n+1}(\Sigma X)$ (stable range)
- Hurewicz map: $\pi_n(X) \to H_n(X)$

### Example
- $\pi_n(S^k) = 0$ for $n < k$
- $\pi_{n+1}(S^n) = \mathbb{Z}_2$ for $n \geq 3$
- $\pi_{4n-1}(S^{2n})$ contains a $\mathbb{Z}$ summand

---

## 13. Homology Group (同调群)

**MSC Code:** 55Nxx, 55Uxx

### English Definition
Homology groups $H_n(X; R)$ are algebraic invariants of a topological space defined via chain complexes. They count $n$-dimensional holes and satisfy the Eilenberg-Steenrod axioms.

### 中文定义
同调群$H_n(X; R)$是通过链复形定义的拓扑空间的代数不变量。它们计数$n$维"洞"并满足艾伦伯格-斯廷罗德公理。

### Notation
- $H_n(X; G)$: singular homology with coefficients in $G$
- $\tilde{H}_n(X)$: reduced homology
- $\partial_n: C_n \to C_{n-1}$: boundary operator

### Example
- $H_k(S^n) = \mathbb{Z}$ for $k = 0, n$ and 0 otherwise
- $H_k(T^n) = \mathbb{Z}^{\binom{n}{k}}$ (homology of torus)
- $H_k(\mathbb{RP}^n; \mathbb{Z}_2) = \mathbb{Z}_2$ for $0 \leq k \leq n$

---

## 14. Singular Homology (奇异同调)

**MSC Code:** 55N10

### English Definition
Singular homology $H_n(X)$ is defined using singular simplices: continuous maps $\sigma: \Delta^n \to X$ from the standard $n$-simplex. The singular chain complex has boundary maps $\partial: C_n(X) \to C_{n-1}(X)$.

### 中文定义
奇异同调$H_n(X)$使用奇异单形定义：从标准$n$-单形$\Delta^n$到$X$的连续映射$\sigma: \Delta^n \to X$。奇异链复形具有边界映射$\partial: C_n(X) \to C_{n-1}(X)$。

### Notation
- $\Delta^n = \{(t_0, \ldots, t_n) : t_i \geq 0, \sum t_i = 1\}$: standard simplex
- $\sigma: \Delta^n \to X$: singular $n$-simplex
- $C_n(X) = \mathbb{Z}\langle \text{singular } n\text{-simplices} \rangle$

### Example
- $H_0(X) = \mathbb{Z}^{\text{(path components)}}$
- For contractible $X$: $H_n(X) = 0$ for $n > 0$
- $H_n(X \times Y) \neq H_n(X) \times H_n(Y)$ in general

---

## 15. Cellular Homology (胞腔同调)

**MSC Code:** 55N10, 55U15

### English Definition
Cellular homology is defined for CW complexes using the cell structure. The cellular chain complex has $C_n^{CW}(X) = H_n(X^n, X^{n-1}) \cong \mathbb{Z}^{\text{(}n\text{-cells)}}$, with boundary maps from the cellular boundary formula.

### 中文定义
胞腔同调对CW复形使用胞腔结构定义。胞腔链复形有$C_n^{CW}(X) = H_n(X^n, X^{n-1}) \cong \mathbb{Z}^{\text{(}n\text{维胞腔数)}}$，边界映射由胞腔边界公式给出。

### Notation
- $X^n$: $n$-skeleton
- $d_n: C_n^{CW} \to C_{n-1}^{CW}$: cellular boundary map
- $H_n^{CW}(X) \cong H_n(X)$: isomorphism with singular homology

### Example
- $H_k(S^n) = \mathbb{Z}$ for $k = 0, n$: one 0-cell, one $n$-cell
- $H_k(\mathbb{CP}^n) = \mathbb{Z}$ for even $k \leq 2n$: one cell in each even dimension
- $H_k(T^2)$: one 0-cell, two 1-cells, one 2-cell

---

## 16. Cohomology (上同调)

**MSC Code:** 55Nxx, 55Uxx

### English Definition
Cohomology $H^n(X; R)$ is the dual theory to homology, defined as the cohomology of the cochain complex $C^n(X) = \text{Hom}(C_n(X), R)$. It has a natural ring structure via cup product.

### 中文定义
上同调$H^n(X; R)$是同调的对偶理论，定义为上链复形$C^n(X) = \text{Hom}(C_n(X), R)$的上同调。它通过上积具有自然的环结构。

### Notation
- $\delta: C^n \to C^{n+1}$: coboundary operator, $\delta(f) = f \circ \partial$
- $\smile: H^p \times H^q \to H^{p+q}$: cup product
- $H^*(X) = \bigoplus_n H^n(X)$: cohomology ring

### Example
- $H^*(S^n) = \mathbb{Z}[x]/(x^2)$ where $|x| = n$
- $H^*(T^n) = \Lambda^*(\mathbb{Z}^n)$: exterior algebra
- $H^*(\mathbb{CP}^n) = \mathbb{Z}[h]/(h^{n+1})$ where $h$ has degree 2

---

## 17. Cup Product (上积)

**MSC Code:** 55N45

### English Definition
The cup product $\smile: H^p(X) \times H^q(X) \to H^{p+q}(X)$ gives cohomology a graded ring structure. It is defined on cochains by $(\alpha \smile \beta)(\sigma) = \alpha(\sigma|_{[v_0, \ldots, v_p]}) \cdot \beta(\sigma|_{[v_p, \ldots, v_{p+q}]})$.

### 中文定义
上积$\smile: H^p(X) \times H^q(X) \to H^{p+q}(X)$赋予上同调一个分次环结构。它在上链上定义为$(\alpha \smile \beta)(\sigma) = \alpha(\sigma|_{[v_0, \ldots, v_p]}) \cdot \beta(\sigma|_{[v_p, \ldots, v_{p+q}]})$。

### Notation
- $\alpha \smile \beta$: cup product
- Graded commutativity: $\alpha \smile \beta = (-1)^{pq} \beta \smile \alpha$
- $H^*(X)$: cohomology ring

### Example
- $H^*(T^2) = \Lambda(a, b)$ with $|a| = |b| = 1$
- $H^*(\mathbb{CP}^n) = \mathbb{Z}[h]/(h^{n+1})$: generated by degree-2 class
- Cup product on $S^2 \vee S^4$: trivial in middle degree

---

## 18. de Rham Cohomology (德拉姆上同调)

**MSC Code:** 58A12, 55Nxx

### English Definition
For a smooth manifold $M$, de Rham cohomology $H_{dR}^k(M)$ is defined using differential forms: $H_{dR}^k(M) = \ker(d: \Omega^k \to \Omega^{k+1}) / \text{im}(d: \Omega^{k-1} \to \Omega^k)$. By de Rham's theorem, $H_{dR}^k(M) \cong H^k(M; \mathbb{R})$.

### 中文定义
对于光滑流形$M$，德拉姆上同调$H_{dR}^k(M)$使用微分形式定义：$H_{dR}^k(M) = \ker(d: \Omega^k \to \Omega^{k+1}) / \text{im}(d: \Omega^{k-1} \to \Omega^k)$。由德拉姆定理，$H_{dR}^k(M) \cong H^k(M; \mathbb{R})$。

### Notation
- $\Omega^k(M)$: space of $k$-forms
- $Z^k(M) = \ker(d)$: closed forms
- $B^k(M) = \text{im}(d)$: exact forms
- $H_{dR}^k(M) = Z^k(M)/B^k(M)$

### Example
- $H_{dR}^0(M) = \mathbb{R}^{\text{(components)}}$
- $H_{dR}^1(S^1) = \mathbb{R}$: generated by $d\theta$
- $H_{dR}^2(S^2) = \mathbb{R}$: generated by volume form

---

## 19. Čech Cohomology (切赫上同调)

**MSC Code:** 55N30

### English Definition
Čech cohomology $\check{H}^n(X; \mathcal{F})$ is defined using open covers and nerves. For sheaves, it computes sheaf cohomology under suitable conditions. It is particularly useful for complex manifolds and algebraic geometry.

### 中文定义
切赫上同调$\check{H}^n(X; \mathcal{F})$使用开覆盖和网定义。对于层，在适当条件下计算层上同调。它对复流形和代数几何特别有用。

### Notation
- $\check{H}^n(X; \mathcal{F})$: Čech cohomology with coefficients in sheaf $\mathcal{F}$
- $\check{C}^n(\mathcal{U}, \mathcal{F})$: Čech cochains
- $\delta: \check{C}^n \to \check{C}^{n+1}$: Čech coboundary

### Example
- $\check{H}^1(X; \mathcal{O}^*) = \text{Pic}(X)$: Picard group (line bundles)
- For good covers: $\check{H}^n(X; G) \cong H^n(X; G)$
- $\check{H}^2(X; \mathbb{Z})$ classifies complex line bundles

---

## 20. Sheaf Cohomology (层上同调)

**MSC Code:** 14F05, 55N30

### English Definition
Sheaf cohomology $H^i(X, \mathcal{F})$ measures the failure of the global section functor $\Gamma(X, -)$ to be exact. It is the derived functor of $\Gamma$ and provides obstructions to extending local sections globally.

### 中文定义
层上同调$H^i(X, \mathcal{F})$度量整体截面函子$\Gamma(X, -)$正合性的失败。它是$\Gamma$的导出函子，给出将局部截面整体延拓的障碍。

### Notation
- $\mathcal{F}$: sheaf of abelian groups
- $\Gamma(X, \mathcal{F}) = \mathcal{F}(X)$: global sections
- $R^i\Gamma(X, \mathcal{F}) = H^i(X, \mathcal{F})$

### Example
- $H^0(X, \mathcal{F}) = \Gamma(X, \mathcal{F})$
- $H^1(X, \mathcal{O}^*) = \text{Pic}(X)$
- $H^q(\mathbb{CP}^n, \mathcal{O}(k))$: computed by Bott vanishing

---

## 21. Riemannian Metric Tensor (黎曼度量张量)

**MSC Code:** 53B20, 53C20

### English Definition
A Riemannian metric $g$ on manifold $M$ is a smooth symmetric 2-tensor field that is positive definite at each point: $g_p: T_pM \times T_pM \to \mathbb{R}$ is an inner product varying smoothly with $p$.

### 中文定义
流形$M$上的黎曼度量$g$是一个光滑对称2-张量场，在每点正定：$g_p: T_pM \times T_pM \to \mathbb{R}$是内积，且随$p$光滑变化。

### Notation
- $g = g_{ij}dx^i \otimes dx^j$: metric in coordinates
- $ds^2 = g_{ij}dx^idx^j$: line element
- $|v|_g = \sqrt{g(v,v)}$: norm of vector

### Example
- Euclidean metric on $\mathbb{R}^n$: $g_{ij} = \delta_{ij}$
- Standard metric on $S^n$: induced from $\mathbb{R}^{n+1}$
- Poincaré metric on hyperbolic space: $ds^2 = \frac{dx^2 + dy^2}{y^2}$

---

## 22. Levi-Civita Connection (列维-奇维塔联络)

**MSC Code:** 53B05, 53C05

### English Definition
The Levi-Civita connection $\nabla$ on a Riemannian manifold $(M, g)$ is the unique torsion-free connection compatible with the metric: $\nabla g = 0$ and $T(X, Y) = \nabla_X Y - \nabla_Y X - [X, Y] = 0$.

### 中文定义
黎曼流形$(M, g)$上的列维-奇维塔联络$\nabla$是唯一的与度量相容的无挠联络：$\nabla g = 0$且$T(X, Y) = \nabla_X Y - \nabla_Y X - [X, Y] = 0$。

### Notation
- $\nabla_X Y$: covariant derivative of $Y$ along $X$
- Christoffel symbols: $\nabla_{\partial_i} \partial_j = \Gamma^k_{ij} \partial_k$
- $\Gamma^k_{ij} = \frac{1}{2}g^{kl}(\partial_i g_{jl} + \partial_j g_{il} - \partial_l g_{ij})$

### Example
- On $\mathbb{R}^n$ with Euclidean metric: $\nabla_X Y = \sum X(Y^i)\partial_i$
- On sphere $S^n$: connection induced from ambient $\mathbb{R}^{n+1}$
- Parallel transport: vector field constant along curves

---

## 23. Riemann Curvature Tensor (黎曼曲率张量)

**MSC Code:** 53B20, 53C21

### English Definition
The Riemann curvature tensor $R$ measures the failure of covariant derivatives to commute: $R(X,Y)Z = \nabla_X\nabla_Y Z - \nabla_Y\nabla_X Z - \nabla_{[X,Y]}Z$. In coordinates: $R^\rho_{\sigma\mu\nu}$.

### 中文定义
黎曼曲率张量$R$度量协变导数交换的失败：$R(X,Y)Z = \nabla_X\nabla_Y Z - \nabla_Y\nabla_X Z - \nabla_{[X,Y]}Z$。在坐标下：$R^\rho_{\sigma\mu\nu}$。

### Notation
- $R(X,Y,Z,W) = g(R(X,Y)Z, W)$: $(0,4)$ curvature tensor
- Symmetries: $R_{\sigma\mu\nu\rho} = -R_{\mu\sigma\nu\rho} = -R_{\sigma\mu\rho\nu} = R_{\nu\rho\sigma\mu}$
- Bianchi identities: algebraic and differential

### Example
- Flat space: $R = 0$
- Sphere $S^n(r)$: $R(X,Y)Z = \frac{1}{r^2}(\langle Y,Z \rangle X - \langle X,Z \rangle Y)$
- Hyperbolic space: constant negative curvature

---

## 24. Ricci Curvature (里奇曲率)

**MSC Code:** 53B20, 53C21

### English Definition
The Ricci curvature $\text{Ric}$ is the trace of the Riemann tensor: $\text{Ric}_{\mu\nu} = R^\rho_{\mu\rho\nu}$. It measures volume distortion and appears in Einstein's equations.

### 中文定义
里奇曲率$\text{Ric}$是黎曼张量的迹：$\text{Ric}_{\mu\nu} = R^\rho_{\mu\rho\nu}$。它度量体积畸变并出现在爱因斯坦方程中。

### Notation
- $\text{Ric}(X,Y) = \text{tr}(Z \mapsto R(Z,X)Y)$
- $R = g^{\mu\nu}\text{Ric}_{\mu\nu}$: scalar curvature
- Einstein metric: $\text{Ric} = \lambda g$

### Example
- Euclidean space: $\text{Ric} = 0$
- Sphere $S^n(r)$: $\text{Ric} = \frac{n-1}{r^2}g$
- Schwarzschild metric: $\text{Ric} = 0$ (vacuum Einstein)

---

## 25. Sectional Curvature (截面曲率)

**MSC Code:** 53B20, 53C21

### English Definition
Sectional curvature $K(\Pi)$ for a 2-plane $\Pi \subset T_pM$ spanned by orthonormal vectors $X, Y$ is $K(\Pi) = \langle R(X,Y)Y, X \rangle$. It determines the full Riemann tensor.

### 中文定义
截面曲率$K(\Pi)$对于由标准正交向量$X, Y$张成的2-平面$\Pi \subset T_pM$定义为$K(\Pi) = \langle R(X,Y)Y, X \rangle$。它决定整个黎曼张量。

### Notation
- $K(X,Y) = \frac{\langle R(X,Y)Y, X \rangle}{|X|^2|Y|^2 - \langle X,Y \rangle^2}$
- Constant curvature: $K = \kappa$ for all planes
- Gaussian curvature: sectional curvature of surfaces

### Example
- Constant positive: sphere
- Constant negative: hyperbolic space
- Variable: general Riemannian manifolds

---

## 26. Symplectic Manifold (辛流形)

**MSC Code:** 53D05

### English Definition
A symplectic manifold $(M, \omega)$ is a smooth manifold with a closed non-degenerate 2-form $\omega \in \Omega^2(M)$: $d\omega = 0$ and $\omega^n \neq 0$ everywhere ($\dim M = 2n$).

### 中文定义
辛流形$(M, \omega)$是具有闭的非退化2-形式$\omega \in \Omega^2(M)$的光滑流形：$d\omega = 0$且处处有$\omega^n \neq 0$（$\dim M = 2n$）。

### Notation
- $\omega = \sum dp_i \wedge dq^i$: Darboux coordinates
- $d\omega = 0$: closed condition
- $\omega^n$: volume form

### Example
- $(\mathbb{R}^{2n}, \sum dp_i \wedge dq^i)$: standard symplectic
- $T^*Q$ with canonical symplectic form
- Kähler manifolds with Kähler form

---

## 27. Symplectic Form (辛形式)

**MSC Code:** 53D05

### English Definition
A symplectic form $\omega$ is a non-degenerate, skew-symmetric, closed 2-form. Non-degeneracy means $\omega(X, -) = 0 \iff X = 0$. It induces an isomorphism between vectors and covectors.

### 中文定义
辛形式$\omega$是非退化的、反对称的、闭的2-形式。非退化性意味着$\omega(X, -) = 0 \iff X = 0$。它在向量与余向量之间诱导同构。

### Notation
- $\omega^\flat: TM \to T^*M$, $X \mapsto \omega(X, -)$: flat map
- $\omega^\sharp = (\omega^\flat)^{-1}$: sharp map
- Hamiltonian vector field: $X_H = \omega^\sharp(dH)$

### Example
- $\omega = dx \wedge dy$ on $\mathbb{R}^2$
- Canonical form on $T^*Q$: $\omega = -d\theta$ where $\theta$ is Liouville form
- Fubini-Study form on $\mathbb{CP}^n$

---

## 28. Hamiltonian Vector Field (哈密顿向量场)

**MSC Code:** 53D05, 37Jxx

### English Definition
Given a Hamiltonian function $H: M \to \mathbb{R}$ on symplectic manifold $(M, \omega)$, the Hamiltonian vector field $X_H$ is defined by $\omega(X_H, -) = dH$. Flow preserves $\omega$.

### 中文定义
给定辛流形$(M, \omega)$上的哈密顿函数$H: M \to \mathbb{R}$，哈密顿向量场$X_H$由$\omega(X_H, -) = dH$定义。流保持$\omega$。

### Notation
- $X_H = \omega^\sharp(dH)$
- $\iota_{X_H}\omega = dH$: interior product
- $\mathcal{L}_{X_H}\omega = 0$: invariance of $\omega$

### Example
- On $\mathbb{R}^{2n}$: $X_H = \sum (\frac{\partial H}{\partial p_i}\frac{\partial}{\partial q^i} - \frac{\partial H}{\partial q^i}\frac{\partial}{\partial p_i})$
- Simple harmonic oscillator: $H = \frac{1}{2}(p^2 + q^2)$
- Kepler problem: $H = \frac{p^2}{2m} - \frac{k}{r}$

---

## 29. Kähler Manifold (凯勒流形)

**MSC Code:** 53C55, 32Q15

### English Definition
A Kähler manifold is a complex manifold $(M, J)$ with Hermitian metric $h = g - i\omega$ where $g$ is Riemannian, $\omega$ is symplectic (Kähler form), and $J$ is parallel: $\nabla J = 0$.

### 中文定义
凯勒流形是复流形$(M, J)$带有厄米度量$h = g - i\omega$，其中$g$是黎曼度量，$\omega$是辛形式（凯勒形式），且$J$平行：$\nabla J = 0$。

### Notation
- $J$: complex structure ($J^2 = -I$)
- $\omega(X,Y) = g(JX, Y)$: Kähler form
- $\nabla J = 0$: Kähler condition

### Example
- $\mathbb{C}^n$ with standard metric
- $\mathbb{CP}^n$ with Fubini-Study metric
- Complex tori: $\mathbb{C}^n/\Lambda$

---

## 30. Complex Structure (复结构)

**MSC Code:** 32Q15, 53C15

### English Definition
An almost complex structure $J$ on manifold $M$ is a bundle endomorphism $J: TM \to TM$ with $J^2 = -I$. It is integrable (giving a complex structure) iff the Nijenhuis tensor vanishes.

### 中文定义
流形$M$上的近复结构$J$是丛自同态$J: TM \to TM$满足$J^2 = -I$。它可积（给出复结构）当且仅当尼延黑斯张量消失。

### Notation
- $J_p: T_pM \to T_pM$, $J^2 = -I$
- $T^{1,0}M = \ker(J - iI)$: holomorphic tangent bundle
- $N_J(X,Y) = [JX,JY] - J[JX,Y] - J[X,JY] - [X,Y]$: Nijenhuis tensor

### Example
- Complex manifolds: integrable $J$
- $S^6$ has non-integrable almost complex structure
- $S^2$ is the only sphere admitting complex structure

---

## 31. Algebraic Variety (代数簇)

**MSC Code:** 14A10, 14A15

### English Definition
An algebraic variety is the zero locus of polynomial equations. An affine variety is $V \subset \mathbb{A}^n$ defined by ideal $I \subset k[x_1, \ldots, x_n]$. A projective variety lives in $\mathbb{P}^n$.

### 中文定义
代数簇是多项式方程的零点集。仿射簇是$V \subset \mathbb{A}^n$，由理想$I \subset k[x_1, \ldots, x_n]$定义。射影簇位于$\mathbb{P}^n$中。

### Notation
- $V(I) = \{x : f(x) = 0 \text{ for all } f \in I\}$
- $I(V) = \{f : f|_V = 0\}$: ideal of variety
- $\mathbb{P}^n = (\mathbb{A}^{n+1} \setminus \{0\})/\mathbb{G}_m$: projective space

### Example
- $\mathbb{A}^n$: affine $n$-space
- $V(x^2 + y^2 - 1) \subset \mathbb{A}^2$: circle
- $V(y^2 - x^3) \subset \mathbb{A}^2$: cuspidal cubic

---

## 32. Scheme (概形)

**MSC Code:** 14A15

### English Definition
A scheme $(X, \mathcal{O}_X)$ is a locally ringed space locally isomorphic to affine schemes $\text{Spec}(A)$. It generalizes algebraic varieties by allowing nilpotents and generic points.

### 中文定义
概形$(X, \mathcal{O}_X)$是局部同构于仿射概形$\text{Spec}(A)$的局部环化空间。通过允许幂零元和一般点，它推广了代数簇。

### Notation
- $\text{Spec}(A)$: prime spectrum of ring $A$
- $\mathcal{O}_X$: structure sheaf
- $X(k) = \text{Hom}(\text{Spec}(k), X)$: $k$-points

### Example
- $\text{Spec}(\mathbb{Z})$: arithmetic scheme
- $\text{Spec}(k[x]/(x^2))$: double point (nilpotent)
- Projective space $\mathbb{P}^n = \text{Proj}(k[x_0, \ldots, x_n])$

---

## 33. Sheaf (层)

**MSC Code:** 14F05, 18F20

### English Definition
A sheaf $\mathcal{F}$ on topological space $X$ assigns to each open $U \subset X$ a set (group, ring, etc.) $\mathcal{F}(U)$ with restriction maps satisfying locality and gluing axioms.

### 中文定义
拓扑空间$X$上的层$\mathcal{F}$给每个开集$U \subset X$赋予集合（群、环等）$\mathcal{F}(U)$和限制映射，满足局部性和粘合公理。

### Notation
- $\mathcal{F}(U)$: sections over $U$
- $\rho_{UV}: \mathcal{F}(U) \to \mathcal{F}(V)$ for $V \subset U$: restriction
- $\mathcal{F}_x = \varinjlim_{U \ni x} \mathcal{F}(U)$: stalk at $x$

### Example
- $\mathcal{O}_X$: structure sheaf on scheme
- $\mathcal{C}^\infty$: sheaf of smooth functions
- $\Omega^p$: sheaf of differential $p$-forms

---

## 34. Line Bundle (线丛)

**MSC Code:** 14F06, 32L05

### English Definition
A holomorphic line bundle $L$ over complex manifold $X$ is a rank-1 holomorphic vector bundle. Its isomorphism classes form the Picard group $\text{Pic}(X) \cong H^1(X, \mathcal{O}^*)$.

### 中文定义
复流形$X$上的全纯线丛$L$是秩1全纯向量丛。其同构类构成皮卡群$\text{Pic}(X) \cong H^1(X, \mathcal{O}^*)$。

### Notation
- $L \to X$: line bundle with fiber $\mathbb{C}$
- $L \otimes L'$: tensor product
- $L^* = L^{-1}$: dual line bundle
- $c_1(L) \in H^2(X, \mathbb{Z})$: first Chern class

### Example
- $\mathcal{O}(1)$ on $\mathbb{CP}^n$: hyperplane bundle
- Tautological line bundle $\mathcal{O}(-1)$ on $\mathbb{CP}^n$
- Canonical bundle $K_X = \det(T^*X)$

---

## 35. Divisor (除子)

**MSC Code:** 14C20, 14C22

### English Definition
A Weil divisor on normal variety $X$ is a formal $\mathbb{Z}$-linear combination of codimension-1 subvarieties. A Cartier divisor is locally given by a single equation. Linear equivalence classes correspond to line bundles.

### 中文定义
正规簇$X$上的韦伊除子是余维1子簇的形式$\mathbb{Z}$-线性组合。卡蒂埃除子局部由单个方程给出。线性等价类对应于线丛。

### Notation
- $\text{Div}(X)$: group of divisors
- $D \sim D'$: linear equivalence
- $\mathcal{O}(D)$: line bundle associated to divisor
- $\text{Cl}(X) = \text{Div}(X)/\text{Princ}(X)$: divisor class group

### Example
- Hyperplane $H \subset \mathbb{P}^n$: $\mathcal{O}(1)$
- Point on curve: degree 1 divisor
- Principal divisor: $(f) = \text{div}(f)$ for rational function $f$

---

## 36. Hodge Theory (霍奇理论)

**MSC Code:** 32Q15, 58A14

### English Definition
Hodge theory studies harmonic forms on compact Kähler manifolds. The Hodge decomposition states $H^k(X, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(X)$ where $H^{p,q}$ consists of classes represented by $(p,q)$-forms.

### 中文定义
霍奇理论研究紧凯勒流形上的调和形式。霍奇分解表明$H^k(X, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(X)$，其中$H^{p,q}$由$(p,q)$-形式代表的类组成。

### Notation
- $\mathcal{H}^k(X)$: harmonic $k$-forms
- $H^{p,q}(X) = H^q(X, \Omega^p)$: Dolbeault cohomology
- $\overline{H^{p,q}} = H^{q,p}$: complex conjugation
- Hodge diamond: array of $h^{p,q} = \dim H^{p,q}$

### Example
- $H^k(T^n) = \bigoplus_{p+q=k} \binom{n}{p}\binom{n}{q}$
- $H^{p,q}(\mathbb{P}^n) = \mathbb{C}$ for $p = q$ and 0 otherwise
- $H^{1,0}(C) = \Gamma(C, K_C)$: holomorphic 1-forms on curve

---

## 37. Morse Theory (莫尔斯理论)

**MSC Code:** 57R70, 58E05

### English Definition
Morse theory relates the topology of a manifold to the critical points of a Morse function $f: M \to \mathbb{R}$ (non-degenerate critical points). The Morse inequalities bound Betti numbers by numbers of critical points.

### 中文定义
莫尔斯理论将流形的拓扑与莫尔斯函数$f: M \to \mathbb{R}$（非退化临界点）的临界点联系起来。莫尔斯不等式用临界点个数限制贝蒂数。

### Notation
- $\text{Hess}(f)$: Hessian at critical point
- Index of critical point: number of negative eigenvalues
- Morse complex: chain complex with critical points as generators
- $\mu_k$: number of critical points of index $k$

### Example
- Height function on torus: 4 critical points (min, 2 saddles, max)
- $\mathbb{CP}^n$ has perfect Morse function with $n+1$ critical points
- Morse homology: $HM_*(M) \cong H_*(M)$

---

## 38. Cobordism (配边)

**MSC Code:** 57R80, 57R90

### English Definition
Two closed manifolds $M_0, M_1$ are cobordant if there exists a manifold $W$ with boundary $\partial W = M_0 \sqcup M_1$. Cobordism classes form a graded ring under disjoint union and Cartesian product.

### 中文定义
两个闭流形$M_0, M_1$配边如果存在流形$W$使得边界$\partial W = M_0 \sqcup M_1$。配边类在不交并和笛卡尔积下构成分次环。

### Notation
- $\Omega_n^O$: unoriented cobordism group
- $\Omega_n^{SO}$: oriented cobordism group
- $\Omega_n^U$: complex cobordism
- $[M] \in \Omega_n$: cobordism class

### Example
- $\Omega_0^O = \mathbb{Z}_2$, $\Omega_1^O = 0$
- $\Omega_2^O = \mathbb{Z}_2$ (torus bounds)
- $\Omega_*^{SO} \otimes \mathbb{Q} = \mathbb{Q}[\mathbb{CP}^2, \mathbb{CP}^4, \ldots]$

---

## 39. Knot Theory (纽结理论)

**MSC Code:** 57K10, 57K14

### English Definition
A knot is an embedding $K: S^1 \hookrightarrow S^3$. Knot theory studies equivalence classes under ambient isotopy. Invariants include knot polynomials, homology theories, and hyperbolic invariants.

### 中文定义
纽结是嵌入$K: S^1 \hookrightarrow S^3$。纽结理论研究环境同痕下的等价类。不变量包括纽结多项式、同调理论和双曲不变量。

### Notation
- $\Delta_K(t)$: Alexander polynomial
- $J_K(q)$: Jones polynomial
- $P_K(a, z)$: HOMFLY polynomial
- $\widehat{HFK}(K)$: knot Floer homology

### Example
- Unknot: trivial embedding
- Trefoil: simplest non-trivial knot
- Figure-eight knot: hyperbolic with volume $2v_3$

---

## 40. 3-Manifold (三维流形)

**MSC Code:** 57K30, 57K31

### English Definition
A 3-manifold is a topological space locally homeomorphic to $\mathbb{R}^3$. Key results include the prime decomposition, geometrization conjecture (theorem), and the classification of Seifert fibered spaces.

### 中文定义
三维流形是局部同胚于$\mathbb{R}^3$的拓扑空间。主要结果包括素分解、几何化猜想（定理）和塞弗特纤维空间的分类。

### Notation
- Prime decomposition: $M = M_1 \# M_2 \# \cdots \# M_k$
- JSJ decomposition: along tori
- Geometric structure: $(X, G)$-structure locally modeled on homogeneous space

### Example
- $S^3$: 3-sphere
- Lens spaces $L(p,q)$: spherical geometry
- Hyperbolic 3-manifolds: $M = \mathbb{H}^3/\Gamma$

---

## 41. 4-Manifold (四维流形)

**MSC Code:** 57K40, 57K41

### English Definition
Smooth 4-manifold topology is unique among dimensions. Key tools include intersection forms, Seiberg-Witten invariants, and Donaldson theory. Many open problems remain, including the smooth Poincaré conjecture in dimension 4.

### 中文定义
光滑四维流形拓扑在所有维度中是独特的。主要工具包括相交形式、塞伯格-威滕不变量和唐纳森理论。许多开放问题仍然存在，包括四维光滑庞加莱猜想。

### Notation
- $Q_X: H^2(X) \times H^2(X) \to \mathbb{Z}$: intersection form
- $b_2^+, b_2^-$: signature of intersection form
- $SW_X$: Seiberg-Witten invariant
- $D_X$: Donaldson invariant

### Example
- $S^4$: no exotic smooth structure known
- $\mathbb{CP}^2$: intersection form $\langle 1 \rangle$
- K3 surface: $Q_{K3} = 2(-E_8) \oplus 3H$

---

## 42. Intersection Form (相交形式)

**MSC Code:** 57K40

### English Definition
For closed oriented 4-manifold $X$, the intersection form $Q_X: H^2(X; \mathbb{Z}) \times H^2(X; \mathbb{Z}) \to \mathbb{Z}$ is defined by $Q(\alpha, \beta) = \langle \alpha \smile \beta, [X] \rangle$. It is a unimodular symmetric bilinear form.

### 中文定义
对于闭定向四维流形$X$，相交形式$Q_X: H^2(X; \mathbb{Z}) \times H^2(X; \mathbb{Z}) \to \mathbb{Z}$定义为$Q(\alpha, \beta) = \langle \alpha \smile \beta, [X] \rangle$。它是幺模对称双线性形式。

### Notation
- $Q_X$: intersection form
- Signature $\sigma(X) = b_2^+ - b_2^-$
- Unimodular: $\det Q = \pm 1$
- Definite: $Q$ is positive or negative definite

### Example
- $Q_{\mathbb{CP}^2} = \langle 1 \rangle$
- $Q_{S^2 \times S^2} = H = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
- $Q_{K3} = 2(-E_8) \oplus 3H$

---

## 43. Donaldson Invariant (唐纳森不变量)

**MSC Code:** 57K41, 58J20

### English Definition
Donaldson invariants are invariants of smooth 4-manifolds defined by counting anti-self-dual connections on $SU(2)$-bundles. They distinguish smooth structures that are homeomorphic but not diffeomorphic.

### 中文定义
唐纳森不变量是通过计数$SU(2)$丛上的反自对偶联络定义的光滑四维流形不变量。它们区分同胚但非微分同胚的光滑结构。

### Notation
- $\mathcal{M}_k$: moduli space of anti-self-dual connections
- $\mu: H_2(X) \to H^2(\mathcal{M})$: $\mu$-map
- $D_X: \text{Sym}^*(H_2(X)) \to \mathbb{Z}$: Donaldson invariant

### Example
- Donaldson's theorem: definite intersection form is diagonalizable over $\mathbb{Z}$
- $\mathbb{CP}^2 \# \overline{\mathbb{CP}^2}$ has non-trivial invariants
- Exotic $\mathbb{R}^4$: smooth structure on $\mathbb{R}^4$ not diffeomorphic to standard

---

## 44. Seiberg-Witten Invariant (塞伯格-威滕不变量)

**MSC Code:** 57K41, 58J20

### English Definition
Seiberg-Witten invariants are simpler invariants of smooth 4-manifolds defined by counting solutions to Seiberg-Witten equations on $spin^c$ structures. They often give the same information as Donaldson invariants but are easier to compute.

### 中文定义
塞伯格-威滕不变量是通过计数$spin^c$结构上塞伯格-威滕方程解定义的光滑四维流形不变量。它们通常给出与唐纳森不变量相同的信息但更易于计算。

### Notation
- $\mathfrak{s}$: $spin^c$ structure
- $SW_X(\mathfrak{s}) \in \mathbb{Z}$: Seiberg-Witten invariant
- Seiberg-Witten equations: $D_A \psi = 0$, $F_A^+ = q(\psi)$

### Example
- $SW_{K3} = 1$ for unique $spin^c$ structure with basic class 0
- Symplectic 4-manifolds: $SW(\mathfrak{s}_\omega) = \pm 1$
- Taubes' theorem: SW = Gromov-Witten for symplectic manifolds

---

## 45. Morse Homology (莫尔斯同调)

**MSC Code:** 57R70, 58E05

### English Definition
Morse homology is constructed from the critical points of a Morse function and gradient flow lines between them. It is isomorphic to singular homology and provides a link between Morse theory and Floer theory.

### 中文定义
莫尔斯同调由莫尔斯函数的临界点和它们之间的梯度流线构造。它同构于奇异同调，提供了莫尔斯理论与弗洛尔理论之间的联系。

### Notation
- $C_k = \mathbb{Z}^{\text{(critical points of index } k)}$: Morse chain group
- $\partial: C_k \to C_{k-1}$: boundary operator counting flow lines
- $HM_*(M) \cong H_*(M)$: Morse homology

### Example
- $HM_*(T^2) = H_*(T^2)$ from height function
- Perfect Morse function: $\mu_k = b_k$ (no boundary operator)
- Witten's approach: Morse theory as supersymmetric QM

---

## 46. Floer Homology (弗洛尔同调)

**MSC Code:** 57R58, 53D40

### English Definition
Floer homology is an infinite-dimensional version of Morse homology for the action functional on loop spaces or Chern-Simons functional on connections. Variants include symplectic, instanton, and Heegaard Floer homology.

### 中文定义
弗洛尔同调是莫尔斯同调的无穷维版本，作用于环空间上的作用泛函或联络上的陈-西蒙斯泛函。变体包括辛、瞬子和海加德弗洛尔同调。

### Notation
- $HF(L_0, L_1)$: Lagrangian intersection Floer homology
- $HF_*(H)$: Hamiltonian Floer homology
- $HF^+(Y)$: Heegaard Floer homology
- $\widehat{HF}(K)$: knot Floer homology

### Example
- $HF(L, L) \cong H^*(L)$ for exact Lagrangian
- $HF_*(T^*Q) \cong H_{*}(\Lambda Q)$ (free loop space)
- $\widehat{HF}(S^3) = \mathbb{Z}$

---

## 47. Gromov-Witten Invariant (格罗莫夫-威滕不变量)

**MSC Code:** 53D45, 14N35

### English Definition
Gromov-Witten invariants count pseudoholomorphic curves in symplectic manifolds. They are deformation invariants and play a central role in mirror symmetry and enumerative geometry.

### 中文定义
格罗莫夫-威滕不变量计数辛流形中的伪全纯曲线。它们是形变不变量，在镜像对称和计数几何中起核心作用。

### Notation
- $\overline{\mathcal{M}}_{g,n}(X, \beta)$: moduli space of stable maps
- $\langle \tau_{a_1}(\gamma_1) \cdots \tau_{a_n}(\gamma_n) \rangle_{g,\beta}$: GW invariant
- $QH^*(X)$: quantum cohomology

### Example
- $\langle pt, \ldots, pt \rangle_{0,d[\text{line}]} = 1$ for $\mathbb{CP}^n$
- $N_d = \langle [pt]^3 \rangle_{0,d}$: number of degree $d$ rational curves through 3 points
- Mirror symmetry relates GW invariants to period integrals

---

## 48. Mirror Symmetry (镜像对称)

**MSC Code:** 14J33, 14N35

### English Definition
Mirror symmetry is a duality between Calabi-Yau manifolds $X$ and $\check{X}$ exchanging complex and symplectic structures: $h^{p,q}(X) = h^{n-p,q}(\check{X})$. It relates A-model (GW) and B-model (variations of Hodge structure) invariants.

### 中文定义
镜像对称是卡拉比-丘流形$X$与$\check{X}$之间的对偶，交换复结构与辛结构：$h^{p,q}(X) = h^{n-p,q}(\check{X})$。它联系A模型（GW）和B模型（霍奇结构变分）不变量。

### Notation
- $X \leftrightarrow \check{X}$: mirror pair
- $q = e^{2\pi i t}$: complexified Kähler parameter
- Yukawa coupling: structure constant of quantum cohomology
- Periods: integrals of holomorphic forms

### Example
- Quintic 3-fold and its mirror: $h^{1,1} \leftrightarrow h^{2,1}$
- Local $\mathbb{P}^1$: mirror is B-model on $\mathbb{C}^2/\mathbb{Z}_2$
- HMS: homological mirror symmetry conjecture

---

## 49. Calabi-Yau Manifold (卡拉比-丘流形)

**MSC Code:** 14J32, 32Q25

### English Definition
A Calabi-Yau $n$-fold is a compact Kähler manifold with trivial canonical bundle $K_X \cong \mathcal{O}_X$ and $H^i(X, \mathcal{O}_X) = 0$ for $0 < i < n$. Yau's theorem guarantees existence of Ricci-flat Kähler metrics.

### 中文定义
卡拉比-丘$n$-流形是具有平凡典范丛$K_X \cong \mathcal{O}_X$和$H^i(X, \mathcal{O}_X) = 0$（$0 < i < n$）的紧凯勒流形。丘成桐定理保证里奇平坦凯勒度量的存在。

### Notation
- $K_X = \det(T^*X)$: canonical bundle
- $\Omega \in H^0(X, K_X)$: holomorphic volume form
- $c_1(X) = 0$: first Chern class vanishes
- $\text{Ric}(\omega) = 0$: Ricci-flat metric

### Example
- Elliptic curve ($n=1$): torus $T^2$
- K3 surface ($n=2$): $h^{1,1} = 20$, $h^{2,0} = 1$
- Quintic 3-fold in $\mathbb{P}^4$: $h^{1,1} = 1$, $h^{2,1} = 101$

---

## 50. Moduli Space (模空间)

**MSC Code:** 14D20, 14D22

### English Definition
A moduli space $\mathcal{M}$ parametrizes isomorphism classes of geometric objects. It carries universal families and is central to classification problems in algebraic geometry.

### 中文定义
模空间$\mathcal{M}$参数化几何对象的同构类。它承载泛族，是代数几何分类问题的核心。

### Notation
- $\mathcal{M}_g$: moduli of curves of genus $g$
- $\mathcal{M}_g(X, \beta)$: moduli of stable maps
- $T_{[C]}\mathcal{M}_g = H^1(C, T_C)$: tangent space via deformation theory
- Deligne-Mumford compactification: $\overline{\mathcal{M}}_g$

### Example
- $\mathcal{M}_{1,1} = \mathbb{H}/SL(2,\mathbb{Z})$: modular curve
- $\mathcal{M}_g$ has dimension $3g-3$ for $g \geq 2$
- GIT quotients: $\mathbb{P}^N/\!/G$

---

*End of Advanced Geometry and Topology Concepts*
