# Geometry and Topology (几何拓扑)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 15 core concepts in geometry and topology.

---

## 1. Metric Space (度量空间)

### English Definition
A metric space $(X, d)$ is a set $X$ with a metric $d: X \times X \to [0, \infty)$ satisfying: (1) $d(x, y) = 0 \iff x = y$; (2) $d(x, y) = d(y, x)$; (3) $d(x, z) \leq d(x, y) + d(y, z)$ (triangle inequality).

### 中文定义
度量空间$(X, d)$是一个集合$X$配上度量$d: X \times X \to [0, \infty)$，满足：(1) $d(x, y) = 0 \iff x = y$；(2) $d(x, y) = d(y, x)$；(3) $d(x, z) \leq d(x, y) + d(y, z)$（三角不等式）。

### Notation
- $d(x, y)$: distance between $x$ and $y$
- $B(x, r) = \{y : d(x, y) < r\}$: open ball
- $\bar{B}(x, r) = \{y : d(x, y) \leq r\}$: closed ball

### Example
- Euclidean space: $(\mathbb{R}^n, d_2)$ where $d_2(\mathbf{x}, \mathbf{y}) = \sqrt{\sum (x_i - y_i)^2}$
- Discrete metric: $d(x, y) = 1$ if $x \neq y$, $0$ if $x = y$

---

## 2. Open Set (开集)

### English Definition
In a metric space, a set $U$ is open if for every $x \in U$, there exists $\varepsilon > 0$ such that $B(x, \varepsilon) \subseteq U$. The collection of all open sets forms a topology.

### 中文定义
在度量空间中，集合$U$是开集，如果对每个$x \in U$，存在$\varepsilon > 0$使得$B(x, \varepsilon) \subseteq U$。所有开集的集合构成一个拓扑。

### Notation
- $U, V$: open sets
- $\mathcal{T}$: topology (collection of open sets)
- $U^\circ$: interior of $U$

### Example
- $(a, b) = \{x : a < x < b\}$ is open in $\mathbb{R}$
- $\emptyset$ and $X$ are always open
- Union of open sets is open; finite intersection of open sets is open

---

## 3. Closed Set (闭集)

### English Definition
A set is closed if its complement is open. Equivalently, $F$ is closed if it contains all its limit points: if $(x_n) \subseteq F$ and $x_n \to x$, then $x \in F$.

### 中文定义
集合是闭集，如果它的补集是开集。等价地，$F$是闭集如果它包含所有极限点：如果$(x_n) \subseteq F$且$x_n \to x$，则$x \in F$。

### Notation
- $F$: closed set
- $\bar{A}$ or $A^-$: closure of $A$
- $\partial A$: boundary of $A$

### Example
- $[a, b] = \{x : a \leq x \leq b\}$ is closed in $\mathbb{R}$
- $\{1/n : n \in \mathbb{N}\}$ is not closed (limit point $0$ missing)
- Intersection of closed sets is closed; finite union of closed sets is closed

---

## 4. Topological Space (拓扑空间)

### English Definition
A topological space $(X, \mathcal{T})$ is a set $X$ with a topology $\mathcal{T}$ (collection of open sets) satisfying: (1) $\emptyset, X \in \mathcal{T}$; (2) arbitrary unions of open sets are open; (3) finite intersections of open sets are open.

### 中文定义
拓扑空间$(X, \mathcal{T})$是一个集合$X$配上拓扑$\mathcal{T}$（开集的集合），满足：(1) $\emptyset, X \in \mathcal{T}$；(2) 开集的任意并是开集；(3) 开集的有限交是开集。

### Notation
- $(X, \mathcal{T})$: topological space
- $\mathcal{T}$: topology
- Neighborhood of $x$: open set containing $x$

### Example
- Discrete topology: $\mathcal{T} = \mathcal{P}(X)$ (all subsets open)
- Indiscrete topology: $\mathcal{T} = \{\emptyset, X\}$
- Standard topology on $\mathbb{R}^n$

---

## 5. Continuous Function (Continuous Map) (连续函数/映射)

### English Definition
A function $f: X \to Y$ between topological spaces is continuous if $f^{-1}(V)$ is open in $X$ for every open $V \subseteq Y$. Equivalently, $f^{-1}(F)$ is closed for every closed $F$.

### 中文定义
拓扑空间之间的函数$f: X \to Y$是连续的，如果对每个开集$V \subseteq Y$，$f^{-1}(V)$在$X$中是开集。等价地，对每个闭集$F$，$f^{-1}(F)$是闭集。

### Notation
- $f: X \to Y$ continuous
- Homeomorphism: continuous bijection with continuous inverse
- $X \cong Y$: homeomorphic

### Example
- Polynomials are continuous on $\mathbb{R}$
- $f: \mathbb{R} \to \mathbb{R}$, $f(x) = x^2$ is continuous
- Identity map is always continuous

---

## 6. Homeomorphism (同胚)

### English Definition
A homeomorphism is a continuous bijection $f: X \to Y$ with continuous inverse $f^{-1}: Y \to X$. Spaces are homeomorphic if there exists a homeomorphism between them.

### 中文定义
同胚是一个连续双射$f: X \to Y$且其逆$f^{-1}: Y \to X$也连续。如果两个空间之间存在同胚，则称它们同胚。

### Notation
- $f: X \xrightarrow{\sim} Y$: homeomorphism
- $X \cong Y$: $X$ is homeomorphic to $Y$
- Topological property: invariant under homeomorphism

### Example
- $(a, b) \cong (c, d)$ for any open intervals
- $(0, 1) \cong \mathbb{R}$ via $f(x) = \tan(\pi(x - \frac{1}{2}))$
- $[0, 1] \not\cong (0, 1)$ (compactness distinguishes them)

---

## 7. Compactness (紧性)

### English Definition
A space $X$ is compact if every open cover has a finite subcover. In metric spaces, compactness is equivalent to sequential compactness (every sequence has a convergent subsequence).

### 中文定义
空间$X$是紧的，如果每个开覆盖都有有限子覆盖。在度量空间中，紧性等价于序列紧性（每个序列都有收敛子序列）。

### Notation
- Compact space: every open cover has finite subcover
- Heine-Borel: in $\mathbb{R}^n$, compact $\iff$ closed and bounded

### Example
- $[a, b]$ is compact in $\mathbb{R}$ (Heine-Borel)
- $(0, 1)$ is not compact
- $S^n$ (unit sphere in $\mathbb{R}^{n+1}$) is compact

---

## 8. Connectedness (连通性)

### English Definition
A space $X$ is connected if it cannot be partitioned into two disjoint non-empty open sets. Equivalently, the only subsets that are both open and closed are $\emptyset$ and $X$.

### 中文定义
空间$X$是连通的，如果不能将它分割成两个不相交的非空开集。等价地，既开又闭的子集只有$\emptyset$和$X$。

### Notation
- Connected: no separation $X = U \cup V$ with $U, V$ disjoint open
- Path-connected: any two points can be joined by a continuous path
- Components: maximal connected subsets

### Example
- $\mathbb{R}$ is connected
- $(-\infty, 0) \cup (0, \infty)$ is disconnected
- $\mathbb{R}^n$ is path-connected for all $n$

---

## 9. Path-Connected (道路连通)

### English Definition
A space is path-connected if for any two points $x, y$, there exists a continuous function $\gamma: [0, 1] \to X$ with $\gamma(0) = x$ and $\gamma(1) = y$ (a path from $x$ to $y$).

### 中文定义
空间是道路连通的，如果对任意两点$x, y$，存在连续函数$\gamma: [0, 1] \to X$满足$\gamma(0) = x$和$\gamma(1) = y$（从$x$到$y$的道路）。

### Notation
- $\gamma: [0, 1] \to X$: path
- Path-connected: stronger than connected
- Path component: maximal path-connected subset

### Example
- $\mathbb{R}^n$ is path-connected
- Topologist's sine curve is connected but not path-connected
- Convex sets in $\mathbb{R}^n$ are path-connected

---

## 10. Manifold (流形)

### English Definition
An $n$-dimensional manifold is a Hausdorff, second-countable space locally homeomorphic to $\mathbb{R}^n$. Each point has a neighborhood homeomorphic to an open subset of $\mathbb{R}^n$.

### 中文定义
$n$维流形是豪斯多夫、第二可数的空间，局部同胚于$\mathbb{R}^n$。每一点都有一个邻域同胚于$\mathbb{R}^n$的开子集。

### Notation
- $M^n$: $n$-dimensional manifold
- Chart: $(U, \varphi)$ where $\varphi: U \to \mathbb{R}^n$ is homeomorphism
- Atlas: collection of charts covering $M$

### Example
- $\mathbb{R}^n$ is an $n$-manifold
- $S^n$ (unit sphere) is an $n$-manifold
- Torus $T^2 = S^1 \times S^1$ is a 2-manifold

---

## 11. Tangent Space (切空间)

### English Definition
The tangent space $T_pM$ at point $p$ on a manifold $M$ consists of all tangent vectors to curves passing through $p$. It is an $n$-dimensional vector space isomorphic to $\mathbb{R}^n$.

### 中文定义
流形$M$上点$p$处的切空间$T_pM$由所有过$p$点的曲线的切向量组成。它是一个$n$维向量空间，同构于$\mathbb{R}^n$。

### Notation
- $T_pM$: tangent space at $p$
- $v \in T_pM$: tangent vector
- $TM = \bigcup_{p \in M} T_pM$: tangent bundle

### Example
- $T_p\mathbb{R}^n \cong \mathbb{R}^n$
- $T_pS^2 = \{v \in \mathbb{R}^3 : v \cdot p = 0\}$ (plane perpendicular to $p$)

---

## 12. Riemannian Metric (黎曼度量)

### English Definition
A Riemannian metric $g$ on manifold $M$ assigns to each point $p$ an inner product $g_p$ on $T_pM$, varying smoothly with $p$. It allows measuring lengths and angles.

### 中文定义
流形$M$上的黎曼度量$g$给每一点$p$的切空间$T_pM$赋予内积$g_p$，且随$p$光滑变化。它允许测量长度和角度。

### Notation
- $g_p(v, w)$ or $\langle v, w \rangle_p$: inner product on $T_pM$
- $ds^2 = g_{ij}dx^idx^j$: metric in coordinates
- $(M, g)$: Riemannian manifold

### Example
- Euclidean metric on $\mathbb{R}^n$: $g_{ij} = \delta_{ij}$
- Metric on sphere: induced from ambient $\mathbb{R}^3$
- Hyperbolic metric: constant negative curvature

---

## 13. Curvature (曲率)

### English Definition
Curvature measures how a geometric object deviates from being flat. Gaussian curvature $K$ for surfaces: $K = \kappa_1 \kappa_2$ (product of principal curvatures). Riemann curvature tensor generalizes this.

### 中文定义
曲率度量几何对象偏离平坦的程度。高斯曲率$K$对曲面：$K = \kappa_1 \kappa_2$（主曲率的乘积）。黎曼曲率张量推广了这一概念。

### Notation
- $K$: Gaussian curvature
- $R_{ijkl}$: Riemann curvature tensor
- $\text{Ric}_{ij}$: Ricci curvature
- $R$: scalar curvature

### Example
- Plane: $K = 0$ everywhere
- Sphere of radius $r$: $K = \frac{1}{r^2}$ everywhere
- Pseudosphere: $K = -1$ (constant negative curvature)

---

## 14. Geodesic (测地线)

### English Definition
A geodesic is a curve that locally minimizes distance. It is the generalization of a straight line to curved spaces, satisfying the geodesic equation involving Christoffel symbols.

### 中文定义
测地线是局部最短距离的曲线。它是直线在弯曲空间中的推广，满足涉及克里斯托费尔符号的测地线方程。

### Notation
- $\gamma(t)$: geodesic curve
- $\frac{d^2x^i}{dt^2} + \Gamma^i_{jk}\frac{dx^j}{dt}\frac{dx^k}{dt} = 0$: geodesic equation
- $\Gamma^i_{jk}$: Christoffel symbols

### Example
- Geodesics on plane: straight lines
- Geodesics on sphere: great circles
- Geodesics on cylinder: helices and circles

---

## 15. Fundamental Group (基本群)

### English Definition
The fundamental group $\pi_1(X, x_0)$ consists of homotopy classes of loops based at $x_0$. It measures the "holes" in a space and is invariant under homotopy equivalence.

### 中文定义
基本群$\pi_1(X, x_0)$由基于$x_0$的回路的同伦类组成。它度量空间中的"洞"，在同伦等价下不变。

### Notation
- $\pi_1(X, x_0)$: fundamental group
- $[\gamma]$: homotopy class of loop $\gamma$
- Simply connected: $\pi_1(X) = \{e\}$ (trivial group)

### Example
- $\pi_1(\mathbb{R}^n) = \{e\}$ (simply connected)
- $\pi_1(S^1) \cong \mathbb{Z}$ (one "hole")
- $\pi_1(T^2) \cong \mathbb{Z} \times \mathbb{Z}$ (torus has two independent loops)

---

*End of Geometry and Topology Concepts*
