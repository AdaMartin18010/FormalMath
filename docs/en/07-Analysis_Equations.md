---
title: Analysis and Differential Equations (分析与微分方程)
msc_primary: 00

  - 00A99
processed_at: '2026-04-05'
---
# Analysis and Differential Equations (分析与微分方程)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 50 core concepts in analysis and differential equations.

---

## 1. Partial Differential Equation (偏微分方程)

**MSC Code:** @, @

### English Definition
A partial differential equation (PDE) is an equation involving partial derivatives of an unknown function $u(x_1, \ldots, x_n)$. Order is the highest derivative; linearity depends on $u$ and its derivatives appearing linearly.

### 中文定义
偏微分方程（PDE）是涉及未知函数$u(x_1, \ldots, x_n)$偏导数的方程。阶数是最高导数；线性性取决于$u$及其导数是否线性出现。

### Notation
- $u_{x} = \frac{\partial u}{\partial x}$, $u_{xx} = \frac{\partial^2 u}{\partial x^2}$
- Laplacian: $\Delta u = \sum_{i=1}^n \frac{\partial^2 u}{\partial x_i^2}$
- Linear PDE: $Lu = f$ where $L$ is linear operator

### Example
- Laplace equation: $\Delta u = 0$
- Heat equation: $u_t = \Delta u$
- Wave equation: $u_{tt} = \Delta u$

---

## 2. Laplace Equation (拉普拉斯方程)

**MSC Code:** 35J05, @

### English Definition
The Laplace equation $\Delta u = 0$ describes harmonic functions. Solutions are infinitely differentiable and satisfy the mean value property. The Dirichlet problem seeks harmonic functions with prescribed boundary values.

### 中文定义
拉普拉斯方程$\Delta u = 0$描述调和函数。解是无穷可微的并满足平均值性质。狄利克雷问题寻求具有给定边界值的调和函数。

### Notation
- $\Delta = \nabla^2 = \sum \frac{\partial^2}{\partial x_i^2}$: Laplacian
- Harmonic: $\Delta u = 0$
- Mean value: $u(x) = \frac{1}{|B|}\int_B u(y)dy$

### Example
- $u(x,y) = x^2 - y^2$: harmonic in $\mathbb{R}^2$
- Fundamental solution: $\Phi(x) = \frac{1}{n(2-n)\omega_n}|x|^{2-n}$ for $n \geq 3$
- Poisson kernel for unit ball

---

## 3. Heat Equation (热方程)

**MSC Code:** 35K05, @

### English Definition
The heat equation $u_t = \Delta u$ describes diffusion processes. It is parabolic and smoothing: even discontinuous initial data becomes instantaneously smooth. The fundamental solution is the heat kernel.

### 中文定义
热方程$u_t = \Delta u$描述扩散过程。它是抛物型且光滑化的：即使不连续初值也立即变光滑。基本解是热核。

### Notation
- $u_t = \Delta u$: heat equation
- Heat kernel: $K(t,x,y) = \frac{1}{(4\pi t)^{n/2}}e^{-|x-y|^2/4t}$
- Semigroup property: $e^{t\Delta}$

### Example
- Fundamental solution: Gaussian
- Maximum principle: max attained on parabolic boundary
- Backward heat equation: ill-posed

---

## 4. Wave Equation (波动方程)

**MSC Code:** 35L05, @

### English Definition
The wave equation $u_{tt} = \Delta u$ describes wave propagation. It is hyperbolic with finite speed of propagation. Solutions satisfy Huygens' principle in odd dimensions.

### 中文定义
波动方程$u_{tt} = \Delta u$描述波的传播。它是双曲型且具有有限传播速度。解在奇数维满足惠更斯原理。

### Notation
- $u_{tt} = c^2\Delta u$: wave speed $c$
- D'Alembert solution: $u(x,t) = f(x-ct) + g(x+ct)$ in 1D
- Energy: $E(t) = \int (u_t^2 + |\nabla u|^2)dx$

### Example
- 1D wave: $u(x,t) = \sin(x-t)$
- Kirchhoff formula for 3D
- Finite propagation speed: $c$

---

## 5. Schrödinger Equation (薛定谔方程)

**MSC Code:** 35Q41, @

### English Definition
The Schrödinger equation $i\hbar\partial_t \psi = \hat{H}\psi$ governs quantum mechanical systems. The Hamiltonian $\hat{H} = -\frac{\hbar^2}{2m}\Delta + V(x)$ combines kinetic and potential energy terms.

### 中文定义
薛定谔方程$i\hbar\partial_t \psi = \hat{H}\psi$支配量子力学系统。哈密顿量$\hat{H} = -\frac{\hbar^2}{2m}\Delta + V(x)$结合动能和势能项。

### Notation
- $\psi(x,t)$: wave function
- $|\psi|^2$: probability density
- Stationary states: $\psi(x,t) = e^{-iEt/\hbar}\phi(x)$

### Example
- Free particle: $V = 0$
- Harmonic oscillator: $V = \frac{1}{2}m\omega^2 x^2$
- Hydrogen atom: $V = -\frac{e^2}{4\pi\epsilon_0 r}$

---

## 6. Sobolev Space (索伯列夫空间)

**MSC Code:** 46E35

### English Definition
Sobolev space $W^{k,p}(\Omega)$ consists of functions whose weak derivatives up to order $k$ are in $L^p$. $H^k = W^{k,2}$ is a Hilbert space. These spaces provide the natural framework for weak solutions of PDEs.

### 中文定义
索伯列夫空间$W^{k,p}(\Omega)$由弱导数直到$k$阶都在$L^p$中的函数组成。$H^k = W^{k,2}$是希尔伯特空间。这些空间为PDE弱解提供自然框架。

### Notation
- $\|u\|_{W^{k,p}} = \left(\sum_{|\alpha| \leq k} \|\partial^\alpha u\|_{L^p}^p\right)^{1/p}$
- $H_0^1(\Omega)$: closure of $C_c^\infty$ in $H^1$
- Embedding theorems: $W^{k,p} \hookrightarrow L^q$

### Example
- $u(x) = |x|^{-\alpha} \in W^{1,p}(B_1)$ for suitable $\alpha, p$
- Trace theorem: boundary values in $H^1$
- Rellich-Kondrachov: compact embedding

---

## 7. Distribution (广义函数/分布)

**MSC Code:** @

### English Definition
Distributions generalize functions via duality. A distribution $T$ is a continuous linear functional on test functions $C_c^\infty$. Every locally integrable function defines a distribution, but distributions include objects like Dirac delta.

### 中文定义
广义函数通过推广函数。分布$T$是试验函数$C_c^\infty$上的连续线性泛函。每个局部可积函数定义一个分布，但分布包括狄拉克δ等对象。

### Notation
- $\langle T, \varphi \rangle$: pairing
- $\partial^\alpha T$: distributional derivative
- $\mathcal{D}'(\Omega)$: space of distributions
- $\mathcal{S}'(\mathbb{R}^n)$: tempered distributions

### Example
- Dirac delta: $\langle \delta, \varphi \rangle = \varphi(0)$
- PV($1/x$): principal value
- Heaviside function defines distribution

---

## 8. Weak Solution (弱解)

**MSC Code:** 35D30, @

### English Definition
A weak solution satisfies the PDE in the sense of distributions. For $Lu = f$, a weak solution $u \in H^1$ satisfies $\int (Lu)\varphi = \int f\varphi$ for all test functions $\varphi$.

### 中文定义
弱解在分布意义下满足PDE。对于$Lu = f$，弱解$u \in H^1$满足对所有试验函数$\varphi$有$\int (Lu)\varphi = \int f\varphi$。

### Notation
- Bilinear form: $B[u, \varphi] = \int a^{ij}\partial_i u \partial_j \varphi + \cdots$
- Weak formulation: $B[u, \varphi] = \langle f, \varphi \rangle$
- Galerkin method for approximation

### Example
- Shock waves: discontinuous weak solutions
- Variational formulation of elliptic PDEs
- Finite element methods

---

## 9. Elliptic Regularity (椭圆正则性)

**MSC Code:** 35B65, @

### English Definition
Elliptic regularity states that weak solutions of elliptic PDEs with smooth coefficients and data are actually smooth. Interior regularity: $u \in C^\infty$ inside domain; boundary regularity requires smooth boundary.

### 中文定义
椭圆正则性表明具有光滑系数和数据的椭圆PDE的弱解实际上是光滑的。内部正则性：$u$在区域内部属于$C^\infty$；边界正则性需要光滑边界。

### Notation
- $Lu = f$ elliptic: $a^{ij}\xi_i\xi_j \geq \lambda|\xi|^2$
- $f \in C^\infty \Rightarrow u \in C^\infty$
- Schauder estimates: $C^{2,\alpha}$ bounds

### Example
- Laplace equation: harmonic functions are smooth
- Weyl's lemma: weakly harmonic implies harmonic
- Agmon-Douglis-Nirenberg estimates

---

## 10. Maximum Principle (极值原理)

**MSC Code:** 35B50, @

### English Definition
The maximum principle states that for elliptic (or parabolic) PDEs, extrema of solutions occur on the boundary. Strong maximum principle: if interior maximum, solution is constant.

### 中文定义
极值原理表明对于椭圆（或抛物）PDE，解的极值出现在边界上。强极值原理：如果有内部极大值，则解是常数。

### Notation
- $Lu \geq 0$ implies $\max u$ on boundary
- Hopf boundary lemma: sign of normal derivative
- Comparison principle

### Example
- Harmonic functions: $\max$ on boundary
- Heat equation: max on parabolic boundary
- Applications: uniqueness, a priori bounds

---

## 11. Spectral Theory (谱理论)

**MSC Code:** 47A10, @

### English Definition
Spectral theory studies the spectrum of linear operators. For bounded $T$ on Banach space, spectrum $\sigma(T) = \{\lambda : T - \lambda I \text{ not invertible}\}$. Self-adjoint operators on Hilbert spaces have real spectrum.

### 中文定义
谱理论研究线性算子的谱。对于巴拿赫空间上的有界算子$T$，谱$\sigma(T) = \{\lambda : T - \lambda I \text{ 不可逆}\}$。希尔伯特空间上的自伴算子有实谱。

### Notation
- Point spectrum (eigenvalues), continuous spectrum, residual spectrum
- Resolvent: $R(\lambda) = (T - \lambda I)^{-1}$
- Spectral radius: $r(T) = \sup\{|\lambda| : \lambda \in \sigma(T)\}$

### Example
- Finite-dimensional: spectrum = eigenvalues
- Shift operator on $\ell^2$: continuous spectrum
- Compact operators: spectrum is discrete (except 0)

---

## 12. Compact Operator (紧算子)

**MSC Code:** 47B06, 47B07

### English Definition
A compact operator $T: X \to Y$ maps bounded sets to relatively compact sets. On Hilbert spaces, compact self-adjoint operators have orthonormal eigenbases with eigenvalues tending to 0.

### 中文定义
紧算子$T: X \to Y$将有界集映射到相对紧集。在希尔伯特空间上，紧自伴算子有标准正交特征基，特征值趋于0。

### Notation
- $K(X, Y)$: space of compact operators
- $T$ compact: $\overline{T(B_X)}$ compact
- Spectral theorem for compact self-adjoint operators

### Example
- Finite-rank operators are compact
- Integral operators with continuous kernel
- Hilbert-Schmidt operators

---

## 13. Hilbert Space (希尔伯特空间)

**MSC Code:** @

### English Definition
A Hilbert space is a complete inner product space. The inner product $\langle \cdot, \cdot \rangle$ induces norm $\|x\| = \sqrt{\langle x, x \rangle}$. Hilbert spaces generalize Euclidean geometry to infinite dimensions.

### 中文定义
希尔伯特空间是完备的内积空间。内积$\langle \cdot, \cdot \rangle$诱导范数$\|x\| = \sqrt{\langle x, x \rangle}$。希尔伯特空间将欧氏几何推广到无穷维。

### Notation
- $\langle x, y \rangle$: inner product (conjugate symmetric)
- Orthonormal basis $\{e_n\}$
- Parseval identity: $\|x\|^2 = \sum |\langle x, e_n \rangle|^2$

### Example
- $\mathbb{R}^n$, $\mathbb{C}^n$ with standard inner product
- $L^2(\mu)$: square-integrable functions
- $\ell^2$: square-summable sequences

---

## 14. Banach Space (巴拿赫空间)

**MSC Code:** @

### English Definition
A Banach space is a complete normed vector space. Every Hilbert space is a Banach space, but not conversely. Key examples include $L^p$ for $p \neq 2$ and spaces of continuous functions.

### 中文定义
巴拿赫空间是完备的赋范向量空间。每个希尔伯特空间都是巴拿赫空间，但反之不成立。主要例子包括$p \neq 2$的$L^p$和连续函数空间。

### Notation
- $\|x\|$: norm
- Dual space $X^*$: continuous linear functionals
- Hahn-Banach theorem: extension of functionals

### Example
- $L^p(X, \mu)$ for $1 \leq p \leq \infty$
- $C(K)$: continuous functions on compact $K$
- $c_0$: sequences converging to 0

---

## 15. Dual Space (对偶空间)

**MSC Code:** 46B10, @

### English Definition
The dual space $X^*$ of normed space $X$ is the space of continuous linear functionals $f: X \to \mathbb{K}$. The double dual $X^{**}$ contains $X$ via evaluation map. Reflexive spaces satisfy $X^{**} = X$.

### 中文定义
赋范空间$X$的对偶空间$X^*$是连续线性泛函$f: X \to \mathbb{K}$的空间。双对偶$X^{**}$通过求值映射包含$X$。自反空间满足$X^{**} = X$。

### Notation
- $X^*$: dual space with operator norm
- Weak topology $\sigma(X, X^*)$
- Weak* topology on $X^*$

### Example
- $(L^p)^* \cong L^q$ for $1 < p < \infty$, $\frac{1}{p} + \frac{1}{q} = 1$
- $(c_0)^* \cong \ell^1$, $(\ell^1)^* \cong \ell^\infty$
- Hilbert spaces are self-dual (Riesz representation)

---

## 16. Riesz Representation Theorem (里斯表示定理)

**MSC Code:** 46C05, 46E27

### English Definition
For Hilbert space $H$, every continuous linear functional $f \in H^*$ is given by $f(x) = \langle x, y \rangle$ for unique $y \in H$. For $C(K)$, positive functionals correspond to regular Borel measures.

### 中文定义
对于希尔伯特空间$H$，每个连续线性泛函$f \in H^*$由$f(x) = \langle x, y \rangle$给出，其中唯一$y \in H$。对于$C(K)$，正泛函对应于正则博雷尔测度。

### Notation
- $H^* \cong H$: conjugate-linear isomorphism
- $C(K)^* \cong M(K)$: space of signed measures
- Riesz-Fréchet theorem (Hilbert case)

### Example
- Evaluation at point: $f \mapsto f(x_0)$
- Integration: $f \mapsto \int f d\mu$
- Weak convergence via Riesz

---

## 17. Fredholm Operator (弗雷德霍姆算子)

**MSC Code:** 47A53

### English Definition
A Fredholm operator $T: X \to Y$ has finite-dimensional kernel and cokernel, and closed range. The index $\text{ind}(T) = \dim \ker T - \dim \text{coker} T$ is stable under compact perturbations.

### 中文定义
弗雷德霍姆算子$T: X \to Y$有有限维核和余核，且值域闭。指标$\text{ind}(T) = \dim \ker T - \dim \text{coker} T$在紧扰动下稳定。

### Notation
- $\text{Fred}(X, Y)$: Fredholm operators
- Index theorem: $\text{ind}(T)$ invariants
- Atiyah-Singer index theorem

### Example
- Elliptic PDOs on compact manifolds are Fredholm
- Shift operator: index = -1
- Toeplitz operators

---

## 18. Semigroup of Operators (算子半群)

**MSC Code:** 47D03, @

### English Definition
A strongly continuous semigroup $T(t) = e^{tA}$ on Banach space solves the Cauchy problem $u'(t) = Au(t)$, $u(0) = u_0$. The generator $A$ is generally unbounded.

### 中文定义
巴拿赫空间上的强连续半群$T(t) = e^{tA}$解决柯西问题$u'(t) = Au(t)$，$u(0) = u_0$。生成元$A$通常是无界的。

### Notation
- $T(t+s) = T(t)T(s)$, $T(0) = I$
- Generator: $Ax = \lim_{t \to 0} \frac{T(t)x - x}{t}$
- Hille-Yosida theorem: characterization of generators

### Example
- Heat semigroup: $e^{t\Delta}$
- Wave equation: $e^{tA}$ with $A = \begin{pmatrix} 0 & I \\ \Delta & 0 \end{pmatrix}$
- Contraction semigroups

---

## 19. Fourier Transform (傅里叶变换)

**MSC Code:** 42A38, 42B10

### English Definition
The Fourier transform $\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x)e^{-2\pi ix\cdot\xi}dx$ decomposes functions into frequency components. It is an isometry on $L^2$ (Plancherel) and converts differentiation to multiplication.

### 中文定义
傅里叶变换$\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x)e^{-2\pi ix\cdot\xi}dx$将函数分解为频率分量。它在$L^2$上是等距（普朗歇尔）且将微分转化为乘法。

### Notation
- $\mathcal{F}(f) = \hat{f}$
- $\widehat{\partial^\alpha f}(\xi) = (2\pi i\xi)^\alpha \hat{f}(\xi)$
- Convolution: $\widehat{f * g} = \hat{f} \cdot \hat{g}$

### Example
- $\hat{e^{-\pi x^2}} = e^{-\pi \xi^2}$ (Gaussian)
- $\hat{\delta} = 1$
- Pseudodifferential operators via Fourier transform

---

## 20. Sobolev Embedding (索伯列夫嵌入)

**MSC Code:** 46E35, @

### English Definition
Sobolev embedding theorems relate Sobolev spaces to classical function spaces. If $k > n/p$, then $W^{k,p}(\mathbb{R}^n) \hookrightarrow C^{0,\alpha}$ for appropriate $\alpha$. Critical case $k = n/p$ gives borderline embeddings.

### 中文定义
索伯列夫嵌入定理联系索伯列夫空间与经典函数空间。如果$k > n/p$，则$W^{k,p}(\mathbb{R}^n) \hookrightarrow C^{0,\alpha}$对适当$\alpha$。临界情形$k = n/p$给出边界嵌入。

### Notation
- $W^{k,p} \hookrightarrow L^q$ where $\frac{1}{q} = \frac{1}{p} - \frac{k}{n}$
- Morrey's inequality
- Gagliardo-Nirenberg inequalities

### Example
- $H^1(\mathbb{R}^3) \hookrightarrow L^6(\mathbb{R}^3)$
- $W^{1,2}(\mathbb{R}) \hookrightarrow C^{0,1/2}(\mathbb{R})$
- Rellich-Kondrachov: compact embeddings

---

## 21. Harmonic Analysis (调和分析)

**MSC Code:** @, @

### English Definition
Harmonic analysis studies the decomposition of functions and operators into basic waves (Fourier analysis). It includes singular integrals, maximal functions, and Littlewood-Paley theory, with applications to PDEs.

### 中文定义
调和分析研究函数和算子分解为基本波（傅里叶分析）。它包括奇异积分、极大函数和利特尔伍德-佩利理论，应用于PDE。

### Notation
- Hardy-Littlewood maximal function
- Singular integrals: Hilbert transform, Riesz transforms
- $A_p$ weights

### Example
- Calderón-Zygmund theory
- Boundedness of singular integrals on $L^p$
- $T(1)$ theorem

---

## 22. Singular Integral (奇异积分)

**MSC Code:** 42B20, @

### English Definition
Singular integral operators have kernels with singularity on the diagonal. The Calderón-Zygmund theory provides $L^p$ boundedness for operators like the Hilbert transform $Hf(x) = \frac{1}{\pi}\text{p.v.}\int \frac{f(y)}{x-y}dy$.

### 中文定义
奇异积分算子在对角线上有奇性的核。卡尔德龙-济格蒙德理论提供$L^p$有界性，如对希尔伯特变换$Hf(x) = \frac{1}{\pi}\text{p.v.}\int \frac{f(y)}{x-y}dy$。

### Notation
- Principal value: $\text{p.v.}\int$
- Kernel $K(x,y)$ with singularity at $x = y$
- $L^2$ boundedness + kernel conditions $\Rightarrow$ $L^p$ boundedness

### Example
- Hilbert transform: $H$ on $\mathbb{R}$
- Riesz transforms: $\partial_j(-\Delta)^{-1/2}$
- Calderón-Zygmund decomposition

---

## 23. Hardy Space (哈代空间)

**MSC Code:** 42B30, 32A35

### English Definition
Hardy space $H^p$ ($0 < p \leq \infty$) consists of holomorphic functions on unit disk (or upper half-plane) with bounded $L^p$ norms on circles. Real-variable Hardy spaces require atomic decompositions.

### 中文定义
哈代空间$H^p$（$0 < p \leq \infty$）由单位圆盘（或上半平面）上具有有界$L^p$范数的全纯函数组成。实变哈代空间需要原子分解。

### Notation
- $\|f\|_{H^p} = \sup_{r < 1} \left(\int |f(re^{i\theta})|^p d\theta\right)^{1/p}$
- Atomic decomposition: $f = \sum \lambda_j a_j$
- $H^1$-BMO duality

### Example
- $H^\infty$: bounded holomorphic functions
- $H^2$: Hilbert space with orthonormal basis $\{z^n\}$
- Fefferman-Stein theory

---

## 24. BMO Space (有界平均振动空间)

**MSC Code:** 42B35, 46E30

### English Definition
BMO (bounded mean oscillation) consists of locally integrable functions with bounded oscillation over cubes. It is the dual of $H^1$ and properly contains $L^\infty$. John-Nirenberg inequality provides exponential integrability.

### 中文定义
BMO（有界平均振动）由在立方体上有界振动的局部可积函数组成。它是$H^1$的对偶且真包含$L^\infty$。约翰-尼伦伯格不等式提供指数可积性。

### Notation
- $\|f\|_{BMO} = \sup_Q \frac{1}{|Q|}\int_Q |f - f_Q|$
- $f_Q$: average over cube $Q$
- John-Nirenberg: distribution function estimate

### Example
- $\log|x| \in BMO$ but $\notin L^\infty$
- $L^\infty \subset BMO \subset \bigcap_{p < \infty} L^p_{loc}$
- Commutators: $[b, T]$ bounded iff $b \in BMO$

---

## 25. Interpolation Theory (插值理论)

**MSC Code:** 46B70, 46M35

### English Definition
Interpolation theory constructs intermediate spaces between Banach spaces. If $T$ is bounded on both $X_0$ and $X_1$, it is bounded on interpolated spaces. Methods include complex (Calderón) and real (K-, J-method) interpolation.

### 中文定义
插值理论在巴拿赫空间之间构造中间空间。如果$T$在$X_0$和$X_1$上都有界，则在插值空间上有界。方法包括复（卡尔德龙）和实（K-、J-方法）插值。

### Notation
- $(X_0, X_1)_\theta$: complex interpolation
- $(X_0, X_1)_{\theta, q}$: real interpolation
- Riesz-Thorin theorem (complex method)
- Marcinkiewicz interpolation (real method)

### Example
- $(L^1, L^\infty)_\theta = L^p$ where $\frac{1}{p} = 1 - \theta$
- Sobolev spaces via interpolation
- Nonlinear interpolation

---

## 26. Measure Theory (测度论)

**MSC Code:** @, @

### English Definition
Measure theory generalizes length, area, and volume to abstract spaces. A measure $\mu$ assigns non-negative values to measurable sets, countably additive on disjoint unions. Lebesgue measure extends Jordan measure.

### 中文定义
测度论将长度、面积和体积推广到抽象空间。测度$\mu$给可测集赋予非负值，对不交并可数可加。勒贝格测度延拓若尔当测度。

### Notation
- $\sigma$-algebra $\mathcal{M}$: collection of measurable sets
- $\mu(\bigcup E_n) = \sum \mu(E_n)$ for disjoint $E_n$
- Complete measure: subsets of null sets measurable

### Example
- Lebesgue measure on $\mathbb{R}^n$
- Counting measure
- Dirac measure: $\delta_x(A) = 1$ if $x \in A$, else 0

---

## 27. Lebesgue Integration (勒贝格积分)

**MSC Code:** 28A25, @

### English Definition
Lebesgue integration partitions the range rather than the domain. A measurable function is integrable if $\int |f| d\mu < \infty$. The integral is defined via simple functions and extends Riemann integration.

### 中文定义
勒贝格积分划分值域而非定义域。可测函数可积如果$\int |f| d\mu < \infty$。积分通过简单函数定义，延拓黎曼积分。

### Notation
- $\int f d\mu$ or $\int f(x) d\mu(x)$
- $L^1(X, \mu)$: space of integrable functions
- Monotone convergence, dominated convergence

### Example
- $\chi_\mathbb{Q}$ on $[0,1]$: Lebesgue integrable (value 0), not Riemann
- $f(x) = 1/x$ on $(0,1)$: not Lebesgue integrable
- Fubini-Tonelli theorems

---

## 28. Radon-Nikodym Theorem (拉东-尼科迪姆定理)

**MSC Code:** 28A15

### English Definition
If $\nu$ is absolutely continuous with respect to $\mu$ ($\nu \ll \mu$), there exists measurable $f$ (the Radon-Nikodym derivative) such that $\nu(E) = \int_E f d\mu$. This generalizes the fundamental theorem of calculus.

### 中文定义
如果$\nu$关于$\mu$绝对连续（$\nu \ll \mu$），则存在可测函数$f$（拉东-尼科迪姆导数）使得$\nu(E) = \int_E f d\mu$。这推广微积分基本定理。

### Notation
- $\nu \ll \mu$: absolute continuity
- $f = \frac{d\nu}{d\mu}$: Radon-Nikodym derivative
- Lebesgue decomposition: $\nu = \nu_{ac} + \nu_{sing}$

### Example
- Probability density: $d\mathbb{P} = f d\lambda$
- Conditional expectation
- Change of measure in finance

---

## 29. Probability Space (概率空间)

**MSC Code:** @

### English Definition
A probability space $(\Omega, \mathcal{F}, \mathbb{P})$ consists of sample space $\Omega$, $\sigma$-algebra $\mathcal{F}$ of events, and probability measure $\mathbb{P}$ with $\mathbb{P}(\Omega) = 1$. Random variables are measurable functions $X: \Omega \to \mathbb{R}$.

### 中文定义
概率空间$(\Omega, \mathcal{F}, \mathbb{P})$由样本空间$\Omega$、事件$\sigma$-代数$\mathcal{F}$和概率测度$\mathbb{P}$（$\mathbb{P}(\Omega) = 1$）组成。随机变量是可测函数$X: \Omega \to \mathbb{R}$。

### Notation
- $\mathbb{P}(A)$: probability of event $A$
- $\mathbb{E}[X] = \int X d\mathbb{P}$: expectation
- Distribution: $\mathbb{P}_X = \mathbb{P} \circ X^{-1}$

### Example
- Coin toss: $\Omega = \{H, T\}$, $\mathbb{P}(H) = \mathbb{P}(T) = 1/2$
- Standard normal: $\Omega = \mathbb{R}$, $d\mathbb{P} = \frac{1}{\sqrt{2\pi}}e^{-x^2/2}dx$
- Wiener space: continuous paths

---

## 30. Random Variable (随机变量)

**MSC Code:** 60A10

### English Definition
A random variable $X$ is a measurable function from probability space to measurable space. Its distribution encodes all probabilistic information. Moments like $\mathbb{E}[X]$ and $\text{Var}(X)$ capture key statistics.

### 中文定义
随机变量$X$是从概率空间到可测空间的可测函数。其分布编码所有概率信息。矩如$\mathbb{E}[X]$和$\text{Var}(X)$捕捉关键统计量。

### Notation
- $F_X(x) = \mathbb{P}(X \leq x)$: cumulative distribution function
- $f_X(x)$: probability density function (if exists)
- $\mathbb{E}[X]$, $\text{Var}(X) = \mathbb{E}[(X-\mathbb{E}[X])^2]$: mean, variance

### Example
- Bernoulli: $\mathbb{P}(X=1) = p$, $\mathbb{P}(X=0) = 1-p$
- Gaussian: $f(x) = \frac{1}{\sqrt{2\pi\sigma^2}}e^{-(x-\mu)^2/2\sigma^2}$
- Indicator: $\mathbf{1}_A(\omega) = 1$ if $\omega \in A$

---

## 31. Conditional Expectation (条件期望)

**MSC Code:** 60A10, @

### English Definition
The conditional expectation $\mathbb{E}[X|\mathcal{G}]$ is the unique $\mathcal{G}$-measurable random variable satisfying $\int_G \mathbb{E}[X|\mathcal{G}] d\mathbb{P} = \int_G X d\mathbb{P}$ for all $G \in \mathcal{G}$. It is the best prediction of $X$ given information $\mathcal{G}$.

### 中文定义
条件期望$\mathbb{E}[X|\mathcal{G}]$是唯一的$\mathcal{G}$-可测随机变量，满足对所有$G \in \mathcal{G}$有$\int_G \mathbb{E}[X|\mathcal{G}] d\mathbb{P} = \int_G X d\mathbb{P}$。它是给定信息$\mathcal{G}$下$X$的最佳预测。

### Notation
- $\mathbb{E}[X|Y] = \mathbb{E}[X|\sigma(Y)]$
- Tower property: $\mathbb{E}[\mathbb{E}[X|\mathcal{G}]|\mathcal{H}] = \mathbb{E}[X|\mathcal{H}]$ for $\mathcal{H} \subset \mathcal{G}$
- $\mathbb{E}[XY|\mathcal{G}] = X\mathbb{E}[Y|\mathcal{G}]$ if $X$ is $\mathcal{G}$-measurable

### Example
- $\mathbb{E}[X|Y]$ for discrete $Y$
- Martingale property: $\mathbb{E}[X_{n+1}|\mathcal{F}_n] = X_n$
- Bayesian updating

---

## 32. Stochastic Process (随机过程)

**MSC Code:** @

### English Definition
A stochastic process $(X_t)_{t \in T}$ is a collection of random variables indexed by time. It models random phenomena evolving in time or space. Filtrations represent information flow.

### 中文定义
随机过程$(X_t)_{t \in T}$是随时间索引的随机变量集合。它模拟随时间或空间演化的随机现象。滤过表示信息流。

### Notation
- $(\Omega, \mathcal{F}, (\mathcal{F}_t), \mathbb{P})$: filtered probability space
- Sample path: $t \mapsto X_t(\omega)$
- Finite-dimensional distributions

### Example
- Random walk: $S_n = X_1 + \cdots + X_n$
- Poisson process: counting arrivals
- Brownian motion: continuous, independent increments

---

## 33. Brownian Motion (布朗运动)

**MSC Code:** 60J65

### English Definition
Brownian motion (Wiener process) $B_t$ is a continuous Gaussian process with $B_0 = 0$, independent increments, and $B_t - B_s \sim N(0, t-s)$. It is the fundamental example of a continuous martingale.

### 中文定义
布朗运动（维纳过程）$B_t$是连续高斯过程，满足$B_0 = 0$、独立增量且$B_t - B_s \sim N(0, t-s)$。它是连续鞅的基本例子。

### Notation
- $B_t$ or $W_t$: standard Brownian motion
- Quadratic variation: $\langle B \rangle_t = t$
- Scaling: $\frac{1}{\sqrt{c}}B_{ct}$ is also Brownian motion

### Example
- Law of the iterated logarithm
- Nowhere differentiable (a.s.)
- Donsker's invariance principle

---

## 34. Martingale (鞅)

**MSC Code:** 60G42, 60G44

### English Definition
A martingale $(M_t)$ satisfies $\mathbb{E}[|M_t|] < \infty$ and $\mathbb{E}[M_t|\mathcal{F}_s] = M_s$ for $s \leq t$. It represents a fair game. Submartingales and supermartingales allow trends.

### 中文定义
鞅$(M_t)$满足$\mathbb{E}[|M_t|] < \infty$且对$s \leq t$有$\mathbb{E}[M_t|\mathcal{F}_s] = M_s$。它代表公平博弈。下鞅和上鞅允许趋势。

### Notation
- Martingale: $\mathbb{E}[M_t|\mathcal{F}_s] = M_s$
- Submartingale: $\mathbb{E}[M_t|\mathcal{F}_s] \geq M_s$
- Supermartingale: $\mathbb{E}[M_t|\mathcal{F}_s] \leq M_s$

### Example
- Brownian motion is a martingale
- $M_t = B_t^2 - t$: martingale
- Compensated Poisson process

---

## 35. Markov Process (马尔可夫过程)

**MSC Code:** @

### English Definition
A Markov process $(X_t)$ satisfies the Markov property: future depends only on present, not past. Formally, $\mathbb{P}(X_t \in A | \mathcal{F}_s) = \mathbb{P}(X_t \in A | X_s)$ for $s < t$.

### 中文定义
马尔可夫过程$(X_t)$满足马尔可夫性：未来只依赖于现在，不依赖于过去。形式上，对$s < t$有$\mathbb{P}(X_t \in A | \mathcal{F}_s) = \mathbb{P}(X_t \in A | X_s)$。

### Notation
- Transition kernel: $P(s, x; t, A) = \mathbb{P}(X_t \in A | X_s = x)$
- Chapman-Kolmogorov equation
- Generator of Markov process

### Example
- Brownian motion is Markov
- Markov chains (discrete time/state)
- Ornstein-Uhlenbeck process

---

## 36. Itô Calculus (伊藤微积分)

**MSC Code:** 60H05, @

### English Definition
Itô calculus extends calculus to stochastic integrals with respect to Brownian motion. The Itô integral $\int H_s dB_s$ is a martingale. Itô's formula includes an extra second-order term due to non-zero quadratic variation.

### 中文定义
伊藤微积分将微积分推广到关于布朗运动的随机积分。伊藤积分$\int H_s dB_s$是鞅。伊藤公式包含额外的二阶项，因为二次变差非零。

### Notation
- $\int_0^t H_s dB_s$: Itô integral
- Itô's formula: $df(B_t) = f'(B_t)dB_t + \frac{1}{2}f''(B_t)dt$
- Quadratic covariation: $[X, Y]_t$

### Example
- $\int_0^t B_s dB_s = \frac{1}{2}B_t^2 - \frac{1}{2}t$
- Geometric Brownian motion: $dS_t = \mu S_t dt + \sigma S_t dB_t$
- Itô vs Stratonovich

---

## 37. Stochastic Differential Equation (随机微分方程)

**MSC Code:** 60H10

### English Definition
An SDE $dX_t = b(X_t)dt + \sigma(X_t)dB_t$ is interpreted via Itô integral. Under Lipschitz conditions on $b$ and $\sigma$, there exists a unique strong solution. Solutions are Markov processes.

### 中文定义
SDE $dX_t = b(X_t)dt + \sigma(X_t)dB_t$通过伊藤积分解释。在$b$和$\sigma$的利普希茨条件下，存在唯一强解。解是马尔可夫过程。

### Notation
- Drift: $b(x)$
- Diffusion coefficient: $\sigma(x)$
- Strong/weak solutions
- Generator: $Lf = b \cdot \nabla f + \frac{1}{2}\text{tr}(\sigma\sigma^T D^2f)$

### Example
- Ornstein-Uhlenbeck: $dX_t = -\theta X_t dt + \sigma dB_t$
- Langevin equation
- Black-Scholes model

---

## 38. Feynman-Kac Formula (费曼-卡茨公式)

**MSC Code:** 60H30, 35K15

### English Definition
The Feynman-Kac formula represents solutions of parabolic PDEs via expectations over Brownian paths. For $\partial_t u = \Delta u + Vu$, $u(x,t) = \mathbb{E}_x[\exp(\int_0^t V(B_s)ds)f(B_t)]$.

### 中文定义
费曼-卡茨公式通过布朗路径上的期望表示抛物型PDE的解。对于$\partial_t u = \Delta u + Vu$，有$u(x,t) = \mathbb{E}_x[\exp(\int_0^t V(B_s)ds)f(B_t)]$。

### Notation
- Probabilistic representation of PDE solutions
- Kac functional: $\exp(\int_0^t V(B_s)ds)$
- Connection: PDEs $\leftrightarrow$ diffusion processes

### Example
- Heat equation: Feynman-Kac with $V = 0$
- Schrödinger equation: analytic continuation
- Exit times and Dirichlet problems

---

## 39. Malliavin Calculus (马利亚文微积分)

**MSC Code:** 60H07

### English Definition
Malliavin calculus provides a differential calculus on Wiener space. It defines a derivative operator $D$ and enables integration by parts for Wiener functionals. Applications include probabilistic proofs of Hörmander's theorem.

### 中文定义
马利亚文微积分在维纳空间上提供微分运算。它定义导数算子$D$并允许维纳泛函的分部积分。应用包括赫尔曼德定理的概率证明。

### Notation
- Malliavin derivative: $D_tF$
- Skorokhod integral: divergence operator $\delta$
- Integration by parts: $\mathbb{E}[\langle DF, u \rangle] = \mathbb{E}[F \delta(u)]$

### Example
- Differentiability of SDE solutions
- Existence of densities via Malliavin covariance
- Clark-Ocone formula

---

## 40. Functional Analysis (泛函分析)

**MSC Code:** @, @, @

### English Definition
Functional analysis studies infinite-dimensional vector spaces (function spaces) and operators between them. Key themes include duality, spectral theory, and fixed point theorems, with applications throughout analysis and PDEs.

### 中文定义
泛函分析研究无穷维向量空间（函数空间）及它们之间的算子。关键主题包括对偶性、谱理论和不动点定理，应用于分析和PDE各领域。

### Notation
- Locally convex spaces
- Operator algebras $B(H)$, $C^*$-algebras
- Spectral measures

### Example
- Spectral theorem for normal operators
- Gelfand-Naimark theorem
- Applications to quantum mechanics

---

## 41. Operator Algebra (算子代数)

**MSC Code:** @, @

### English Definition
Operator algebras are algebras of bounded operators on Hilbert space. $C^*$-algebras are norm-closed *-algebras; von Neumann algebras are weakly closed. They provide the framework for non-commutative geometry.

### 中文定义
算子代数是希尔伯特空间上有界算子的代数。$C^*$-代数是范数闭的*-代数；冯诺依曼代数是弱闭的。它们为非交换几何提供框架。

### Notation
- $B(H)$: all bounded operators
- $C^*$-algebra: $\|a^*a\| = \|a\|^2$
- von Neumann algebra: double commutant

### Example
- $C(X)$: continuous functions (commutative $C^*$-algebra)
- $K(H)$: compact operators
- Group von Neumann algebra $L(G)$

---

## 42. von Neumann Algebra (冯诺依曼代数)

**MSC Code:** 46L10

### English Definition
A von Neumann algebra is a *-subalgebra of $B(H)$ that is closed in the weak operator topology. By the double commutant theorem, $\mathcal{M} = \mathcal{M}''$ (commutant of commutant).

### 中文定义
冯诺依曼代数是$B(H)$的*-子代数且在弱算子拓扑下闭。由双交换子定理，$\mathcal{M} = \mathcal{M}''$（交换子的交换子）。

### Notation
- Types I, II, III: classification by projections
- Factor: center is scalars
- Tomita-Takesaki theory: modular automorphisms

### Example
- $B(H)$: type I factor
- $L^\infty(X)$: (commutative) type I
- Group von Neumann algebras

---

## 43. $C^*$-Algebra ($C^*$-代数)

**MSC Code:** 46L05

### English Definition
A $C^*$-algebra is a Banach *-algebra satisfying $\|a^*a\| = \|a\|^2$. They generalize function algebras and operator algebras. Commutative $C^*$-algebras are $C_0(X)$ by Gelfand duality.

### 中文定义
$C^*$-代数是满足$\|a^*a\| = \|a\|^2$的巴拿赫*-代数。它们推广函数代数和算子代数。交换$C^*$-代数由盖尔范德对偶是$C_0(X)$。

### Notation
- $C^*$-identity: $\|a^*a\| = \|a\|^2$
- Positive elements: $a = b^*b$
- States: positive linear functionals of norm 1

### Example
- $C(X)$ for compact $X$
- $M_n(\mathbb{C})$: matrix algebra
- CAR algebra, Cuntz algebras

---

## 44. Unbounded Operator (无界算子)

**MSC Code:** 47A05, 47B25

### English Definition
Unbounded operators on Hilbert space have domain a proper subspace. They arise naturally as generators of semigroups and in quantum mechanics (position, momentum operators). Self-adjointness requires careful domain specification.

### 中文定义
希尔伯特空间上的无界算子有真子空间作为定义域。它们自然地作为半群生成元和量子力学（位置、动量算子）出现。自伴性需要仔细的域规定。

### Notation
- Domain $D(A)$: dense subspace
- Graph of operator
- Self-adjoint: $A = A^*$ (including domains)
- Essentially self-adjoint

### Example
- Position operator: $(Xf)(x) = xf(x)$
- Momentum operator: $P = -i\frac{d}{dx}$
- Laplacian on $L^2(\mathbb{R}^n)$

---

## 45. Variational Method (变分方法)

**MSC Code:** 35A15, @

### English Definition
Variational methods find solutions of PDEs as critical points of functionals. The Euler-Lagrange equation gives the PDE. Direct methods in the calculus of variations establish existence via minimization.

### 中文定义
变分方法将PDE的解作为泛函的临界点寻找。欧拉-拉格朗日方程给出PDE。变分法中的直接方法通过最小化建立存在性。

### Notation
- $I[u] = \int_\Omega L(x, u, \nabla u)dx$: functional
- Euler-Lagrange: $\frac{\partial L}{\partial u} - \partial_i \frac{\partial L}{\partial u_{x_i}} = 0$
- Coercivity, weak lower semicontinuity

### Example
- Dirichlet energy: $\int |\nabla u|^2$
- $p$-Laplacian
- Mountain pass theorem

---

## 46. Critical Point Theory (临界点理论)

**MSC Code:** 58E05, 49J35

### English Definition
Critical point theory finds critical points of functionals beyond global minima. Morse theory, minimax methods, and Morse inequalities provide tools for existence of multiple solutions.

### 中文定义
临界点理论寻找泛函除全局最小外的临界点。莫尔斯理论、极小极大方法和莫尔斯不等式提供多重解存在性的工具。

### Notation
- Palais-Smale condition
- Minimax principle
- Ljusternik-Schnirelmann category
- Morse index

### Example
- Mountain pass theorem: saddle points
- Symmetric criticality principle
- Infinite-dimensional Morse theory

---

## 47. Calculus of Variations (变分法)

**MSC Code:** @, @

### English Definition
Calculus of variations optimizes functionals over functions. It generalizes finding extrema of functions to infinite-dimensional spaces. Applications include physics (least action), geometry (geodesics), and PDEs.

### 中文定义
变分法优化函数上的泛函。它将函数的极值寻找推广到无穷维空间。应用包括物理（最小作用）、几何（测地线）和PDE。

### Notation
- First variation: $\delta I = 0$
- Second variation
- Euler-Lagrange equation
- Natural boundary conditions

### Example
- Shortest path: geodesics
- Brachistochrone problem
- Minimal surfaces

---

## 48. Optimal Control (最优控制)

**MSC Code:** 49J15, 49K15

### English Definition
Optimal control finds control functions minimizing cost functional subject to dynamics. The Pontryagin maximum principle gives necessary conditions. Hamilton-Jacobi-Bellman equation provides sufficient conditions.

### 中文定义
最优控制寻找在动态约束下最小化代价泛函的控制函数。庞特里亚金最大值原理给出必要条件。哈密顿-雅可比-贝尔曼方程给出充分条件。

### Notation
- State $x(t)$, control $u(t)$
- Dynamics: $\dot{x} = f(x, u)$
- Cost: $J = \int_0^T L(x, u)dt + \psi(x(T))$
- Hamiltonian: $H(x, p, u) = p \cdot f(x, u) - L(x, u)$

### Example
- Linear-quadratic regulator
- Time-optimal control
- Rocket trajectory optimization

---

## 49. Ergodic Theory (遍历理论)

**MSC Code:** @, @

### English Definition
Ergodic theory studies measure-preserving dynamical systems. Birkhoff's ergodic theorem states time averages equal space averages for ergodic systems. It connects probability, analysis, and dynamical systems.

### 中文定义
遍历理论研究保测动力系统。伯克霍夫遍历定理表明遍历系统的时间平均等于空间平均。它联系概率、分析和动力系统。

### Notation
- Measure-preserving: $\mu(T^{-1}A) = \mu(A)$
- Ergodic: $T^{-1}A = A$ implies $\mu(A) = 0$ or $1$
- Birkhoff average: $\frac{1}{n}\sum_{k=0}^{n-1} f \circ T^k$

### Example
- Circle rotation: ergodic iff irrational angle
- Bernoulli shift: mixing
- Geodesic flow on negatively curved manifolds

---

## 50. Dynamical System (动力系统)

**MSC Code:** @, @, @

### English Definition
A dynamical system is a map $T: X \to X$ (discrete time) or flow $\phi_t: X \to X$ (continuous time) describing evolution. Orbits, invariant sets, and stability are central concerns.

### 中文定义
动力系统是映射$T: X \to X$（离散时间）或流$\phi_t: X \to X$（连续时间）描述演化。轨道、不变集和稳定性是核心关注点。

### Notation
- Orbit: $\{T^n(x) : n \geq 0\}$
- Fixed point: $T(x) = x$
- Periodic point: $T^n(x) = x$
- Attractor, basin of attraction

### Example
- Logistic map: $x_{n+1} = rx_n(1-x_n)$
- Lorenz system
- Hamiltonian systems

---

*End of Analysis and Differential Equations Concepts*
