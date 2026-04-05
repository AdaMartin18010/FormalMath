---
title: Analysis (分析学)
msc_primary: 00A99
processed_at: '2026-04-05'
---
# Analysis (分析学)

This document provides bilingual (English-Chinese) definitions, notations, and examples for 20 core concepts in mathematical analysis.

---

## 1. Sequence (序列)

### English Definition
A sequence in a set $X$ is a function $a: \mathbb{N} \to X$, typically written as $(a_n)_{n=1}^{\infty}$ or $(a_1, a_2, a_3, \ldots)$ where $a_n = a(n)$.

### 中文定义
集合$X$中的序列是一个函数$a: \mathbb{N} \to X$，通常记作$(a_n)_{n=1}^{\infty}$或$(a_1, a_2, a_3, \ldots)$，其中$a_n = a(n)$。

### Notation
- $(a_n)$ or $(a_n)_{n=1}^{\infty}$: sequence
- $a_n$: $n$-th term
- $\{a_n\}$: set of sequence values (distinct from sequence)

### Example
- $(1, \frac{1}{2}, \frac{1}{3}, \frac{1}{4}, \ldots) = (\frac{1}{n})_{n=1}^{\infty}$
- $(2, 4, 6, 8, \ldots) = (2n)_{n=1}^{\infty}$
- Constant sequence: $(c, c, c, \ldots)$

---

## 2. Limit of a Sequence (序列极限)

### English Definition
A sequence $(a_n)$ converges to limit $L$, denoted $\lim_{n \to \infty} a_n = L$, if for every $\varepsilon > 0$, there exists $N \in \mathbb{N}$ such that $|a_n - L| < \varepsilon$ for all $n \geq N$.

### 中文定义
序列$(a_n)$收敛于极限$L$，记作$\lim_{n \to \infty} a_n = L$，如果对任意$\varepsilon > 0$，存在$N \in \mathbb{N}$使得对所有$n \geq N$有$|a_n - L| < \varepsilon$。

### Notation
- $\lim_{n \to \infty} a_n = L$: limit
- $a_n \to L$: converges to $L$
- Divergent: no limit exists

### Example
- $\lim_{n \to \infty} \frac{1}{n} = 0$
- $\lim_{n \to \infty} (1 + \frac{1}{n})^n = e$
- $((-1)^n)$ diverges

---

## 3. Cauchy Sequence (柯西序列)

### English Definition
A sequence $(a_n)$ is Cauchy if for every $\varepsilon > 0$, there exists $N$ such that $|a_m - a_n| < \varepsilon$ for all $m, n \geq N$. In complete spaces, Cauchy sequences converge.

### 中文定义
序列$(a_n)$是柯西序列，如果对任意$\varepsilon > 0$，存在$N$使得对所有$m, n \geq N$有$|a_m - a_n| < \varepsilon$。在完备空间中，柯西序列收敛。

### Notation
- Cauchy criterion: $|a_m - a_n| < \varepsilon$
- Complete space: every Cauchy sequence converges

### Example
- Every convergent sequence is Cauchy
- In $\mathbb{Q}$, $(1, 1.4, 1.41, 1.414, \ldots)$ is Cauchy but not convergent (limit is $\sqrt{2} \notin \mathbb{Q}$)

---

## 4. Limit of a Function (函数极限)

### English Definition
$\lim_{x \to c} f(x) = L$ if for every $\varepsilon > 0$, there exists $\delta > 0$ such that $|f(x) - L| < \varepsilon$ whenever $0 < |x - c| < \delta$.

### 中文定义
$\lim_{x \to c} f(x) = L$，如果对任意$\varepsilon > 0$，存在$\delta > 0$使得当$0 < |x - c| < \delta$时有$|f(x) - L| < \varepsilon$。

### Notation
- $\lim_{x \to c} f(x)$: two-sided limit
- $\lim_{x \to c^+} f(x)$: right-hand limit
- $\lim_{x \to c^-} f(x)$: left-hand limit
- $\lim_{x \to \infty} f(x)$: limit at infinity

### Example
- $\lim_{x \to 2} x^2 = 4$
- $\lim_{x \to 0} \frac{\sin x}{x} = 1$
- $\lim_{x \to 0^+} \frac{1}{x} = +\infty$

---

## 5. Continuity (连续性)

### English Definition
A function $f$ is continuous at $c$ if $\lim_{x \to c} f(x) = f(c)$. Equivalently: for every $\varepsilon > 0$, there exists $\delta > 0$ such that $|f(x) - f(c)| < \varepsilon$ whenever $|x - c| < \delta$.

### 中文定义
函数$f$在$c$点连续，如果$\lim_{x \to c} f(x) = f(c)$。等价地：对任意$\varepsilon > 0$，存在$\delta > 0$使得当$|x - c| < \delta$时有$|f(x) - f(c)| < \varepsilon$。

### Notation
- $f \in C(A)$: $f$ is continuous on set $A$
- Continuous at $c$: $\forall \varepsilon > 0, \exists \delta > 0$
- Uniformly continuous: $\delta$ depends only on $\varepsilon$

### Example
- Polynomials are continuous everywhere
- $f(x) = \frac{1}{x}$ is continuous on $(0, \infty)$ but not at $0$
- Dirichlet function (1 on rationals, 0 on irrationals) is discontinuous everywhere

---

## 6. Uniform Continuity (一致连续)

### English Definition
$f$ is uniformly continuous on $A$ if for every $\varepsilon > 0$, there exists $\delta > 0$ such that for all $x, y \in A$, $|x - y| < \delta$ implies $|f(x) - f(y)| < \varepsilon$.

### 中文定义
$f$在$A$上一致连续，如果对任意$\varepsilon > 0$，存在$\delta > 0$使得对所有$x, y \in A$，当$|x - y| < \delta$时有$|f(x) - f(y)| < \varepsilon$。

### Notation
- Uniformly continuous: $\delta$ works for all points simultaneously
- Lipschitz continuous: $|f(x) - f(y)| \leq L|x - y|$

### Example
- $f(x) = x^2$ is uniformly continuous on $[0, 1]$ but not on $\mathbb{R}$
- Continuous functions on compact sets are uniformly continuous

---

## 7. Derivative (导数)

### English Definition
The derivative of $f$ at $a$ is $f'(a) = \lim_{h \to 0} \frac{f(a+h) - f(a)}{h}$, provided the limit exists. Geometrically, it is the slope of the tangent line.

### 中文定义
函数$f$在$a$点的导数是$f'(a) = \lim_{h \to 0} \frac{f(a+h) - f(a)}{h}$（如果极限存在）。几何上，它是切线的斜率。

### Notation
- $f'(x)$ or $\frac{df}{dx}$ or $\frac{d}{dx}f(x)$: derivative
- $\dot{y}$: derivative with respect to time
- $f^{(n)}(x)$: $n$-th derivative

### Example
- If $f(x) = x^n$, then $f'(x) = nx^{n-1}$
- $(e^x)' = e^x$, $(\ln x)' = \frac{1}{x}$, $(\sin x)' = \cos x$

---

## 8. Differentiable Function (可微函数)

### English Definition
A function is differentiable at $a$ if $f'(a)$ exists. It is differentiable on an open set if differentiable at every point of the set.

### 中文定义
函数在$a$点可微，如果$f'(a)$存在。函数在开集上可微，如果在集合的每一点都可微。

### Notation
- $C^1(A)$: continuously differentiable functions
- $C^n(A)$: functions with $n$ continuous derivatives
- $C^\infty(A)$: infinitely differentiable (smooth) functions

### Example
- $f(x) = |x|$ is not differentiable at $x = 0$
- $f(x) = x^{4/3}$ is differentiable everywhere but $C^1$ only away from $0$

---

## 9. Chain Rule (链式法则)

### English Definition
If $g$ is differentiable at $a$ and $f$ is differentiable at $g(a)$, then $(f \circ g)'(a) = f'(g(a)) \cdot g'(a)$, or $\frac{dy}{dx} = \frac{dy}{du} \cdot \frac{du}{dx}$.

### 中文定义
如果$g$在$a$点可微，$f$在$g(a)$点可微，则$(f \circ g)'(a) = f'(g(a)) \cdot g'(a)$，或$\frac{dy}{dx} = \frac{dy}{du} \cdot \frac{du}{dx}$。

### Notation
- $\frac{d}{dx}f(g(x)) = f'(g(x)) \cdot g'(x)$
- $(f \circ g)' = (f' \circ g) \cdot g'$

### Example
- $\frac{d}{dx} \sin(x^2) = \cos(x^2) \cdot 2x = 2x\cos(x^2)$
- $\frac{d}{dx} e^{3x} = e^{3x} \cdot 3 = 3e^{3x}$

---

## 10. Mean Value Theorem (中值定理)

### English Definition
If $f$ is continuous on $[a, b]$ and differentiable on $(a, b)$, then there exists $c \in (a, b)$ such that $f'(c) = \frac{f(b) - f(a)}{b - a}$.

### 中文定义
如果$f$在$[a, b]$上连续，在$(a, b)$上可微，则存在$c \in (a, b)$使得$f'(c) = \frac{f(b) - f(a)}{b - a}$。

### Notation
- MVT: Mean Value Theorem
- $f'(c) = \frac{\Delta f}{\Delta x}$: average rate of change equals instantaneous rate

### Example
- If $f(1) = 3$ and $f(5) = 11$, there exists $c \in (1, 5)$ with $f'(c) = 2$
- Used to prove: if $f' = 0$ everywhere, then $f$ is constant

---

## 11. Riemann Integral (黎曼积分)

### English Definition
The Riemann integral of $f$ on $[a, b]$ is $\int_a^b f(x)dx = \lim_{\|P\| \to 0} \sum_{i=1}^{n} f(c_i)\Delta x_i$, where $P$ is a partition and $c_i \in [x_{i-1}, x_i]$.

### 中文定义
函数$f$在$[a, b]$上的黎曼积分是$\int_a^b f(x)dx = \lim_{\|P\| \to 0} \sum_{i=1}^{n} f(c_i)\Delta x_i$，其中$P$是分割，$c_i \in [x_{i-1}, x_i]$。

### Notation
- $\int_a^b f(x)dx$: definite integral
- $F(x) = \int_a^x f(t)dt$: accumulation function
- $\|P\|$: mesh (maximum subinterval length)

### Example
- $\int_0^1 x^2 dx = \frac{1}{3}$
- Continuous functions on $[a, b]$ are Riemann integrable

---

## 12. Fundamental Theorem of Calculus (微积分基本定理)

### English Definition
Part I: If $f$ is continuous on $[a, b]$ and $F(x) = \int_a^x f(t)dt$, then $F'(x) = f(x)$. Part II: If $F' = f$, then $\int_a^b f(x)dx = F(b) - F(a)$.

### 中文定义
第一部分：如果$f$在$[a, b]$上连续，$F(x) = \int_a^x f(t)dt$，则$F'(x) = f(x)$。第二部分：如果$F' = f$，则$\int_a^b f(x)dx = F(b) - F(a)$。

### Notation
- FTC: Fundamental Theorem of Calculus
- $F(b) - F(a) = [F(x)]_a^b = F(x)|_a^b$

### Example
- $\int_0^\pi \cos x dx = \sin(\pi) - \sin(0) = 0$
- $\frac{d}{dx} \int_0^x e^{t^2} dt = e^{x^2}$

---

## 13. Series (级数)

### English Definition
An infinite series $\sum_{n=1}^{\infty} a_n$ is the limit of its partial sums $S_N = \sum_{n=1}^{N} a_n$. The series converges if $\lim_{N \to \infty} S_N$ exists.

### 中文定义
无穷级数$\sum_{n=1}^{\infty} a_n$是其部分和$S_N = \sum_{n=1}^{N} a_n$的极限。如果$\lim_{N \to \infty} S_N$存在，则称级数收敛。

### Notation
- $\sum_{n=1}^{\infty} a_n$: infinite series
- $S_N$: $N$-th partial sum
- Convergent: $\lim S_N = S$ exists
- Divergent: limit does not exist

### Example
- Geometric series: $\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}$ for $|r| < 1$
- Harmonic series: $\sum_{n=1}^{\infty} \frac{1}{n}$ diverges

---

## 14. Absolute Convergence (绝对收敛)

### English Definition
A series $\sum a_n$ converges absolutely if $\sum |a_n|$ converges. Absolute convergence implies convergence (but not conversely).

### 中文定义
级数$\sum a_n$绝对收敛，如果$\sum |a_n|$收敛。绝对收敛蕴含收敛（但反之不成立）。

### Notation
- Absolutely convergent: $\sum |a_n| < \infty$
- Conditionally convergent: converges but not absolutely

### Example
- $\sum \frac{(-1)^n}{n^2}$ converges absolutely
- $\sum \frac{(-1)^n}{n}$ converges conditionally (alternating harmonic series)

---

## 15. Power Series (幂级数)

### English Definition
A power series centered at $a$ is $\sum_{n=0}^{\infty} c_n(x-a)^n$. It has a radius of convergence $R$ such that the series converges for $|x-a| < R$ and diverges for $|x-a| > R$.

### 中文定义
以$a$为中心的幂级数是$\sum_{n=0}^{\infty} c_n(x-a)^n$。它有一个收敛半径$R$，使得级数在$|x-a| < R$时收敛，在$|x-a| > R$时发散。

### Notation
- $\sum c_n(x-a)^n$: power series
- $R$: radius of convergence
- Interval of convergence: $(a-R, a+R)$ plus possibly endpoints

### Example
- $e^x = \sum_{n=0}^{\infty} \frac{x^n}{n!}$ converges for all $x$ ($R = \infty$)
- $\frac{1}{1-x} = \sum_{n=0}^{\infty} x^n$ for $|x| < 1$ ($R = 1$)

---

## 16. Taylor Series (泰勒级数)

### English Definition
The Taylor series of $f$ at $a$ is $\sum_{n=0}^{\infty} \frac{f^{(n)}(a)}{n!}(x-a)^n$. When $a = 0$, it is called the Maclaurin series.

### 中文定义
函数$f$在$a$点的泰勒级数是$\sum_{n=0}^{\infty} \frac{f^{(n)}(a)}{n!}(x-a)^n$。当$a = 0$时，称为麦克劳林级数。

### Notation
- $f(x) = \sum_{n=0}^{\infty} \frac{f^{(n)}(a)}{n!}(x-a)^n$
- Remainder: $R_n(x) = f(x) - \sum_{k=0}^{n} \frac{f^{(k)}(a)}{k!}(x-a)^k$

### Example
- $e^x = \sum_{n=0}^{\infty} \frac{x^n}{n!} = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + \cdots$
- $\sin x = \sum_{n=0}^{\infty} (-1)^n \frac{x^{2n+1}}{(2n+1)!}$

---

## 17. Complex Number (复数)

### English Definition
A complex number has the form $z = a + bi$ where $a, b \in \mathbb{R}$ and $i^2 = -1$. The set of complex numbers $\mathbb{C}$ forms an algebraically closed field.

### 中文定义
复数的形式为$z = a + bi$，其中$a, b \in \mathbb{R}$且$i^2 = -1$。复数集$\mathbb{C}$构成一个代数闭域。

### Notation
- $z = a + bi$: complex number
- $\text{Re}(z) = a$: real part
- $\text{Im}(z) = b$: imaginary part
- $\bar{z} = a - bi$: complex conjugate
- $|z| = \sqrt{a^2 + b^2}$: modulus

### Example
- $z = 3 + 4i$ has $|z| = 5$, $\bar{z} = 3 - 4i$
- $i^2 = -1$, $i^3 = -i$, $i^4 = 1$

---

## 18. Analytic Function (解析函数)

### English Definition
A function $f$ is analytic (holomorphic) at $z_0$ if it is differentiable in a neighborhood of $z_0$. Analytic functions are infinitely differentiable and equal their Taylor series locally.

### 中文定义
函数$f$在$z_0$点解析（全纯），如果它在$z_0$的某邻域内可微。解析函数无穷可微且在局部等于其泰勒级数。

### Notation
- $f'(z) = \lim_{h \to 0} \frac{f(z+h) - f(z)}{h}$: complex derivative
- Holomorphic on domain $D$: analytic at every point of $D$
- Entire: analytic on all of $\mathbb{C}$

### Example
- Polynomials, $e^z$, $\sin z$, $\cos z$ are entire
- $f(z) = \frac{1}{z}$ is analytic on $\mathbb{C} \setminus \{0\}$
- $f(z) = \bar{z}$ is nowhere analytic

---

## 19. Cauchy-Riemann Equations (柯西-黎曼方程)

### English Definition
If $f(z) = u(x, y) + iv(x, y)$ is analytic, then $u$ and $v$ satisfy: $\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$ and $\frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$.

### 中文定义
如果$f(z) = u(x, y) + iv(x, y)$解析，则$u$和$v$满足：$\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$和$\frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$。

### Notation
- $u_x = v_y$, $u_y = -v_x$: Cauchy-Riemann equations
- $f'(z) = u_x + iv_x = v_y - iu_y$

### Example
- $f(z) = z^2 = (x^2 - y^2) + i(2xy)$: $u = x^2 - y^2$, $v = 2xy$
- Check: $u_x = 2x = v_y$ ✓, $u_y = -2y = -v_x$ ✓

---

## 20. Residue (留数)

### English Definition
The residue of $f$ at an isolated singularity $z_0$ is $\text{Res}(f, z_0) = \frac{1}{2\pi i} \oint_C f(z)dz$, where $C$ is a small loop around $z_0$. It equals the coefficient $a_{-1}$ in the Laurent expansion.

### 中文定义
函数$f$在孤立奇点$z_0$处的留数是$\text{Res}(f, z_0) = \frac{1}{2\pi i} \oint_C f(z)dz$，其中$C$是绕$z_0$的小环路。它等于洛朗展开中$a_{-1}$的系数。

### Notation
- $\text{Res}(f, z_0)$: residue
- Simple pole: $\text{Res}(f, z_0) = \lim_{z \to z_0} (z - z_0)f(z)$
- Residue theorem: $\oint_C f(z)dz = 2\pi i \sum \text{Res}(f, z_k)$

### Example
- $f(z) = \frac{1}{z}$ has $\text{Res}(f, 0) = 1$
- $\oint_{|z|=1} \frac{e^z}{z} dz = 2\pi i \cdot e^0 = 2\pi i$

---

*End of Analysis Concepts*
