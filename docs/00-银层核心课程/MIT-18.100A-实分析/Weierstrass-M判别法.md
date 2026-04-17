---
course: MIT 18.100A 实分析

title: "Weierstrass M-判别法（Weierstrass M-Test）"
level: "silver"
msc_primary: "40-01"
target_courses:
  - "MIT 18.100A Ch.6"
references:
  textbooks:
    - title: "Understanding Analysis"
      author: "Stephen Abbott"
      edition: "2nd"
      chapters: "Ch. 6"
      pages: "170-173"
    - title: "Principles of Mathematical Analysis"
      author: "Walter Rudin"
      edition: "3rd"
      chapters: "Ch. 7"
      pages: "148-149"
  lectures:
    - institution: "MIT"
      course_code: "18.100A"
      lecture: "Lecture 20"
      url: "https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/"
keywords:
  - "一致收敛"
  - "函数项级数"
  - "Weierstrass判别法"
  - "Cauchy准则"
review_status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Weierstrass M-判别法（Weierstrass M-Test）

> **课程**: MIT 18.100A 实分析 | **章节**: Ch. 6 — 函数项级数与一致收敛
> **学习目标**: 掌握函数项级数一致收敛的严格定义；理解并熟练应用 Weierstrass M-判别法判断一致收敛；能够区分逐点收敛与一致收敛的本质差异

---

## 一、核心定义

### 定义 7.1（函数项级数的逐点收敛）

**严格陈述**: 设 $E \subseteq \mathbb{R}$，$\{f_n\}_{n=1}^{\infty}$ 是定义在 $E$ 上的一列实值函数。称函数项级数 $\displaystyle\sum_{n=1}^{\infty} f_n(x)$ 在 $E$ 上**逐点收敛**（pointwise convergent）于函数 $S: E \to \mathbb{R}$，若对每一个固定的 $x \in E$，数项级数 $\displaystyle\sum_{n=1}^{\infty} f_n(x)$ 收敛，且

$$S(x) = \sum_{n=1}^{\infty} f_n(x) = \lim_{N \to \infty} \sum_{n=1}^{N} f_n(x), \qquad \forall x \in E.$$

**直观解释**: 逐点收敛是"每个点各自为政"的收敛模式。对每个固定的 $x$，我们考察数列 $\{f_n(x)\}$ 的部分和是否收敛。不同点处的收敛速度可以截然不同——在某些点可能很快收敛，在某些点可能慢得惊人。逐点收敛不保证任何"整体性"质（如和函数的连续性、可积性、可导性等）。

---

### 定义 7.2（一致收敛）

**严格陈述**: 设 $E \subseteq \mathbb{R}$，$\{f_n\}_{n=1}^{\infty}$ 是定义在 $E$ 上的一列实值函数，$S: E \to \mathbb{R}$。称级数 $\displaystyle\sum_{n=1}^{\infty} f_n(x)$ 在 $E$ 上**一致收敛**（uniformly convergent）于 $S$，若

$$\forall \varepsilon > 0, \quad \exists N = N(\varepsilon) \in \mathbb{N}, \quad \forall n \geq N, \quad \forall x \in E: \quad \left|\sum_{k=1}^{n} f_k(x) - S(x)\right| < \varepsilon.$$

等价地，令 $S_n(x) = \sum_{k=1}^{n} f_k(x)$ 为部分和，则一致收敛要求

$$\lim_{n \to \infty} \sup_{x \in E} |S_n(x) - S(x)| = 0.$$

**直观解释**: 一致收敛是"全定义域统一标准"的收敛模式。对于给定的精度 $\varepsilon$，存在一个统一的 $N$，使得所有 $n \geq N$ 的部分和 $S_n(x)$ 在整个定义域 $E$ 上同时落入 $S(x)$ 的 $\varepsilon$-邻域内。几何上，这意味着当 $n$ 足够大时，$S_n(x)$ 的图像在整个 $E$ 上被"挤压"进 $S(x) \pm \varepsilon$ 的带状区域中。

> **关键区分**: 逐点收敛中 $N$ 可以依赖于 $x$（$N = N(\varepsilon, x)$）；一致收敛中 $N$ **仅依赖于** $\varepsilon$（$N = N(\varepsilon)$），与 $x$ 无关。这与"逐点连续 vs. 一致连续"的区分完全平行。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> -- 逐点收敛的定义
> def pointwiseConvergent (f : ℕ → (ℝ → ℝ)) (S : ℝ → ℝ) (E : Set ℝ) : Prop :=
>   ∀ x ∈ E, ∀ ε > 0, ∃ N, ∀ n ≥ N, |∑ k in Finset.range n, f k x - S x| < ε
>
> -- 一致收敛的定义
> def uniformConvergent (f : ℕ → (ℝ → ℝ)) (S : ℝ → ℝ) (E : Set ℝ) : Prop :=
>   ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ E, |∑ k in Finset.range n, f k x - S x| < ε
> ```

---

### 定义 7.3（一致收敛的 Cauchy 准则）

**严格陈述**: 函数项级数 $\displaystyle\sum_{n=1}^{\infty} f_n(x)$ 在 $E$ 上一致收敛，当且仅当

$$\forall \varepsilon > 0, \quad \exists N \in \mathbb{N}, \quad \forall m > n \geq N, \quad \forall x \in E: \quad \left|\sum_{k=n+1}^{m} f_k(x)\right| < \varepsilon.$$

**证明概要**（必要性）：若级数一致收敛于 $S$，则对 $\varepsilon > 0$，存在 $N$ 使得 $n \geq N$ 时对所有 $x \in E$ 有 $|S_n(x) - S(x)| < \varepsilon/2$。于是对 $m > n \geq N$：

$$\left|\sum_{k=n+1}^{m} f_k(x)\right| = |S_m(x) - S_n(x)| \leq |S_m(x) - S(x)| + |S(x) - S_n(x)| < \frac{\varepsilon}{2} + \frac{\varepsilon}{2} = \varepsilon.$$

（充分性利用 $\mathbb{R}$ 的完备性，对每个 $x$ 得到极限 $S(x)$，再验证一致收敛。）$\square$

---

## 二、核心定理与完整证明

### 定理 7.1（Weierstrass M-判别法）

**定理陈述**: 设 $E \subseteq \mathbb{R}$，$\{f_n\}_{n=1}^{\infty}$ 是定义在 $E$ 上的一列实值函数。若存在一列非负实数 $\{M_n\}_{n=1}^{\infty}$ 满足：

1. **控制条件**: $|f_n(x)| \leq M_n$ 对所有 $x \in E$ 和所有 $n \in \mathbb{N}^+$ 成立；
2. **级数收敛条件**: 数项级数 $\displaystyle\sum_{n=1}^{\infty} M_n$ **收敛**。

则函数项级数 $\displaystyle\sum_{n=1}^{\infty} f_n(x)$ 在 $E$ 上**绝对收敛**且**一致收敛**。

**证明**: 我们分两步证明：先证绝对收敛，再证一致收敛。

**第一步：证明绝对收敛。**

对任意固定的 $x \in E$，由控制条件 $|f_n(x)| \leq M_n$，且 $\sum M_n$ 收敛，根据数项级数的**比较判别法**，$\sum |f_n(x)|$ 收敛。故 $\sum f_n(x)$ 绝对收敛。

**第二步：证明一致收敛。**

我们利用**一致收敛的 Cauchy 准则**。设 $\varepsilon > 0$ 任意给定。

由于 $\sum M_n$ 收敛，其部分和序列是 Cauchy 序列。即：对上述 $\varepsilon > 0$，存在 $N \in \mathbb{N}$，使得对所有 $m > n \geq N$：

$$\sum_{k=n+1}^{m} M_k < \varepsilon.$$

（这里直接用级数收敛的 Cauchy 准则。）

现在对任意 $x \in E$ 和任意 $m > n \geq N$，估计部分和的尾部：

$$\left|\sum_{k=n+1}^{m} f_k(x)\right| \leq \sum_{k=n+1}^{m} |f_k(x)| \leq \sum_{k=n+1}^{m} M_k < \varepsilon.$$

第一个不等式是三角不等式；第二个不等式来自控制条件 $|f_k(x)| \leq M_k$；第三个严格不等式来自 $\sum M_n$ 的 Cauchy 性质。

关键观察：上述估计中的 $N$ **仅依赖于** $\varepsilon$（通过 $\sum M_n$ 的收敛性），与 $x \in E$ **无关**。因此，对所有 $x \in E$，只要 $m > n \geq N(\varepsilon)$，就有

$$\left|\sum_{k=n+1}^{m} f_k(x)\right| < \varepsilon.$$

这正是级数 $\sum f_n(x)$ 在 $E$ 上一致收敛的 Cauchy 准则。

由 Cauchy 准则，$\sum f_n(x)$ 在 $E$ 上一致收敛。$\square$

> **证明要点提示**:
>
> 1. **两个层次的 Cauchy**: Weierstrass M-判别法的精髓在于"借用"数项级数 $\sum M_n$ 的 Cauchy 性质，通过控制条件 $|f_n(x)| \leq M_n$ 将其"下传"给函数项级数 $\sum f_n(x)$。
> 2. **$N$ 的独立性**: 由于控制条件对所有 $x \in E$ 同时成立，从 $\sum M_n$ 得到的 $N$ 自动对所有 $x$ 适用。这是"一致"性的来源。
> 3. **绝对收敛的附赠**: M-判别法不仅证明一致收敛，还同时证明了绝对收敛。这在许多应用中是一个额外的好处。

---

### 定理 7.2（一致收敛的连续性保持）

**定理陈述**: 设 $\{f_n\}$ 在 $E$ 上连续，且 $\sum f_n(x)$ 在 $E$ 上一致收敛于 $S(x)$。则和函数 $S$ 在 $E$ 上连续。

**证明**: 连续函数的一致极限仍连续。对部分和 $S_n = \sum_{k=1}^{n} f_k$，每个 $S_n$ 是有限个连续函数之和，故连续。$S_n \rightrightarrows S$（一致收敛），故 $S$ 连续。$\square$

> **重要性**: 这一定理解释了为什么一致收敛在分析学中至关重要——它保证了极限运算与连续性可交换：
> $$\lim_{x \to x_0} \sum_{n=1}^{\infty} f_n(x) = \sum_{n=1}^{\infty} \lim_{x \to x_0} f_n(x).$$
> 对逐点收敛，此等式**不一定**成立。

---

## 三、典型例题

### 例题 7.1

**题目**: 证明级数 $\displaystyle\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上**一致收敛**。

**解答**:

令 $f_n(x) = \dfrac{\sin(nx)}{n^2}$，$E = \mathbb{R}$。

**验证控制条件**: 对任意 $x \in \mathbb{R}$ 和任意 $n \in \mathbb{N}^+$：

$$|f_n(x)| = \left|\frac{\sin(nx)}{n^2}\right| \leq \frac{1}{n^2}.$$

（利用 $|\sin t| \leq 1$ 对所有 $t \in \mathbb{R}$ 成立。）

取 $M_n = \dfrac{1}{n^2}$。则 $|f_n(x)| \leq M_n$ 对所有 $x \in \mathbb{R}$ 成立。

**验证级数收敛条件**: 数项级数 $\sum M_n = \sum \dfrac{1}{n^2}$ 是 $p$-级数（$p = 2 > 1$），**收敛**（其和为 $\pi^2/6$，但此处只需知道收敛即可）。

由 **Weierstrass M-判别法**，$\sum \dfrac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上绝对收敛且一致收敛。

**进一步结论**: 由于每一项 $f_n(x) = \sin(nx)/n^2$ 都在 $\mathbb{R}$ 上连续，且级数一致收敛，由**连续性保持定理**，和函数

$$S(x) = \sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$$

在 $\mathbb{R}$ 上连续。事实上，由于 $|f_n'(x)| = |\cos(nx)/n| \leq 1/n$ 且 $\sum 1/n$ 发散，M-判别法不能直接用于证明逐项可导。但利用更精细的分析可以证明 $S(x)$ 实际上是连续可导的。

**关键步骤解析**: 此例的要点在于找到**与 $x$ 无关**的上界 $M_n$。$|\sin(nx)| \leq 1$ 是通往成功的关键不等式，它消除了三角函数的振荡特性，将问题简化为纯数值级数的收敛性。

---

### 例题 7.2

**题目**: 设 $\delta > 0$。证明 Riemann $\zeta$ 函数

$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$$

在半平面 $\{s \in \mathbb{C} : \operatorname{Re}(s) \geq 1 + \delta\}$ 上**一致收敛**（从而在该半平面上表示一个连续函数）。

**解答**:

将问题置于实分析的框架下（对复参数 $s$ 的处理类似）。设 $s = \sigma + it$，其中 $\sigma = \operatorname{Re}(s)$，$t = \operatorname{Im}(s)$。令

$$f_n(s) = \frac{1}{n^s} = n^{-s} = e^{-s \ln n}.$$

对 $\operatorname{Re}(s) \geq 1 + \delta$：

$$|f_n(s)| = |n^{-s}| = |e^{-s \ln n}| = e^{-\operatorname{Re}(s) \ln n} = n^{-\operatorname{Re}(s)} \leq n^{-(1+\delta)}.$$

（这里利用了 $|e^z| = e^{\operatorname{Re}(z)}$。）

取 $M_n = n^{-(1+\delta)}$。则 $|f_n(s)| \leq M_n$ 对所有 $\operatorname{Re}(s) \geq 1 + \delta$ 成立。

数项级数 $\sum M_n = \sum \dfrac{1}{n^{1+\delta}}$ 是 $p$-级数，$p = 1 + \delta > 1$，故**收敛**。

由 **Weierstrass M-判别法**，$\zeta(s)$ 在半平面 $\operatorname{Re}(s) \geq 1 + \delta$ 上绝对收敛且一致收敛。

由于每一项 $f_n(s) = n^{-s}$ 都是 $s$ 的连续函数（实际上是全纯函数），且级数一致收敛，和函数 $\zeta(s)$ 在该半平面上**连续**（实际上在该半平面的内部全纯）。

> **注**: $\zeta(s)$ 在 $\operatorname{Re}(s) > 1$ 的每个紧子集上都一致收敛，但在整个半平面 $\operatorname{Re}(s) > 1$ 上**不一致收敛**（因为当 $s \to 1^+$ 时级数趋向发散）。引入 $\delta > 0$ 是为了获得一个"安全边界"，使 $M_n$ 具有统一的衰减率 $n^{-(1+\delta)}$。

**关键步骤解析**: 复指数函数的模估计 $|n^{-s}| = n^{-\operatorname{Re}(s)}$ 将复分析问题转化为实分析问题。参数 $\delta > 0$ 的引入是关键技巧——它为 $p$-级数提供了一个严格大于 1 的指数，从而保证收敛。

---

### 例题 7.3

**题目**: 判断级数 $\displaystyle\sum_{n=1}^{\infty} \frac{x}{n(1+nx^2)}$ 在 $\mathbb{R}$ 上是否一致收敛。

**解答**:

令 $f_n(x) = \dfrac{x}{n(1+nx^2)}$。

**寻找控制函数**: 对 $x \in \mathbb{R}$，利用 AM-GM 不等式 $1 + nx^2 \geq 2\sqrt{n}|x|$，得

$$|f_n(x)| = \frac{|x|}{n(1+nx^2)} \leq \frac{|x|}{n \cdot 2\sqrt{n}|x|} = \frac{1}{2n^{3/2}}.$$

（当 $x = 0$ 时不等式显然成立，两边均为零。）

取 $M_n = \dfrac{1}{2n^{3/2}}$。则 $|f_n(x)| \leq M_n$ 对所有 $x \in \mathbb{R}$ 成立。

数项级数 $\sum M_n = \dfrac{1}{2}\sum \dfrac{1}{n^{3/2}}$ 收敛（$p = 3/2 > 1$）。

由 **Weierstrass M-判别法**，原级数在 $\mathbb{R}$ 上绝对收敛且一致收敛。

**关键步骤解析**: 此题的难点在于找到不依赖于 $x$ 的恰当上界。直接估计 $|x|/(n(1+nx^2)) \leq |x|/(n \cdot nx^2) = 1/(n^2|x|)$ 在 $x \to 0$ 时失效。利用 AM-GM 不等式 $1 + nx^2 \geq 2\sqrt{n}|x|$ 是最简洁的路径，它同时处理了 $x$ 很大和 $x$ 很小的情形。

---

## 四、常见误区与纠正

### 误区 7.1: "逐点收敛且通项一致有界则一致收敛"

**错误观点**: 学生有时会混淆 Weierstrass M-判别法的条件，认为只要 $|f_n(x)| \leq M_n$ 对所有 $x$ 成立（即通项一致有界），且级数 $\sum f_n(x)$ 逐点收敛，那么级数就一致收敛。或者更弱地，认为"如果每个 $f_n$ 都有界，且级数逐点收敛，则一致收敛"。

**反例**: 考虑 $f_n(x) = x^n$ 在区间 $E = [0, 1)$ 上，令级数为 $S_n(x) = \sum_{k=0}^{n} (1-x)x^k$（这是一个 telescoping 的替代例子）。更清晰的反例如下：

令 $f_n(x) = x^n - x^{n+1}$ 在 $[0, 1]$ 上。则部分和

$$S_n(x) = \sum_{k=0}^{n-1} (x^k - x^{k+1}) = 1 - x^n.$$

极限函数为

$$S(x) = \begin{cases} 1, & x \in [0, 1) \\ 0, & x = 1 \end{cases}$$

因为 $S_n(1) = 0$ 对所有 $n$ 成立，故 $S(1) = 0$；对 $x \in [0, 1)$，$x^n \to 0$，故 $S(x) = 1$。

**分析**:

- 每个 $f_n(x) = x^n - x^{n+1} = x^n(1-x)$ 在 $[0, 1]$ 上满足 $0 \leq f_n(x) \leq \left(\frac{n}{n+1}\right)^n \frac{1}{n+1} \to 0$，故有统一上界。
- 级数逐点收敛于 $S(x)$。
- 但 $S(x)$ 在 $x = 1$ 处不连续，而每个 $S_n$ 都连续。若收敛是一致的，则极限函数必须连续（连续性保持定理）。矛盾。
- 更直接地，$\sup_{x \in [0,1]} |S_n(x) - S(x)| = \sup_{x \in [0,1)} x^n = 1 \not\to 0$。

> **为什么错**: Weierstrass M-判别法要求的是**控制级数** $\sum M_n$ **收敛**，而不仅仅是每个 $f_n$ 有界。上面的反例中，若尝试找 $M_n$ 使得 $|f_n(x)| \leq M_n$，最好的情况是 $M_n \sim 1/n$，而 $\sum 1/n$ 发散。因此 M-判别法不适用，且级数确实不一致收敛。

> **正确理解**:
>
> - Weierstrass M-判别法的**充分条件**是：$|f_n(x)| \leq M_n$ **且** $\sum M_n < \infty$。
> - 仅 $|f_n(x)| \leq M_n$（$\sum M_n$ 发散）**不蕴含**任何结论——级数可能一致收敛也可能不一致收敛。
> - 仅逐点收敛 + 通项一致有界 **不蕴含** 一致收敛。
> - M-判别法是**充分但非必要**条件：有许多一致收敛的级数无法用 M-判别法判定（如 $\sum (-1)^n f_n(x)$ 的 Leibniz 型一致收敛）。

---

## 五、思想方法提炼

**本章核心思想**:

1. **控制与一致性**: Weierstrass M-判别法的本质是"用一个与 $x$ 无关的数值级数来控制函数项级数"。数值级数的收敛性不依赖于任何参数，因此由其导出的 $N$ 自然对所有 $x$ 一致适用。这种"用一个简单对象控制一个复杂对象"的策略是分析学中反复出现的主题——从 M-判别法到控制收敛定理，再到 Sobolev 空间中的嵌入定理，都是同一思想的不同表现。

2. **极限运算的可交换性**: 一致收敛的核心价值在于它保证了极限运算的可交换性：
   - 极限与求和：$\displaystyle\lim_{x \to x_0} \sum f_n(x) = \sum \lim_{x \to x_0} f_n(x)$
   - 积分与求和：$\displaystyle\int \sum f_n(x)\, dx = \sum \int f_n(x)\, dx$
   - 求导与求和：$\displaystyle\frac{d}{dx} \sum f_n(x) = \sum \frac{d}{dx} f_n(x)$（在附加条件下）

   这些交换性使得函数项级数成为构造和分析函数的强大工具。

3. **充分性与必要性的区分**: M-判别法是判定一致收敛的**充分条件**，而非必要条件。学会判断何时一个定理是充分的、何时是必要的，是数学成熟度的标志。在应用中，若 M-判别法失效，还需要掌握其他工具（如 Abel 判别法、Dirichlet 判别法、Dini 定理等）。

**与后续章节的联系**:

- **Fourier 级数**: Fourier 级数的一致收敛性分析是 M-判别法的经典应用。若 Fourier 系数 $a_n, b_n$ 满足 $\sum(|a_n| + |b_n|) < \infty$，则 Fourier 级数一致收敛。
- **幂级数**: 幂级数在其收敛区间内部的任意紧子集上一致收敛（Abel 定理），这是 M-判别法的直接推论。
- **复分析**: 在复平面上，全纯函数项级数的一致收敛保持全纯性（Weierstrass 定理），这是实分析中连续性保持定理的复变版本。
- **泛函分析**: 一致收敛对应于上确界范数 $\|f\|_{\infty} = \sup_{x \in E}|f(x)|$ 下的收敛。M-判别法本质上是说：若 $\sum \|f_n\|_{\infty} < \infty$，则 $\sum f_n$ 在 Banach 空间 $(C(E), \|\cdot\|_{\infty})$ 中绝对收敛。

---

## 六、习题

### 习题 7.1

**题目**: 证明级数 $\displaystyle\sum_{n=1}^{\infty} \frac{\cos(nx)}{n^3}$ 在 $\mathbb{R}$ 上一致收敛，且其和函数 $S(x)$ 是连续可导的。

**提示**: 对原级数用 M-判别法；对逐项求导后的级数再用一次 M-判别法。

**解答**:

**第一步：原级数的一致收敛。**

$|f_n(x)| = |\cos(nx)/n^3| \leq 1/n^3 = M_n$。$\sum M_n = \sum 1/n^3$ 收敛（$p = 3 > 1$）。由 M-判别法，原级数一致收敛，故 $S(x)$ 连续。

**第二步：逐项求导后级数的一致收敛。**

$f_n'(x) = -\sin(nx)/n^2$。$|f_n'(x)| \leq 1/n^2$。$\sum 1/n^2$ 收敛。由 M-判别法，$\sum f_n'(x)$ 一致收敛。

由"逐项求导定理"（若 $\sum f_n$ 在某点收敛，且 $\sum f_n'$ 一致收敛，则 $(\sum f_n)' = \sum f_n'$），$S(x)$ 可导且

$$S'(x) = -\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}.$$

由于 $S'(x)$ 是一致收敛的连续函数项级数的和，$S'(x)$ 连续。故 $S(x)$ 连续可导。

---

### 习题 7.2

**题目**: 设 $\{a_n\}$ 是单调递减趋于零的正数列。证明级数 $\displaystyle\sum_{n=1}^{\infty} a_n \sin(nx)$ 在任意区间 $[\delta, 2\pi - \delta]$（$\delta > 0$）上一致收敛。

**提示**: 利用 Dirichlet 判别法：若 $A_n = \sum_{k=1}^{n} b_k$ 一致有界，$a_n$ 单调趋于零，则 $\sum a_n b_n$ 一致收敛。验证 $b_n = \sin(nx)$ 的部分和在 $[\delta, 2\pi - \delta]$ 上一致有界。

**解答**:

$b_n(x) = \sin(nx)$ 的部分和：

$$B_n(x) = \sum_{k=1}^{n} \sin(kx) = \frac{\cos(x/2) - \cos((n+1/2)x)}{2\sin(x/2)}.$$

对 $x \in [\delta, 2\pi - \delta]$，$\sin(x/2) \geq \sin(\delta/2) > 0$。故

$$|B_n(x)| \leq \frac{2}{2\sin(\delta/2)} = \frac{1}{\sin(\delta/2)}.$$

部分和一致有界。又 $a_n$ 单调递减趋于零，且与 $x$ 无关。由 **Dirichlet 判别法**，$\sum a_n \sin(nx)$ 在 $[\delta, 2\pi - \delta]$ 上一致收敛。

> **注**: 此题不能用 M-判别法，因为 $\sum a_n$ 可能发散（如 $a_n = 1/n$）。Dirichlet 判别法处理的是条件收敛型的一致收敛，弥补了 M-判别法仅处理绝对收敛的局限。

---

### 习题 7.3

**题目**: 设 $f_n(x) = nxe^{-nx}$ 在 $[0, 1]$ 上。判断：

(a) $f_n$ 是否在 $[0, 1]$ 上一致收敛于 $0$？

(b) $\displaystyle\lim_{n \to \infty} \int_0^1 f_n(x)\, dx$ 是否等于 $\displaystyle\int_0^1 \lim_{n \to \infty} f_n(x)\, dx$？

**提示**: (a) 求 $f_n$ 在 $[0,1]$ 上的最大值；(b) 直接计算积分。

**解答**:

(a) 对固定的 $x > 0$，$f_n(x) = nx/e^{nx} \to 0$（指数增长快于线性）。$f_n(0) = 0$。故 $f_n$ 逐点收敛于 $0$。

求最大值：$f_n'(x) = ne^{-nx} - n^2 x e^{-nx} = ne^{-nx}(1 - nx)$。令 $f_n'(x) = 0$，得 $x = 1/n$。

$$\max_{x \in [0,1]} f_n(x) = f_n(1/n) = n \cdot \frac{1}{n} \cdot e^{-1} = e^{-1} \not\to 0.$$

故 $f_n$ 在 $[0, 1]$ 上**不一致收敛**于 $0$。

(b)

$$\int_0^1 f_n(x)\, dx = \int_0^1 nxe^{-nx}\, dx.$$

令 $u = nx$，$du = n\, dx$：

$$= \int_0^n u e^{-u}\, du = [-ue^{-u} - e^{-u}]_0^n = 1 - (n+1)e^{-n} \to 1.$$

而

$$\int_0^1 \lim_{n \to \infty} f_n(x)\, dx = \int_0^1 0\, dx = 0.$$

故

$$\lim_{n \to \infty} \int_0^1 f_n(x)\, dx = 1 \neq 0 = \int_0^1 \lim_{n \to \infty} f_n(x)\, dx.$$

极限与积分**不可交换**，正是因为收敛不是一致的。

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
