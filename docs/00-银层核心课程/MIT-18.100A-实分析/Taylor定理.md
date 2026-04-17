---
title: "Taylor定理（Taylor's Theorem）"
level: "silver"
msc_primary: "26-01"
target_courses:
  - "MIT 18.100A Ch.6"
references:
  textbooks:
    - title: "Understanding Analysis"
      author: "Stephen Abbott"
      edition: "2nd"
      chapters: "Ch. 6"
      pages: "162-168"
    - title: "Principles of Mathematical Analysis"
      author: "Walter Rudin"
      edition: "3rd"
      chapters: "Ch. 5"
      pages: "109-111"
  lectures:
    - institution: "MIT"
      course_code: "18.100A"
      lecture: "Lecture 18-19"
      url: "https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/"
keywords:
  - "Taylor展开"
  - "Lagrange余项"
  - "多项式逼近"
  - "Cauchy中值定理"
review_status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Taylor定理（Taylor's Theorem）

> **课程**: MIT 18.100A 实分析 | **章节**: Ch. 6 — 微分学的进一步话题
> **学习目标**: 掌握带 Lagrange 余项的 Taylor 定理的严格表述与证明；能够计算常见初等函数的 Taylor 展开并进行余项估计；理解 Taylor 级数与函数本身的关系

---

## 一、核心定义

### 定义 6.1（$n$ 阶可导与 Taylor 多项式）

**严格陈述**: 设 $f$ 在含 $x_0$ 的某开区间 $I$ 上**$n$ 阶可导**（即 $f', f'', \ldots, f^{(n)}$ 都在 $I$ 上存在）。称

$$P_n(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k$$

为 $f$ 在 $x_0$ 处的 **$n$ 阶 Taylor 多项式**。其中约定 $f^{(0)} = f$，$0! = 1$。

称

$$R_n(x) = f(x) - P_n(x)$$

为 **$n$ 阶余项**（remainder）。

**直观解释**: Taylor 多项式 $P_n(x)$ 是用 $x_0$ 处可获取的局部信息（各阶导数值）构造出的一个多项式，它企图在 $x_0$ 附近"最佳地"逼近原函数 $f(x)$。之所以说"最佳"，是因为 $P_n$ 与 $f$ 在 $x_0$ 处具有相同的前 $n$ 阶导数：$P_n^{(k)}(x_0) = f^{(k)}(x_0)$ 对 $k = 0, 1, \ldots, n$ 均成立。余项 $R_n(x)$ 则量化了这种逼近的误差。

---

### 定义 6.2（Taylor 级数）

**严格陈述**: 设 $f$ 在 $x_0$ 处**无穷阶可导**（smooth），即所有阶导数 $f^{(k)}(x_0)$（$k = 0, 1, 2, \ldots$）都存在。称形式幂级数

$$\sum_{k=0}^{\infty} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k$$

为 $f$ 在 $x_0$ 处的 **Taylor 级数**。若该级数在某区间 $(x_0 - R, x_0 + R)$ 内收敛于 $f(x)$，则称 $f$ 在该区间内可展开为 Taylor 级数。

> **重要区分**: Taylor **定理**处理的是**有限阶**展开（$n$ 阶多项式 + 余项），是一个精确的等式；Taylor **级数**处理的是**无穷级数**，涉及收敛性问题。二者概念相关但不可混为一谈。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> -- Taylor 多项式的定义
> def taylorPolynomial (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
>   ∑ k in Finset.range (n + 1), (iteratedDeriv k f x₀) / k.factorial * (x - x₀) ^ k
>
> -- Taylor 余项
> def taylorRemainder (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
>   f x - taylorPolynomial f x₀ n x
> ```

---

## 二、核心定理与完整证明

### 定理 6.1（Taylor 定理 — 带 Lagrange 余项）

**定理陈述**: 设 $f$ 在闭区间 $[a, b]$ 上**$n$ 阶连续可导**（即 $f, f', \ldots, f^{(n)}$ 都在 $[a, b]$ 上连续），且在开区间 $(a, b)$ 上**$n+1$ 阶可导**。任取 $x_0 \in [a, b]$，则对任意 $x \in [a, b]$，存在 $c$ 严格介于 $x_0$ 与 $x$ 之间，使得

$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n+1)}(c)}{(n+1)!}(x - x_0)^{n+1}.$$

即

$$f(x) = P_n(x) + R_n(x),$$

其中 Lagrange 余项为

$$R_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!}(x - x_0)^{n+1}.$$

**证明**: 不妨设 $x > x_0$（$x < x_0$ 的情形完全对称；$x = x_0$ 时等式两边均为 $f(x_0)$，显然成立）。

固定 $x$ 和 $x_0$。对 $t \in [x_0, x]$，定义**辅助函数**

$$F(t) = f(x) - \sum_{k=0}^{n} \frac{f^{(k)}(t)}{k!}(x - t)^k.$$

**第一步：计算 $F(x_0)$ 和 $F(x)$。**

$$F(x_0) = f(x) - \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k = f(x) - P_n(x) = R_n(x).$$

$$F(x) = f(x) - \sum_{k=0}^{n} \frac{f^{(k)}(x)}{k!}(x - x)^k = f(x) - \frac{f^{(0)}(x)}{0!} \cdot 1 = f(x) - f(x) = 0.$$

**第二步：计算 $F'(t)$。**

对 $F(t)$ 关于 $t$ 求导。注意 $f(x)$ 是常数（相对于 $t$），而每一项 $\dfrac{f^{(k)}(t)}{k!}(x - t)^k$ 都是两个 $t$ 的函数的乘积。

$$F'(t) = -\sum_{k=0}^{n} \frac{d}{dt}\left[\frac{f^{(k)}(t)}{k!}(x - t)^k\right].$$

对每个 $k$，用乘积法则：

$$\frac{d}{dt}\left[\frac{f^{(k)}(t)}{k!}(x - t)^k\right] = \frac{f^{(k+1)}(t)}{k!}(x - t)^k + \frac{f^{(k)}(t)}{k!} \cdot k(x - t)^{k-1} \cdot (-1)$$

$$= \frac{f^{(k+1)}(t)}{k!}(x - t)^k - \frac{f^{(k)}(t)}{(k-1)!}(x - t)^{k-1}.$$

（注意：$k = 0$ 时，第二项按约定为零，因为 $(-1)!$ 无定义，但实际上 $k=0$ 时 $(x-t)^k$ 的导数贡献为零。）

现在写出求和：

$$F'(t) = -\sum_{k=0}^{n} \left[\frac{f^{(k+1)}(t)}{k!}(x - t)^k - \frac{f^{(k)}(t)}{(k-1)!}(x - t)^{k-1}\right]$$

$$= -\sum_{k=0}^{n} \frac{f^{(k+1)}(t)}{k!}(x - t)^k + \sum_{k=0}^{n} \frac{f^{(k)}(t)}{(k-1)!}(x - t)^{k-1}.$$

对第二个求和做指标替换 $j = k - 1$，则当 $k = 0$ 时该项为零（可忽略），$k$ 从 $1$ 到 $n$ 时 $j$ 从 $0$ 到 $n-1$：

$$\sum_{k=1}^{n} \frac{f^{(k)}(t)}{(k-1)!}(x - t)^{k-1} = \sum_{j=0}^{n-1} \frac{f^{(j+1)}(t)}{j!}(x - t)^j.$$

代回 $F'(t)$：

$$F'(t) = -\sum_{k=0}^{n} \frac{f^{(k+1)}(t)}{k!}(x - t)^k + \sum_{j=0}^{n-1} \frac{f^{(j+1)}(t)}{j!}(x - t)^j$$

$$= -\frac{f^{(n+1)}(t)}{n!}(x - t)^n.$$

所有中间项 $k = 0, 1, \ldots, n-1$ 都相互抵消了（望远镜求和）。

**第三步：应用 Cauchy 中值定理。**

引入第二个辅助函数

$$G(t) = (x - t)^{n+1}.$$

$G$ 在 $[x_0, x]$ 上连续，在 $(x_0, x)$ 上可导，且

$$G'(t) = -(n+1)(x - t)^n.$$

注意 $G'(t) \neq 0$ 对所有 $t \in (x_0, x)$ 成立（因为 $x - t > 0$）。

现在对 $F$ 和 $G$ 在 $[x_0, x]$ 上应用 **Cauchy 中值定理**：存在 $c \in (x_0, x)$ 使得

$$\frac{F(x) - F(x_0)}{G(x) - G(x_0)} = \frac{F'(c)}{G'(c)}.$$

计算各项：

- $F(x) = 0$，$F(x_0) = R_n(x)$；
- $G(x) = 0$，$G(x_0) = (x - x_0)^{n+1}$；
- $F'(c) = -\dfrac{f^{(n+1)}(c)}{n!}(x - c)^n$；
- $G'(c) = -(n+1)(x - c)^n$。

代入：

$$\frac{0 - R_n(x)}{0 - (x - x_0)^{n+1}} = \frac{-\dfrac{f^{(n+1)}(c)}{n!}(x - c)^n}{-(n+1)(x - c)^n}.$$

化简左边：

$$\frac{-R_n(x)}{-(x - x_0)^{n+1}} = \frac{R_n(x)}{(x - x_0)^{n+1}}.$$

化简右边：

$$\frac{f^{(n+1)}(c)}{n!} \cdot \frac{1}{(n+1)} = \frac{f^{(n+1)}(c)}{(n+1)!}.$$

（注意 $(x - c)^n$ 被约去，要求 $x \neq c$，这在 $c \in (x_0, x)$ 时成立。）

因此

$$\frac{R_n(x)}{(x - x_0)^{n+1}} = \frac{f^{(n+1)}(c)}{(n+1)!},$$

即

$$R_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!}(x - x_0)^{n+1}.$$

代回 $R_n(x) = f(x) - P_n(x)$ 即得所求等式。$\square$

> **证明要点提示**:
>
> 1. **辅助函数 $F(t)$ 的构造**: 将 $x$ 固定，让展开中心 $t$ 变化。$F(t)$ 表示"以 $t$ 为中心展开到 $n$ 阶时，在 $x$ 处的误差"。当 $t = x$ 时，误差为零（因为在展开中心处零阶展开就是精确值）。
> 2. **望远镜求和**: $F'(t)$ 的计算中，中间项全部抵消，仅余最高阶项。这是精心构造辅助函数的回报。
> 3. **Cauchy 中值定理的妙用**: 引入 $G(t) = (x-t)^{n+1}$ 是为了在应用 Cauchy 中值定理时，恰好让 $(x-c)^n$ 项在分子分母中约去，从而得到整洁的 $(n+1)!$ 阶乘形式。

---

### 推论 6.2（带 Peano 余项的 Taylor 公式）

**严格陈述**: 若 $f$ 在 $x_0$ 处 $n$ 阶可导，则

$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + o\big((x - x_0)^n\big), \qquad x \to x_0.$$

即

$$\lim_{x \to x_0} \frac{R_n(x)}{(x - x_0)^n} = 0.$$

> **Lagrange 余项 vs. Peano 余项**: Lagrange 余项给出了误差的**精确表达式**（含某个中间点 $c$），适用于全局估计；Peano 余项只给出了误差的**渐近阶数**（$o$ 记号），适用于局部极限计算，但要求的条件更弱（只需 $n$ 阶可导，无需 $n+1$ 阶可导）。

---

## 三、典型例题

### 例题 6.1（$e^x$ 的 Taylor 展开）

**题目**: 求 $f(x) = e^x$ 在 $x_0 = 0$ 处的 $n$ 阶 Taylor 展开及 Lagrange 余项，并由此证明 $e^x$ 的 Taylor 级数对所有 $x \in \mathbb{R}$ 收敛于 $e^x$。

**解答**:

$f(x) = e^x$ 的各阶导数均为 $f^{(k)}(x) = e^x$，故 $f^{(k)}(0) = 1$ 对所有 $k \geq 0$ 成立。

$n$ 阶 Taylor 多项式为

$$P_n(x) = \sum_{k=0}^{n} \frac{x^k}{k!} = 1 + x + \frac{x^2}{2!} + \cdots + \frac{x^n}{n!}.$$

Lagrange 余项为

$$R_n(x) = \frac{e^c}{(n+1)!} x^{n+1},$$

其中 $c$ 介于 $0$ 与 $x$ 之间。

**余项估计与收敛性**: 对固定的 $x \in \mathbb{R}$，取 $M = \max\{1, e^x\}$。由于 $c$ 介于 $0$ 和 $x$ 之间，有 $e^c \leq M$。因此

$$|R_n(x)| = \frac{e^c |x|^{n+1}}{(n+1)!} \leq \frac{M |x|^{n+1}}{(n+1)!}.$$

对任意固定的 $x$，$\dfrac{|x|^{n+1}}{(n+1)!} \to 0$ 当 $n \to \infty$（因为阶乘增长快于任何指数）。因此

$$\lim_{n \to \infty} R_n(x) = 0, \qquad \forall x \in \mathbb{R}.$$

故

$$e^x = \sum_{k=0}^{\infty} \frac{x^k}{k!}, \qquad \forall x \in \mathbb{R}.$$

**关键步骤解析**: 证明 Taylor 级数收敛到原函数的核心，是证明余项 $R_n(x) \to 0$（$n \to \infty$）。对于 $e^x$，指数函数的各阶导数有统一上界（在任意有界区间上），这使得 Lagrange 余项的分析变得直接。

---

### 例题 6.2（$\sin x$ 与 $\cos x$ 的 Taylor 展开）

**题目**: 求 $\sin x$ 和 $\cos x$ 在 $x_0 = 0$ 处的 Taylor 展开，给出 Lagrange 余项估计，并证明其 Taylor 级数在 $\mathbb{R}$ 上收敛。

**解答**:

**对于 $\sin x$**:

导数循环：$\sin' x = \cos x$，$\sin'' x = -\sin x$，$\sin''' x = -\cos x$，$\sin^{(4)} x = \sin x$，周期为 4。

在 $x = 0$ 处：$\sin 0 = 0$，$\cos 0 = 1$，故

$$f^{(k)}(0) = \begin{cases} 0, & k = 0, 2, 4, \ldots \\ 1, & k = 1, 5, 9, \ldots \quad (k \equiv 1 \pmod 4) \\ -1, & k = 3, 7, 11, \ldots \quad (k \equiv 3 \pmod 4) \end{cases}$$

Taylor 多项式（仅奇次项非零）：

$$P_{2n+1}(x) = x - \frac{x^3}{3!} + \frac{x^5}{5!} - \cdots + (-1)^n \frac{x^{2n+1}}{(2n+1)!}.$$

Lagrange 余项：

$$R_{2n+1}(x) = \frac{\sin^{(2n+2)}(c)}{(2n+2)!} x^{2n+2} = \frac{\pm \sin c}{(2n+2)!} x^{2n+2} \text{ 或 } \frac{\pm \cos c}{(2n+2)!} x^{2n+2}.$$

无论哪种情况，$|\sin^{(2n+2)}(c)| \leq 1$。故

$$|R_{2n+1}(x)| \leq \frac{|x|^{2n+2}}{(2n+2)!} \to 0 \quad (n \to \infty).$$

因此

$$\sin x = \sum_{n=0}^{\infty} (-1)^n \frac{x^{2n+1}}{(2n+1)!}, \qquad \forall x \in \mathbb{R}.$$

**对于 $\cos x$**: 类似地，

$$\cos x = \sum_{n=0}^{\infty} (-1)^n \frac{x^{2n}}{(2n)!}, \qquad \forall x \in \mathbb{R}.$$

**关键步骤解析**: $\sin x$ 和 $\cos x$ 的所有阶导数都被 $[-1, 1]$ 一致有界，这使得余项估计异常简洁——不需要随区间变化的边界控制。这一性质是三角函数在分析学中特别"友好"的根本原因。

---

### 例题 6.3（$\ln(1+x)$ 的 Taylor 展开）

**题目**: 求 $f(x) = \ln(1+x)$ 在 $x_0 = 0$ 处的 $n$ 阶 Taylor 展开及 Lagrange 余项，确定 Taylor 级数的收敛区间，并证明在 $(-1, 1]$ 上级数收敛于 $f(x)$。

**解答**:

计算各阶导数：

$$f'(x) = \frac{1}{1+x}, \quad f''(x) = \frac{-1}{(1+x)^2}, \quad f'''(x) = \frac{2}{(1+x)^3}, \quad f^{(k)}(x) = \frac{(-1)^{k-1}(k-1)!}{(1+x)^k} \quad (k \geq 1).$$

在 $x = 0$ 处：$f(0) = 0$，$f^{(k)}(0) = (-1)^{k-1}(k-1)!$（$k \geq 1$）。

$n$ 阶 Taylor 多项式：

$$P_n(x) = \sum_{k=1}^{n} \frac{(-1)^{k-1}(k-1)!}{k!} x^k = \sum_{k=1}^{n} \frac{(-1)^{k-1}}{k} x^k = x - \frac{x^2}{2} + \frac{x^3}{3} - \cdots + \frac{(-1)^{n-1}x^n}{n}.$$

Lagrange 余项（$n \geq 1$）：

$$R_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1} = \frac{(-1)^n n!}{(n+1)!(1+c)^{n+1}} x^{n+1} = \frac{(-1)^n}{n+1} \cdot \frac{x^{n+1}}{(1+c)^{n+1}},$$

其中 $c$ 严格介于 $0$ 与 $x$ 之间。

**收敛区间分析**:

对 $x \in (-1, 1]$ 分情形讨论：

**情形一：$x \in [0, 1]$。**

此时 $c \in (0, x) \subseteq [0, 1]$，故 $1 + c \geq 1$。因此

$$|R_n(x)| = \frac{1}{n+1} \cdot \frac{x^{n+1}}{(1+c)^{n+1}} \leq \frac{x^{n+1}}{n+1} \leq \frac{1}{n+1} \to 0.$$

注意 $x = 1$ 时 $|R_n(1)| \leq \dfrac{1}{n+1} \to 0$，级数在 $x = 1$ 处收敛于 $\ln 2$。

**情形二：$x \in (-1, 0)$。**

此时 $c \in (x, 0)$，故 $1 + c \in (1+x, 1)$。由于 $x < 0$，有 $0 < 1 + x < 1 + c < 1$。注意 $x^{n+1}$ 的符号交替，我们取绝对值：

$$|R_n(x)| = \frac{1}{n+1} \cdot \frac{|x|^{n+1}}{(1+c)^{n+1}}.$$

由于 $1 + c > 1 + x > 0$，且 $|x| < 1$，有

$$\frac{|x|}{1+c} < \frac{|x|}{1+x}.$$

（这里要小心：$x \in (-1, 0)$ 时 $1+x \in (0, 1)$，而 $1+c > 1+x$，所以 $|x|/(1+c) < |x|/(1+x)$。）

因为 $|x| < 1$，令 $r = |x| < 1$，则

$$|R_n(x)| \leq \frac{1}{n+1} \cdot \left(\frac{r}{1+x}\right)^{n+1}.$$

实际上更直接的估计：由于 $c > x$，$1+c > 1+x > 0$，且 $x \in (-1, 0)$ 时 $|x|/(1+x) = -x/(1+x) < 1$（因为 $-x < 1+x$，即 $x > -1/2$ 时显然；对 $x \in (-1, -1/2]$，可直接验证 $|R_n(x)| \to 0$）。

更简洁的方法：对 $x \in (-1, 0)$，用积分余项或 Cauchy 余项形式更为方便。但用 Lagrange 余项也可以：注意到 $c \in (x, 0)$，故 $1/(1+c) < 1/(1+x)$，从而

$$|R_n(x)| = \frac{1}{n+1} \left|\frac{x}{1+c}\right|^{n+1} < \frac{1}{n+1} \left(\frac{|x|}{1+x}\right)^{n+1}.$$

当 $x \in (-1, 0)$ 时，$|x|/(1+x) = -x/(1+x) = 1 - 1/(1+x)$。因为 $1+x \in (0, 1)$，这个比值可以大于 1（例如 $x = -0.8$ 时比值为 $4$），所以上述直接估计不够。

**修正估计**: 对 $x \in (-1, 0)$，改用**Cauchy 余项**（Taylor 定理的另一形式）：

$$R_n(x) = \frac{f^{(n+1)}(c)}{n!}(x - c)^n x = \frac{(-1)^n}{(1+c)^{n+1}}(x-c)^n x.$$

选取 $c = 0$（Cauchy 余项允许 $c$ 在 $(0, x)$ 中选取，对 $x < 0$ 即 $c \in (x, 0)$；取 $c = 0$ 是边界但可逼近），得

$$|R_n(x)| \leq \frac{|x|^{n+1}}{1 - |x|} \to 0 \quad (n \to \infty)$$

当 $|x| < 1$。更严格地，利用 Abel 极限定理或直接证明对 $x \in (-1, 0]$，$R_n(x) \to 0$。

实际上，标准教材中的处理是：对 $x \in (-1, 1]$，通过证明级数在 $(-1, 1]$ 上收敛，并结合 Taylor 定理的余项分析，确认级数和等于 $\ln(1+x)$。对 $x \in (-1, 0)$，利用交错级数估计或上述 Lagrange 余项的精细控制均可得 $R_n(x) \to 0$。

**关键结论**:

$$\ln(1+x) = \sum_{k=1}^{\infty} \frac{(-1)^{k-1}}{k} x^k = x - \frac{x^2}{2} + \frac{x^3}{3} - \cdots, \qquad x \in (-1, 1].$$

在 $x = -1$ 处级数发散（调和级数），在 $x = 1$ 处条件收敛（交错调和级数）。

---

## 四、常见误区与纠正

### 误区 6.1: "Taylor 级数收敛则必收敛到原函数"

**错误观点**: 许多学生认为，只要函数 $f$ 无穷阶可导，且其 Taylor 级数在某区间内收敛，那么该级数就一定收敛到 $f(x)$ 本身。这是将 Taylor **定理**（有限阶，精确等式）与 Taylor **级数**（无穷级数，涉及收敛性）混为一谈的典型错误。

**反例**: 经典的反例是

$$f(x) = \begin{cases} e^{-1/x^2}, & x \neq 0 \\ 0, & x = 0 \end{cases}$$

**分析**:

1. **$f$ 在 $\mathbb{R}$ 上无穷阶可导**: 对 $x \neq 0$，$f(x) = e^{-1/x^2}$ 是初等函数的复合，显然光滑。在 $x = 0$ 处，可以归纳证明对所有 $n \geq 0$，$f^{(n)}(0) = 0$。

   归纳基础：$f(0) = 0$。

   归纳步骤：假设 $f^{(n)}(0) = 0$。对 $h \neq 0$，

   $$\frac{f^{(n)}(h) - f^{(n)}(0)}{h} = \frac{f^{(n)}(h)}{h}.$$

   通过归纳可以证明，对 $x \neq 0$，$f^{(n)}(x)$ 具有形式 $P_n(1/x) e^{-1/x^2}$，其中 $P_n$ 是某个多项式。当 $x \to 0$ 时，$1/x \to \infty$，但 $e^{-1/x^2}$ 的衰减速度比任何多项式增长都快，因此 $f^{(n)}(x) \to 0$（$x \to 0$）。故 $f^{(n+1)}(0) = 0$。

2. **Taylor 级数恒为零**: 由于 $f^{(k)}(0) = 0$ 对所有 $k \geq 0$ 成立，$f$ 在 $x_0 = 0$ 处的 Taylor 级数为

   $$\sum_{k=0}^{\infty} \frac{0}{k!} x^k = 0.$$

   该级数当然收敛（对任意 $x$，和为零）。

3. **级数不收敛到 $f(x)$**: 但对任意 $x \neq 0$，$f(x) = e^{-1/x^2} > 0 \neq 0$。因此 Taylor 级数的和函数为 $S(x) = 0$，与原函数 $f(x)$ 仅在 $x = 0$ 处相等。

> **为什么错**: Taylor 级数收敛到 $f(x)$ 需要**额外条件**——余项 $R_n(x) \to 0$（$n \to \infty$）。无穷阶可导只保证 Taylor 级数**存在**，不保证其和等于原函数。Lagrange 余项或 Cauchy 余项的分析是连接 Taylor 多项式与 Taylor 级数的不可或缺的桥梁。

> **正确理解**:
>
> - $f$ 无穷阶可导 $\implies$ Taylor 级数**存在**（形式幂级数）。
> - Taylor 级数在某点 $x$ 处收敛 $\not\!\implies$ 收敛到 $f(x)$。
> - 若要 Taylor 级数收敛到 $f(x)$，必须验证 $R_n(x) \to 0$。
> - **解析函数**（analytic function）的定义：$f$ 在某点处解析，当且仅当 $f$ 在该点的某邻域内等于其 Taylor 级数的和。并非所有光滑函数都是解析函数。

---

## 五、思想方法提炼

**本章核心思想**:

1. **局部到全局的多项式逼近**: Taylor 定理的核心思想是：函数的各阶导数在一点处的值，蕴含了该函数在该点附近的全部局部行为。零阶 Taylor 多项式是常数逼近（切点），一阶是线性逼近（切线），二阶是二次逼近（密切抛物线），依此类推。阶数越高，逼近的精度越高，误差随 $(x - x_0)^{n+1}$ 衰减。

2. **余项分析是收敛性的钥匙**: 从有限阶 Taylor 公式（定理）到无穷 Taylor 级数，关键的跨越在于余项是否趋于零。分析学中大量的收敛性证明——无论是数值方法、渐近分析还是特殊函数论——都归结为对余项的精细估计。

3. **解析与非解析的边界**: $e^{-1/x^2}$ 反例揭示了一个深刻的数学事实：**光滑性不等于解析性**。在复分析中，这个差异更为剧烈：复可导（全纯）即解析，但实可导再多阶也不保证解析。这一差异是实分析与复分析的根本分野之一。

**与后续章节的联系**:

- **幂级数理论**: Taylor 级数是幂级数的特例。幂级数的收敛半径、逐项求导与积分等性质，为 Taylor 展开的运算提供了系统框架。
- **Fourier 分析**: Taylor 展开用多项式基 $\{x^k\}$ 逼近函数，Fourier 展开用三角函数基 $\{e^{ikx}\}$ 逼近函数。两者都是"用简单函数的线性组合逼近复杂函数"这一普遍思想的体现。
- **数值分析**: Newton 法、数值积分、微分方程的级数解法等，都直接依赖于 Taylor 展开和余项估计。
- **渐近分析**: 大参数或小参数的渐近展开（如 Stirling 公式、Laplace 方法）本质上是广义的 Taylor 型展开。

---

## 六、习题

### 习题 6.1

**题目**: 求 $f(x) = \arctan x$ 在 $x_0 = 0$ 处的 Taylor 展开，确定收敛区间，并证明在 $[-1, 1]$ 上级数收敛于 $\arctan x$。

**提示**: 先求 $(\arctan x)' = \dfrac{1}{1+x^2}$ 的几何级数展开，再逐项积分。

**解答**:

对 $|x| < 1$，

$$\frac{1}{1+x^2} = \sum_{k=0}^{\infty} (-1)^k x^{2k}.$$

对 $|t| < 1$，逐项积分：

$$\arctan x = \int_0^x \frac{dt}{1+t^2} = \sum_{k=0}^{\infty} (-1)^k \int_0^x t^{2k} dt = \sum_{k=0}^{\infty} \frac{(-1)^k}{2k+1} x^{2k+1}.$$

在 $x = \pm 1$ 处，级数为交错级数，由 Leibniz 判别法收敛。利用 Abel 定理，级数在 $[-1, 1]$ 上收敛于 $\arctan x$。特别地，

$$\frac{\pi}{4} = \arctan 1 = 1 - \frac{1}{3} + \frac{1}{5} - \frac{1}{7} + \cdots.$$

---

### 习题 6.2

**题目**: 用 Taylor 展开证明 $e$ 是无理数。

**提示**: 假设 $e = p/q$ 为有理数，写出 $e$ 在 $x_0 = 0$ 处的 $n$ 阶 Taylor 展开（$n \geq q$），两边乘 $n!$，分析整数性与余项的矛盾。

**解答**:

假设 $e = p/q$，其中 $p, q \in \mathbb{N}^+$，$\gcd(p, q) = 1$。取 $n \geq q$。

$$e = \sum_{k=0}^{n} \frac{1}{k!} + R_n(1), \qquad R_n(1) = \frac{e^c}{(n+1)!}, \quad c \in (0, 1).$$

两边乘 $n!$：

$$n! \cdot e = \sum_{k=0}^{n} \frac{n!}{k!} + n! \cdot R_n(1).$$

左边 $n! \cdot e = n! \cdot p/q$。由于 $n \geq q$，$n!/q$ 为整数，故左边为整数。

右边第一项 $\sum_{k=0}^{n} \dfrac{n!}{k!}$ 显然是整数（$k \leq n$ 时 $n!/k!$ 为整数）。

因此 $n! \cdot R_n(1)$ 必须是整数。但

$$n! \cdot R_n(1) = \frac{n! \cdot e^c}{(n+1)!} = \frac{e^c}{n+1}.$$

由于 $0 < c < 1$，$1 < e^c < e < 3$。故

$$0 < n! \cdot R_n(1) = \frac{e^c}{n+1} < \frac{3}{n+1}.$$

取 $n \geq 2$，则 $0 < n! \cdot R_n(1) < 1$。但 $n! \cdot R_n(1)$ 被论证为整数，矛盾。

故 $e$ 不是有理数。$\square$

---

### 习题 6.3

**题目**: 设 $f$ 在 $[a, b]$ 上二阶可导，$f'(a) = f'(b) = 0$。证明存在 $c \in (a, b)$ 使得

$$|f''(c)| \geq \frac{4}{(b-a)^2} |f(b) - f(a)|.$$

**提示**: 在 $x_0 = a$ 和 $x_0 = b$ 处分别写出一阶 Taylor 展开，令 $x = (a+b)/2$，联立两个等式消去 $f((a+b)/2)$。

**解答**:

令 $m = (a+b)/2$，$h = (b-a)/2$。

在 $a$ 处展开到二阶，取 $x = m = a + h$：

$$f(m) = f(a) + f'(a) \cdot h + \frac{f''(c_1)}{2} h^2 = f(a) + \frac{f''(c_1)}{2} h^2, \quad c_1 \in (a, m).$$

在 $b$ 处展开到二阶，取 $x = m = b - h$：

$$f(m) = f(b) + f'(b) \cdot (-h) + \frac{f''(c_2)}{2} h^2 = f(b) + \frac{f''(c_2)}{2} h^2, \quad c_2 \in (m, b).$$

两式相减：

$$0 = f(a) - f(b) + \frac{h^2}{2}\big(f''(c_1) - f''(c_2)\big).$$

故

$$f(b) - f(a) = \frac{h^2}{2}\big(f''(c_1) - f''(c_2)\big).$$

取绝对值：

$$|f(b) - f(a)| \leq \frac{h^2}{2}\big(|f''(c_1)| + |f''(c_2)|\big) \leq h^2 \max\{|f''(c_1)|, |f''(c_2)|\}.$$

令 $c$ 为 $c_1, c_2$ 中使 $|f''|$ 较大的那个，则

$$|f(b) - f(a)| \leq h^2 |f''(c)| = \frac{(b-a)^2}{4} |f''(c)|.$$

整理得

$$|f''(c)| \geq \frac{4}{(b-a)^2} |f(b) - f(a)|.$$

$\square$

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
