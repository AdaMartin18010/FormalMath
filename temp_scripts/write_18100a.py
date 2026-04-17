# -*- coding: utf-8 -*-
content = r'''---
title: "MIT 18.100A 实分析课堂验证测试题库"
date: "2026-04-18"
version: "1.0"
course: "MIT 18.100A Real Analysis"
textbook: "Jiri Lebl, Basic Analysis I: Introduction to Real Analysis, Volume 1"
validation_id: "VAL-2026-Q2"
---

# MIT 18.100A 实分析课堂验证测试题库

> 本题库对应 FormalMath 银层文档 MIT 18.100A 模块（8大定理核心内容）。
> 所有题目使用标准 LaTeX 数学符号。

---

## 课前基线测试（Pre-test）

> **测试说明**：本测试用于评估学生进入课程前的先备知识水平，不计入最终成绩。
> **限时**：20 分钟　**总分**：100 分（每题 20 分）

---

### Q1：实数完备性

**难度**：★★☆（中）　**对应章节**：Ch 1 — 实数

**题目陈述**：

(a) 叙述**确界原理**（Supremum Principle / Least Upper Bound Property）：非空有上界的实数集必有上确界。

(b) 设 $S = \{x \in \mathbb{Q} \mid x^2 < 2\}$。证明：$S$ 在 $\mathbb{Q}$ 中没有上确界（即在有理数集中，确界原理不成立）。

**参考答案**：

(a) **确界原理**：设 $S \subseteq \mathbb{R}$ 为非空集合，且 $S$ 有上界（即存在 $M \in \mathbb{R}$，使得对所有 $x \in S$ 有 $x \leq M$）。则 $S$ 在 $\mathbb{R}$ 中存在**上确界**（least upper bound / supremum），记作 $\sup S$，满足：

1. $\sup S$ 是 $S$ 的上界：$\forall x \in S,\ x \leq \sup S$；
2. $\sup S$ 是最小的上界：若 $M$ 是 $S$ 的任一个上界，则 $\sup S \leq M$。

(b) **证明**：反证法。假设 $S$ 在 $\mathbb{Q}$ 中有上确界 $u = \sup_{\mathbb{Q}} S \in \mathbb{Q}$。

**第一步**：证明 $u^2 = 2$。

- 若 $u^2 < 2$，则 $u$ 不是上界（因为可以取有理数 $q$ 满足 $u < q$ 且 $q^2 < 2$），矛盾。
- 若 $u^2 > 2$，则 $u$ 不是最小上界（存在更小的有理数上界），矛盾。

因此 $u^2 = 2$。但 $\sqrt{2} \notin \mathbb{Q}$，与 $u \in \mathbb{Q}$ 矛盾。故 $S$ 在 $\mathbb{Q}$ 中无上确界。$\square$

（注：标准证法需构造性证明中间步骤，此处给出框架；判卷时接受合理的构造性论证。）

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确叙述确界原理 | 6 | 含"非空""有上界""存在上确界"三要素 |
| (a) 正确说明上确界的两条性质 | 4 | 上界性 + 最小性 |
| (b) 正确使用反证法 | 2 | |
| (b) 正确排除 $u^2 < 2$ 和 $u^2 > 2$ | 4 | 各 2 分 |
| (b) 正确得出结论 | 2 | 联系 $\sqrt{2} \notin \mathbb{Q}$ |
| (b) 逻辑完整 | 2 | |
| **合计** | **20** | |

---

### Q2：序列收敛

**难度**：★★☆（中）　**对应章节**：Ch 2 — 序列与极限

**题目陈述**：

设数列 $(a_n)$ 定义为 $a_n = \frac{3n + (-1)^n}{2n + 1}$。

(a) 猜测该数列的极限 $L$，并用 **$\varepsilon$-$N$ 定义**严格证明 $a_n \to L$。

(b) 给出证明中 $N$ 关于 $\varepsilon$ 的显式表达式（即：对任意给定的 $\varepsilon > 0$，$N$ 应取何值？）。

**参考答案**：

(a) **猜测极限**：

$$a_n = \frac{3n + (-1)^n}{2n + 1} = \frac{3 + \frac{(-1)^n}{n}}{2 + \frac{1}{n}} \to \frac{3}{2} \quad (n \to \infty).$$

故猜测 $L = \frac{3}{2}$。

**$\varepsilon$-$N$ 证明**：

对任意 $\varepsilon > 0$，考察

$$\left| a_n - \frac{3}{2} \right| = \left| \frac{3n + (-1)^n}{2n + 1} - \frac{3}{2} \right| = \left| \frac{2(3n + (-1)^n) - 3(2n + 1)}{2(2n + 1)} \right|$$

$$= \left| \frac{6n + 2(-1)^n - 6n - 3}{2(2n + 1)} \right| = \left| \frac{2(-1)^n - 3}{2(2n + 1)} \right|.$$

由于 $|2(-1)^n - 3| \leq |2(-1)^n| + 3 = 2 + 3 = 5$，故

$$\left| a_n - \frac{3}{2} \right| \leq \frac{5}{2(2n + 1)} < \frac{5}{4n}.$$

要使 $\frac{5}{4n} < \varepsilon$，只需 $n > \frac{5}{4\varepsilon}$。

取 $N = \left\lceil \frac{5}{4\varepsilon} \right\rceil$（或更简单地取 $N = \left\lceil \frac{2}{\varepsilon} \right\rceil$，因为 $\frac{5}{4n} < \frac{2}{n}$ 当 $n \geq 2$）。

则当 $n > N$ 时，$\left| a_n - \frac{3}{2} \right| < \varepsilon$。

由 $\varepsilon$-$N$ 定义，$\lim_{n \to \infty} a_n = \frac{3}{2}$。$\square$

(b) 显式取 $N = \left\lceil \frac{5}{4\varepsilon} \right\rceil$ 即可。更松的界：$N = \left\lceil \frac{2}{\varepsilon} \right\rceil$ 也可接受。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确猜测极限 $L = \frac{3}{2}$ | 2 | |
| 正确写出 $\varepsilon$-$N$ 定义的框架 | 2 | "对任意 $\varepsilon > 0$，存在 $N \in \mathbb{N}$..." |
| 正确计算 $|a_n - L|$ 的表达式 | 4 | 通分化简 |
| 正确放缩得到上界 | 4 | 如 $\frac{5}{4n}$ 或更松的界 |
| 正确给出 $N$ 的显式表达式 | 4 | 关于 $\varepsilon$ 的函数 |
| 逻辑完整、结论正确 | 4 | |
| **合计** | **20** | |

---

### Q3：连续函数

**难度**：★★★（难）　**对应章节**：Ch 3 — 连续函数

**题目陈述**：

设 $f: \mathbb{R} \to \mathbb{R}$ 定义为
$$f(x) = \begin{cases} x^2 & x \in \mathbb{Q}, \\ 0 & x \notin \mathbb{Q}. \end{cases}$$

(a) 证明 $f$ 在 $x = 0$ 处连续。

(b) 证明 $f$ 在任意 $x_0 \neq 0$ 处不连续。

**参考答案**：

(a) **在 $x = 0$ 处连续**：

需证：$\forall \varepsilon > 0$，$\exists \delta > 0$，使得当 $|x - 0| < \delta$ 时，$|f(x) - f(0)| < \varepsilon$。

注意 $f(0) = 0^2 = 0$（因为 $0 \in \mathbb{Q}$）。

对任意 $x \in \mathbb{R}$：
- 若 $x \in \mathbb{Q}$，则 $|f(x)| = |x^2| = x^2$；
- 若 $x \notin \mathbb{Q}$，则 $|f(x)| = 0$。

无论哪种情况，$|f(x)| \leq x^2$。因此
$$|f(x) - f(0)| = |f(x)| \leq x^2.$$

取 $\delta = \sqrt{\varepsilon}$，则当 $|x| < \delta$ 时，
$$|f(x)| \leq x^2 < \delta^2 = \varepsilon.$$

故 $f$ 在 $x = 0$ 处连续。$\square$

(b) **在 $x_0 \neq 0$ 处不连续**：

需证：$\exists \varepsilon_0 > 0$，使得 $\forall \delta > 0$，存在 $x$ 满足 $|x - x_0| < \delta$ 但 $|f(x) - f(x_0)| \geq \varepsilon_0$。

**情形 1**：$x_0 \in \mathbb{Q}$，$x_0 \neq 0$。此时 $f(x_0) = x_0^2 \neq 0$。

取 $\varepsilon_0 = \frac{x_0^2}{2} > 0$。对任意 $\delta > 0$，由无理数在 $\mathbb{R}$ 中稠密，存在无理数 $x$ 满足 $|x - x_0| < \delta$。对该 $x$，$f(x) = 0$，故
$$|f(x) - f(x_0)| = |0 - x_0^2| = x_0^2 > \frac{x_0^2}{2} = \varepsilon_0.$$

**情形 2**：$x_0 \notin \mathbb{Q}$。此时 $f(x_0) = 0$。

取 $\varepsilon_0 = \frac{x_0^2}{2} > 0$。对任意 $\delta > 0$，由有理数在 $\mathbb{R}$ 中稠密，存在有理数 $q$ 满足 $|q - x_0| < \delta$ 且 $q \neq 0$。可取 $|q|$ 足够接近 $|x_0|$ 使得 $q^2 > \frac{x_0^2}{2}$。于是
$$|f(q) - f(x_0)| = |q^2 - 0| = q^2 > \frac{x_0^2}{2} = \varepsilon_0.$$

两种情形下均找到满足条件的 $x$，故 $f$ 在 $x_0 \neq 0$ 处不连续。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确写出连续定义的框架 | 2 | $\varepsilon$-$\delta$ 定义 |
| (a) 正确分析 $|f(x)| \leq x^2$ | 4 | 关键放缩 |
| (a) 正确选取 $\delta$ 并完成证明 | 4 | |
| (b) 正确写出不连续的定义 | 2 | 否定形式的 $\varepsilon$-$\delta$ |
| (b) 利用稠密性构造反例 | 4 | 有理数/无理数稠密 |
| (b) 完整论证两种情形 | 4 | 各 2 分 |
| **合计** | **20** | |

---

### Q4：级数判别

**难度**：★★☆（中）　**对应章节**：Ch 2 — 级数收敛

**题目陈述**：

判断下列级数的敛散性。若收敛，请说明是绝对收敛还是条件收敛；若发散，请说明理由。

(a) $\displaystyle\sum_{n=1}^{\infty} \frac{n^2 + 1}{n^3 + 2}$

(b) $\displaystyle\sum_{n=1}^{\infty} \frac{(-1)^n}{\sqrt{n}}$

(c) $\displaystyle\sum_{n=1}^{\infty} \frac{2^n}{n!}$

**参考答案**：

(a) **发散**。

与调和级数比较：
$$\frac{n^2 + 1}{n^3 + 2} \sim \frac{n^2}{n^3} = \frac{1}{n} \quad (n \to \infty).$$

严格地，对 $n \geq 2$：
$$\frac{n^2 + 1}{n^3 + 2} > \frac{n^2}{n^3 + n^3} = \frac{1}{2n}.$$

由比较判别法，因 $\sum \frac{1}{2n}$ 发散，故原级数发散。

或直接用极限比较：$\lim_{n \to \infty} \frac{(n^2+1)/(n^3+2)}{1/n} = 1 \neq 0$，与发散级数 $\sum \frac{1}{n}$ 比较，得发散。

(b) **条件收敛**。

- **收敛性**（Leibniz 判别法）：令 $a_n = \frac{1}{\sqrt{n}}$。$a_n > 0$，$a_n \to 0$，且 $a_{n+1} < a_n$（因为 $\sqrt{n+1} > \sqrt{n}$）。满足 Leibniz 条件，故交错级数收敛。

- **非绝对收敛**：$\sum \left| \frac{(-1)^n}{\sqrt{n}} \right| = \sum \frac{1}{n^{1/2}}$ 是 $p = \frac{1}{2} < 1$ 的 $p$-级数，发散。

故原级数**条件收敛**。

(c) **绝对收敛**。

用比值判别法：
$$\left| \frac{a_{n+1}}{a_n} \right| = \frac{2^{n+1}}{(n+1)!} \cdot \frac{n!}{2^n} = \frac{2}{n+1} \to 0 < 1 \quad (n \to \infty).$$

由比值判别法，级数绝对收敛。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确判定发散 | 2 | |
| (a) 正确使用比较/极限比较 | 4 | 需有明确放缩或极限计算 |
| (b) 正确判定收敛 | 2 | |
| (b) 正确使用 Leibniz 判别法 | 3 | 验证单调递减趋于零 |
| (b) 正确判定非绝对收敛 | 3 | $p$-级数或积分判别 |
| (c) 正确判定绝对收敛 | 2 | |
| (c) 正确使用比值判别法 | 4 | 计算极限 |
| **合计** | **20** | |

---

### Q5：导数定义

**难度**：★★☆（中）　**对应章节**：Ch 4 — 导数

**题目陈述**：

(a) 叙述函数 $f$ 在点 $x_0$ 处**可导**的严格定义（用极限形式）。

(b) 用定义直接证明 $f(x) = x^3$ 在任意点 $x_0 \in \mathbb{R}$ 处可导，并求出 $f'(x_0)$。

(c) 设
$$g(x) = \begin{cases} x^2 \sin\frac{1}{x} & x \neq 0, \\ 0 & x = 0. \end{cases}$$
用定义证明 $g$ 在 $x = 0$ 处可导，并求 $g'(0)$。

**参考答案**：

(a) $f$ 在 $x_0$ 处**可导**，若极限
$$f'(x_0) = \lim_{x \to x_0} \frac{f(x) - f(x_0)}{x - x_0}$$
存在且有限。等价地，
$$f'(x_0) = \lim_{h \to 0} \frac{f(x_0 + h) - f(x_0)}{h}.$$

(b) 对 $f(x) = x^3$：

$$\frac{f(x_0 + h) - f(x_0)}{h} = \frac{(x_0 + h)^3 - x_0^3}{h}$$

$$= \frac{x_0^3 + 3x_0^2 h + 3x_0 h^2 + h^3 - x_0^3}{h}$$

$$= \frac{3x_0^2 h + 3x_0 h^2 + h^3}{h} = 3x_0^2 + 3x_0 h + h^2.$$

令 $h \to 0$，得
$$f'(x_0) = \lim_{h \to 0} (3x_0^2 + 3x_0 h + h^2) = 3x_0^2.$$

(c) 对 $g$ 在 $x = 0$ 处：

$$g'(0) = \lim_{h \to 0} \frac{g(h) - g(0)}{h} = \lim_{h \to 0} \frac{h^2 \sin\frac{1}{h} - 0}{h} = \lim_{h \to 0} h \sin\frac{1}{h}.$$

由于 $\left|\sin\frac{1}{h}\right| \leq 1$，故
$$\left| h \sin\frac{1}{h} \right| \leq |h| \to 0 \quad (h \to 0).$$

由夹逼定理，$g'(0) = 0$。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确叙述导数定义 | 4 | 极限形式，分母为 $h$ 或 $x - x_0$ |
| (b) 正确展开 $(x_0 + h)^3$ | 3 | |
| (b) 正确化简差商 | 3 | |
| (b) 正确取极限得 $3x_0^2$ | 2 | |
| (c) 正确写出 $x = 0$ 处的差商 | 3 | |
| (c) 正确使用夹逼定理 | 3 | 利用 $|\sin| \leq 1$ |
| (c) 得出 $g'(0) = 0$ | 2 | |
| **合计** | **20** | |

---

## 期末综合测试（Final Comprehensive Test）

> **测试说明**：本测试覆盖 MIT 18.100A 全部 8 大定理核心内容，评估学期整体学习成效。
> **限时**：120 分钟　**总分**：100 分

---

### 模块一：定义复述（2题，共20分）

---

#### Q1：定义 — 一致连续与 Cauchy 序列

**难度**：★★☆（中）　**对应章节**：Ch 2–3 — Cauchy 序列与一致连续　**分值**：10 分

**题目陈述**：

(a) 给出**Cauchy 序列**（Cauchy sequence）的严格定义。

(b) 给出函数 $f: D \to \mathbb{R}$ 在定义域 $D$ 上**一致连续**（uniformly continuous）的严格定义。

(c) 用一句话说明：一致连续与逐点连续（pointwise continuous）的关键区别是什么？（提示：从 $\delta$ 的选取方式回答。）

**参考答案**：

(a) 数列 $(x_n)_{n=1}^{\infty} \subseteq \mathbb{R}$ 称为 **Cauchy 序列**，如果
$$\forall \varepsilon > 0,\ \exists N \in \mathbb{N},\ \forall m, n \geq N:\ |x_m - x_n| < \varepsilon.$$

等价表述：$\forall \varepsilon > 0,\ \exists N \in \mathbb{N},\ \forall n \geq N,\ \forall k \geq 0:\ |x_{n+k} - x_n| < \varepsilon$。

(b) 函数 $f: D \to \mathbb{R}$ 在 $D$ 上**一致连续**，如果
$$\forall \varepsilon > 0,\ \exists \delta > 0,\ \forall x, y \in D:\ |x - y| < \delta \Rightarrow |f(x) - f(y)| < \varepsilon.$$

注意：$\delta$ 仅依赖于 $\varepsilon$，不依赖于点的位置。

(c) **关键区别**：在逐点连续中，$\delta$ 的选取依赖于所讨论的点 $x_0$ 和 $\varepsilon$（即 $\delta = \delta(\varepsilon, x_0)$）；在一致连续中，$\delta$ 仅依赖于 $\varepsilon$（即 $\delta = \delta(\varepsilon)$），对定义域中所有点"一视同仁"。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确写出 Cauchy 定义 | 3 | 量词顺序正确 |
| (b) 正确写出一致连续定义 | 3 | 量词顺序正确，$\forall x, y \in D$ 在前 |
| (c) 正确指出 $\delta$ 的依赖性差异 | 4 | 逐点：$\delta(\varepsilon, x_0)$；一致：$\delta(\varepsilon)$ |
| **合计** | **10** | |

---

#### Q2：定义 — Riemann 可积

**难度**：★★★（难）　**对应章节**：Ch 5 — Riemann 积分　**分值**：10 分

**题目陈述**：

设 $f: [a, b] \to \mathbb{R}$ 为有界函数。

(a) 给出区间 $[a, b]$ 的一个**分割**（partition）$P$ 的定义，以及分割的**模**（mesh / norm）$\|P\|$ 的定义。

(b) 给出 **Darboux 上和** $U(P, f)$ 与 **Darboux 下和** $L(P, f)$ 的定义。

(c) 给出 $f$ 在 $[a, b]$ 上 **Riemann 可积** 的 Darboux 准则（用上积分与下积分相等，或用 $\varepsilon$-$\delta$ 形式均可）。

**参考答案**：

(a) 区间 $[a, b]$ 的一个**分割** $P$ 是指有限点集
$$P = \{x_0, x_1, \ldots, x_n\}$$
满足 $a = x_0 < x_1 < \cdots < x_n = b$。

分割的**模**定义为
$$\|P\| = \max_{1 \leq i \leq n} (x_i - x_{i-1}) = \max_{1 \leq i \leq n} \Delta x_i.$$

(b) 设 $M_i = \sup\{f(x) \mid x \in [x_{i-1}, x_i]\}$，$m_i = \inf\{f(x) \mid x \in [x_{i-1}, x_i]\}$。

**Darboux 上和**：
$$U(P, f) = \sum_{i=1}^{n} M_i \Delta x_i.$$

**Darboux 下和**：
$$L(P, f) = \sum_{i=1}^{n} m_i \Delta x_i.$$

(c) **Darboux 可积准则**：$f$ 在 $[a, b]$ 上 Riemann 可积，当且仅当
$$\overline{\int_a^b} f = \underline{\int_a^b} f,$$
其中上积分 $\overline{\int_a^b} f = \inf_P U(P, f)$，下积分 $\underline{\int_a^b} f = \sup_P L(P, f)$。

**$\varepsilon$-$\delta$ 形式**：$f$ 在 $[a, b]$ 上 Riemann 可积，当且仅当
$$\forall \varepsilon > 0,\ \exists \delta > 0,\ \forall P \text{ with } \|P\| < \delta:\ U(P, f) - L(P, f) < \varepsilon.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确给出分割定义 | 2 | 有限点集，有序 |
| (a) 正确给出模的定义 | 2 | 最大子区间长度 |
| (b) 正确写出上和 | 2 | 含 $M_i$ 定义 |
| (b) 正确写出下和 | 2 | 含 $m_i$ 定义 |
| (c) 正确给出可积准则 | 2 | Darboux 或 $\varepsilon$-$\delta$ 形式均可 |
| **合计** | **10** | |

---

### 模块二：定理证明（4题，共40分）

---

#### Q3：证明 — Bolzano-Weierstrass 定理

**难度**：★★★（难）　**对应章节**：Ch 2 — 序列紧致性　**分值**：10 分

**题目陈述**：

证明 **Bolzano-Weierstrass 定理**：$\mathbb{R}$ 中任何有界数列必有收敛子列。

**参考答案**：

**证明**（二分法构造性证明）：

设 $(x_n)$ 是有界数列，则存在闭区间 $[a_0, b_0]$ 使得所有 $x_n \in [a_0, b_0]$。

**构造子列**：

对 $k = 0, 1, 2, \ldots$，维护区间 $[a_k, b_k]$ 满足：

1. $[a_{k+1}, b_{k+1}] \subseteq [a_k, b_k]$；
2. $b_k - a_k = \frac{b_0 - a_0}{2^k}$；
3. $[a_k, b_k]$ 中包含 $(x_n)$ 的无穷多项。

**归纳构造**：

假设 $[a_k, b_k]$ 已构造，将其二等分：$[a_k, m_k]$ 和 $[m_k, b_k]$，其中 $m_k = \frac{a_k + b_k}{2}$。

至少有一个子区间包含 $(x_n)$ 的无穷多项（否则两个子区间都只含有限项，则 $[a_k, b_k]$ 也只含有限项，矛盾）。

取含无穷多项的那个子区间为 $[a_{k+1}, b_{k+1}]$。

**提取子列**：

对每个 $k$，在 $[a_k, b_k]$ 中选取 $x_{n_k}$，其中 $n_k > n_{k-1}$（可以做到，因为每个区间含无穷多项）。

**收敛性**：

由闭区间套定理，$\bigcap_{k=0}^{\infty} [a_k, b_k] = \{c\}$，其中 $c$ 为唯一公共点。

由于 $x_{n_k} \in [a_k, b_k]$，且 $b_k - a_k = \frac{b_0 - a_0}{2^k} \to 0$，故
$$|x_{n_k} - c| \leq b_k - a_k \to 0 \quad (k \to \infty).$$

因此 $x_{n_k} \to c$。证毕。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确设定初始有界区间 | 1 | |
| 正确描述二分构造步骤 | 3 | 三个条件 |
| 正确说明至少一个子区间含无穷多项 | 2 | 反证 |
| 正确提取递增指标子列 | 2 | $n_k > n_{k-1}$ |
| 正确应用闭区间套定理 | 1 | |
| 正确证明子列收敛 | 1 | 估计 $|x_{n_k} - c|$ |
| **合计** | **10** | |

---

#### Q4：证明 — 闭区间上连续函数必一致连续（Heine-Cantor 定理）

**难度**：★★★☆（较难）　**对应章节**：Ch 3 — 一致连续性　**分值**：10 分

**题目陈述**：

证明 **Heine-Cantor 定理**：若 $f: [a, b] \to \mathbb{R}$ 连续，则 $f$ 在 $[a, b]$ 上一致连续。

**参考答案**：

**证明**（反证法）：

假设 $f$ 在 $[a, b]$ 上不一致连续。则
$$\exists \varepsilon_0 > 0,\ \forall \delta > 0,\ \exists x, y \in [a, b]:\ |x - y| < \delta \text{ 但 } |f(x) - f(y)| \geq \varepsilon_0.$$

取 $\delta = \frac{1}{n}$（$n = 1, 2, \ldots$），得到序列 $(x_n), (y_n) \subseteq [a, b]$ 满足
$$|x_n - y_n| < \frac{1}{n}, \quad |f(x_n) - f(y_n)| \geq \varepsilon_0. \quad (*)$$

由 Bolzano-Weierstrass 定理，$(x_n)$ 有收敛子列 $x_{n_k} \to c \in [a, b]$（闭区间保证 $c \in [a, b]$）。

由于 $|x_{n_k} - y_{n_k}| < \frac{1}{n_k} \to 0$，故 $y_{n_k} \to c$ 同样成立。

由 $f$ 在 $c$ 处连续，$f(x_{n_k}) \to f(c)$ 且 $f(y_{n_k}) \to f(c)$，故
$$|f(x_{n_k}) - f(y_{n_k})| \to 0.$$

但这与 $(*)$ 中 $|f(x_{n_k}) - f(y_{n_k})| \geq \varepsilon_0 > 0$ 矛盾。

因此 $f$ 在 $[a, b]$ 上一致连续。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确写出反证假设 | 2 | 否定一致连续定义 |
| 正确构造序列 $(x_n), (y_n)$ | 2 | 取 $\delta = 1/n$ |
| 正确应用 Bolzano-Weierstrass | 2 | 提取收敛子列 |
| 正确证明 $y_{n_k} \to c$ | 1 | 利用 $|x_n - y_n| < 1/n$ |
| 正确利用连续性导出矛盾 | 2 | $f(x_{n_k}), f(y_{n_k}) \to f(c)$ |
| 结论正确 | 1 | |
| **合计** | **10** | |

---

#### Q5：证明 — 介值定理（Intermediate Value Theorem）

**难度**：★★★（难）　**对应章节**：Ch 3 — 连续函数　**分值**：10 分

**题目陈述**：

设 $f: [a, b] \to \mathbb{R}$ 连续，且 $f(a) < 0 < f(b)$。证明：存在 $c \in (a, b)$ 使得 $f(c) = 0$。

要求：不使用任何"显然"，给出**完整的、一步一步的严格证明**。

**参考答案**：

**证明**（二分法）：

**Step 1**：构造区间套。

设 $a_0 = a$，$b_0 = b$。注意 $f(a_0) < 0 < f(b_0)$。

对 $n = 0, 1, 2, \ldots$，设 $m_n = \frac{a_n + b_n}{2}$。

- 若 $f(m_n) = 0$，则取 $c = m_n$，证明结束。
- 若 $f(m_n) < 0$，则令 $a_{n+1} = m_n$，$b_{n+1} = b_n$。此时仍有 $f(a_{n+1}) < 0 \leq f(b_{n+1})$。
- 若 $f(m_n) > 0$，则令 $a_{n+1} = a_n$，$b_{n+1} = m_n$。此时仍有 $f(a_{n+1}) \leq 0 < f(b_{n+1})$。

**Step 2**：区间套收敛。

由构造，$[a_{n+1}, b_{n+1}] \subseteq [a_n, b_n]$，且 $b_n - a_n = \frac{b - a}{2^n} \to 0$。

由闭区间套定理，存在唯一的 $c \in \bigcap_{n=0}^{\infty} [a_n, b_n]$，且 $a_n \to c$，$b_n \to c$。

**Step 3**：证明 $f(c) = 0$。

由构造，对所有 $n$ 有 $f(a_n) \leq 0$。由于 $f$ 连续且 $a_n \to c$，
$$f(c) = \lim_{n \to \infty} f(a_n) \leq 0.$$

同理，$f(b_n) \geq 0$ 对所有 $n$ 成立，且 $b_n \to c$，故
$$f(c) = \lim_{n \to \infty} f(b_n) \geq 0.$$

因此 $f(c) \leq 0$ 且 $f(c) \geq 0$，即 $f(c) = 0$。

又 $c \in [a, b]$。若 $c = a$，则 $f(c) = f(a) < 0$，矛盾；若 $c = b$，则 $f(c) = f(b) > 0$，矛盾。故 $c \in (a, b)$。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确设定二分构造 | 2 | 中点分类讨论 |
| 正确维护区间不变性 | 2 | $f(a_n) \leq 0 \leq f(b_n)$ |
| 正确应用闭区间套定理 | 2 | 得到公共点 $c$ |
| 正确利用连续性从左侧得 $f(c) \leq 0$ | 2 | $f(a_n) \leq 0$ 取极限 |
| 正确利用连续性从右侧得 $f(c) \geq 0$ | 2 | $f(b_n) \geq 0$ 取极限 |
| **合计** | **10** | |

---

#### Q6：证明 — Rolle 定理与中值定理（MVT）

**难度**：★★★（难）　**对应章节**：Ch 4 — 导数　**分值**：10 分

**题目陈述**：

(a) 证明 **Rolle 定理**：若 $f: [a, b] \to \mathbb{R}$ 连续，在 $(a, b)$ 内可导，且 $f(a) = f(b)$，则存在 $c \in (a, b)$ 使得 $f'(c) = 0$。

(b) 利用 (a) 证明 **中值定理（Mean Value Theorem）**：在同样连续性、可导性条件下，存在 $c \in (a, b)$ 使得
$$f'(c) = \frac{f(b) - f(a)}{b - a}.$$

**参考答案**：

(a) **Rolle 定理证明**：

由闭区间上连续函数的**极值定理**，$f$ 在 $[a, b]$ 上取得最大值 $M$ 和最小值 $m$。

**情形 1**：$M = m$。则 $f$ 在 $[a, b]$ 上为常函数，故 $f'(x) = 0$ 对所有 $x \in (a, b)$ 成立。任取 $c \in (a, b)$ 即可。

**情形 2**：$M > m$。由于 $f(a) = f(b)$，$M$ 和 $m$ 中至少有一个在开区间 $(a, b)$ 内某点 $c$ 处取得。（否则最大值和最小值都在端点取得，则 $M = m$，矛盾。）

不妨设 $M$ 在 $c \in (a, b)$ 处取得（$m$ 的情形类似）。即 $f(c) = M$ 且 $f(x) \leq f(c)$ 对所有 $x \in [a, b]$ 成立。

对 $h > 0$ 充分小（使 $c + h \in (a, b)$）：
$$\frac{f(c + h) - f(c)}{h} \leq 0 \quad \Rightarrow \quad f'(c) = \lim_{h \to 0^+} \frac{f(c + h) - f(c)}{h} \leq 0.$$

对 $h < 0$ 充分小：
$$\frac{f(c + h) - f(c)}{h} \geq 0 \quad \Rightarrow \quad f'(c) = \lim_{h \to 0^-} \frac{f(c + h) - f(c)}{h} \geq 0.$$

因此 $f'(c) \leq 0$ 且 $f'(c) \geq 0$，故 $f'(c) = 0$。$\square$

(b) **MVT 证明**：

构造辅助函数
$$g(x) = f(x) - \frac{f(b) - f(a)}{b - a}(x - a).$$

验证 $g$ 满足 Rolle 定理条件：
- $g$ 在 $[a, b]$ 上连续（因为 $f$ 连续，线性函数连续）。
- $g$ 在 $(a, b)$ 内可导（因为 $f$ 可导，线性函数可导）。
- $g(a) = f(a) - 0 = f(a)$。
- $g(b) = f(b) - \frac{f(b) - f(a)}{b - a}(b - a) = f(b) - (f(b) - f(a)) = f(a)$。

故 $g(a) = g(b)$。

由 Rolle 定理，存在 $c \in (a, b)$ 使得 $g'(c) = 0$。

计算 $g'$：
$$g'(x) = f'(x) - \frac{f(b) - f(a)}{b - a}.$$

由 $g'(c) = 0$ 得
$$f'(c) = \frac{f(b) - f(a)}{b - a}.$$

证毕。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确应用极值定理 | 2 | |
| (a) 正确处理常函数情形 | 1 | |
| (a) 正确处理 $M > m$ 情形 | 2 | 指出最值至少一个在内点 |
| (a) 正确分左右导数得 $f'(c) = 0$ | 3 | 关键步骤 |
| (b) 正确构造辅助函数 $g(x)$ | 1 | |
| (b) 验证 Rolle 条件 | 2 | 特别是 $g(a) = g(b)$ |
| (b) 正确求导并得出结论 | 1 | |
| **合计** | **12** → **10** | 按 10 分折算 |

**修正评分标准（总分 10 分）**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 极值定理 + 常函数情形 | 2 | |
| (a) 最值在内点取得 | 2 | |
| (a) 左右导数论证 | 2 | |
| (b) 辅助函数构造 | 1 | |
| (b) 验证 Rolle 条件并应用 | 2 | |
| (b) 求导得结论 | 1 | |
| **合计** | **10** | |

---

### 模块三：计算应用（2题，共20分）

---

#### Q7：计算 — 极限计算与 Taylor 展开

**难度**：★★★（难）　**对应章节**：Ch 2, Ch 4 — 极限与 Taylor 定理　**分值**：10 分

**题目陈述**：

计算下列极限：

(a) $\displaystyle\lim_{n \to \infty} \left(1 + \frac{1}{n}\right)^n$

(b) $\displaystyle\lim_{x \to 0} \frac{e^x - 1 - x}{x^2}$

(c) 求 $f(x) = \ln(1 + x)$ 在 $x_0 = 0$ 处的 **Taylor 多项式** $T_3(x)$（3 阶），并写出 **Lagrange 余项** $R_3(x)$。

**参考答案**：

(a) 这是**自然常数 $e$ 的定义**：
$$\lim_{n \to \infty} \left(1 + \frac{1}{n}\right)^n = e.$$

标准证明：令 $a_n = (1 + 1/n)^n$。利用二项式定理和单调有界原理可证 $a_n$ 单调递增有上界，故收敛。其极限定义为 $e$。

(b) **方法一：Taylor 展开**

$e^x = 1 + x + \frac{x^2}{2} + O(x^3)$，故
$$\frac{e^x - 1 - x}{x^2} = \frac{\frac{x^2}{2} + O(x^3)}{x^2} = \frac{1}{2} + O(x) \to \frac{1}{2} \quad (x \to 0).$$

**方法二：L'Hôpital 法则**

原式为 $\frac{0}{0}$ 型。第一次 L'Hôpital：
$$\lim_{x \to 0} \frac{e^x - 1}{2x}$$
仍为 $\frac{0}{0}$ 型。第二次 L'Hôpital：
$$\lim_{x \to 0} \frac{e^x}{2} = \frac{1}{2}.$$

(c) $f(x) = \ln(1 + x)$，$f(0) = 0$。

求导：
- $f'(x) = \frac{1}{1 + x}$，$f'(0) = 1$
- $f''(x) = -\frac{1}{(1 + x)^2}$，$f''(0) = -1$
- $f'''(x) = \frac{2}{(1 + x)^3}$，$f'''(0) = 2$

**3 阶 Taylor 多项式**：
$$T_3(x) = f(0) + f'(0)x + \frac{f''(0)}{2!}x^2 + \frac{f'''(0)}{3!}x^3$$

$$= 0 + x - \frac{x^2}{2} + \frac{2x^3}{6} = x - \frac{x^2}{2} + \frac{x^3}{3}.$$

**Lagrange 余项**：
$$R_3(x) = \frac{f^{(4)}(\xi)}{4!} x^4 = \frac{-6}{24(1 + \xi)^4} x^4 = -\frac{x^4}{4(1 + \xi)^4},$$
其中 $\xi$ 介于 $0$ 和 $x$ 之间。

（注：$f^{(4)}(x) = -\frac{6}{(1 + x)^4}$。）

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确得出极限为 $e$ | 2 | |
| (a) 简要说明理由（定义或证明） | 1 | |
| (b) 正确识别 $0/0$ 型 | 1 | |
| (b) 正确应用 Taylor/L'Hôpital | 2 | |
| (b) 正确得出 $1/2$ | 1 | |
| (c) 正确计算前三阶导数 | 2 | 各 0.5 分 |
| (c) 正确写出 $T_3(x)$ | 2 | 含阶乘 |
| (c) 正确写出 Lagrange 余项 | 2 | 含 $f^{(4)}(\xi)$ 和 $4!$ |
| **合计** | **13** → **10** | 按 10 分折算 |

**修正评分标准（总分 10 分）**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 极限 $e$ + 理由 | 2 | |
| (b) 正确计算极限 | 3 | |
| (c) Taylor 多项式（含导数计算） | 3 | |
| (c) Lagrange 余项 | 2 | |
| **合计** | **10** | |

---

#### Q8：计算 — Riemann 积分计算

**难度**：★★★（难）　**对应章节**：Ch 5 — Riemann 积分与 FTC　**分值**：10 分

**题目陈述**：

(a) 用 **Riemann 和的定义**直接计算
$$\int_0^1 x^2 \, dx.$$
即：对分割 $P_n = \{0, \frac{1}{n}, \frac{2}{n}, \ldots, \frac{n-1}{n}, 1\}$，取右端点作为样本点，写出 Riemann 和 $R(P_n, f)$ 的显式表达式，并求 $n \to \infty$ 时的极限。

(b) 利用 **微积分基本定理（FTC）** 验证 (a) 的结果。

(c) 计算 $\displaystyle\int_0^{\pi/2} x \cos x \, dx$。

**参考答案**：

(a) 分割 $P_n$ 将 $[0, 1]$ 分为 $n$ 个等长子区间，$\Delta x = \frac{1}{n}$。

右端点：$x_i^* = \frac{i}{n}$（$i = 1, 2, \ldots, n$）。

Riemann 和：
$$R(P_n, f) = \sum_{i=1}^{n} f(x_i^*) \Delta x = \sum_{i=1}^{n} \left(\frac{i}{n}\right)^2 \cdot \frac{1}{n} = \frac{1}{n^3} \sum_{i=1}^{n} i^2.$$

利用公式 $\sum_{i=1}^{n} i^2 = \frac{n(n+1)(2n+1)}{6}$：

$$R(P_n, f) = \frac{1}{n^3} \cdot \frac{n(n+1)(2n+1)}{6} = \frac{(n+1)(2n+1)}{6n^2}$$

$$= \frac{2n^2 + 3n + 1}{6n^2} = \frac{1}{3} + \frac{1}{2n} + \frac{1}{6n^2}.$$

令 $n \to \infty$：
$$\int_0^1 x^2 \, dx = \lim_{n \to \infty} R(P_n, f) = \frac{1}{3}.$$

(b) **FTC**：设 $F(x) = \frac{x^3}{3}$，则 $F'(x) = x^2 = f(x)$。

由 FTC：
$$\int_0^1 x^2 \, dx = F(1) - F(0) = \frac{1}{3} - 0 = \frac{1}{3}.$$

与 (a) 一致。✓

(c) **分部积分**：令 $u = x$，$dv = \cos x \, dx$，则 $du = dx$，$v = \sin x$。

$$\int_0^{\pi/2} x \cos x \, dx = \left[ x \sin x \right]_0^{\pi/2} - \int_0^{\pi/2} \sin x \, dx$$

$$= \frac{\pi}{2} \cdot 1 - 0 - \left[ -\cos x \right]_0^{\pi/2}$$

$$= \frac{\pi}{2} - (-\cos\frac{\pi}{2} + \cos 0)$$

$$= \frac{\pi}{2} - (0 + 1) = \frac{\pi}{2} - 1.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确写出 Riemann 和表达式 | 2 | 含右端点选取 |
| (a) 正确应用求和公式 | 2 | $\sum i^2 = n(n+1)(2n+1)/6$ |
| (a) 正确取极限得 $1/3$ | 2 | |
| (b) 正确找到原函数 | 1 | $F(x) = x^3/3$ |
| (b) 正确应用 FTC | 1 | $F(1) - F(0)$ |
| (c) 正确选择分部积分 | 1 | |
| (c) 正确计算得 $\pi/2 - 1$ | 1 | |
| **合计** | **10** | |

---

### 模块四：综合拓展（2题，共20分）

---

#### Q9：综合 — 级数收敛的系统性判别

**难度**：★★★☆（较难）　**对应章节**：Ch 2 — 级数收敛　**分值**：10 分

**题目陈述**：

判断下列级数的敛散性。若收敛，说明是绝对收敛还是条件收敛。请明确指出每一步使用的判别法，并验证该判别法的适用条件。

(a) $\displaystyle\sum_{n=1}^{\infty} \frac{n!}{n^n}$

(b) $\displaystyle\sum_{n=2}^{\infty} \frac{(-1)^n}{n \ln n}$

(c) $\displaystyle\sum_{n=1}^{\infty} \frac{\sin n}{n^2}$

**参考答案**：

(a) **绝对收敛**（比值判别法）。

令 $a_n = \frac{n!}{n^n}$。

$$\left| \frac{a_{n+1}}{a_n} \right| = \frac{(n+1)!}{(n+1)^{n+1}} \cdot \frac{n^n}{n!} = \frac{n+1}{(n+1)^{n+1}} \cdot n^n = \frac{n^n}{(n+1)^n} = \left(\frac{n}{n+1}\right)^n = \frac{1}{\left(1 + \frac{1}{n}\right)^n}.$$

当 $n \to \infty$ 时，$\left(1 + \frac{1}{n}\right)^n \to e$，故
$$\lim_{n \to \infty} \left| \frac{a_{n+1}}{a_n} \right| = \frac{1}{e} < 1.$$

由比值判别法，级数绝对收敛。

(b) **条件收敛**（Leibniz 判别法 + 积分判别法）。

令 $a_n = \frac{1}{n \ln n}$（$n \geq 2$）。

- **收敛性**：验证 Leibniz 条件：
  1. $a_n > 0$（显然）；
  2. $a_n \to 0$（因为 $n \ln n \to \infty$）；
  3. $a_{n+1} < a_n$：函数 $f(x) = \frac{1}{x \ln x}$ 在 $x \geq 2$ 时单调递减（导数 $f'(x) = -\frac{\ln x + 1}{(x \ln x)^2} < 0$）。
  
  满足 Leibniz 条件，交错级数收敛。

- **非绝对收敛**：$\sum \frac{1}{n \ln n}$ 用积分判别法。令 $f(x) = \frac{1}{x \ln x}$，则
  $$\int_2^{\infty} \frac{dx}{x \ln x} = \left[ \ln(\ln x) \right]_2^{\infty} = \infty.$$
  积分发散，故 $\sum \frac{1}{n \ln n}$ 发散。

因此原级数条件收敛。

(c) **绝对收敛**（比较判别法）。

$$\left| \frac{\sin n}{n^2} \right| \leq \frac{1}{n^2}.$$

$\sum \frac{1}{n^2}$ 是 $p = 2 > 1$ 的 $p$-级数，收敛。

由比较判别法，$\sum \left| \frac{\sin n}{n^2} \right|$ 收敛，故原级数绝对收敛。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确选择比值判别法 | 1 | |
| (a) 正确计算比值极限 $1/e$ | 2 | 关键步骤：化简为 $(1 + 1/n)^{-n}$ |
| (a) 正确判定绝对收敛 | 1 | |
| (b) 正确应用 Leibniz 判别法 | 2 | 验证三个条件 |
| (b) 正确用积分判别法判定非绝对收敛 | 2 | 计算反常积分 |
| (b) 正确判定条件收敛 | 1 | |
| (c) 正确放缩 $|\sin n| \leq 1$ | 2 | |
| (c) 正确判定绝对收敛 | 1 | |
| (c) 指出 $p$-级数 | 1 | |
| **合计** | **11** → **10** | 按 10 分折算 |

**修正评分标准（总分 10 分）**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 比值判别法 + 极限 $1/e$ + 结论 | 3 | |
| (b) Leibniz + 积分判别 + 条件收敛 | 4 | |
| (c) 比较判别 + 绝对收敛 | 3 | |
| **合计** | **10** | |

---

#### Q10：综合拓展 — 函数序列的一致收敛

**难度**：★★★★（难）　**对应章节**：Ch 6 — 函数序列的一致收敛　**分值**：10 分

**题目陈述**：

设函数序列 $f_n: [0, 1] \to \mathbb{R}$ 定义为 $f_n(x) = x^n$。

(a) 求 $f_n$ 的**点态极限**函数 $f(x) = \lim_{n \to \infty} f_n(x)$，并写出 $f(x)$ 的分段表达式。

(b) 证明 $f_n$ 在 $[0, 1]$ 上**不一致收敛**于 $f$。

(c) 证明：对任意 $0 < a < 1$，$f_n$ 在 $[0, a]$ 上**一致收敛**于 $f$。

(d) 解释为什么 (b) 和 (c) 不矛盾，并说明一致收敛与定义域的关系。

**参考答案**：

(a) **点态极限**：

- 当 $0 \leq x < 1$ 时，$x^n \to 0$（$n \to \infty$）；
- 当 $x = 1$ 时，$1^n = 1 \to 1$。

故
$$f(x) = \begin{cases} 0 & 0 \leq x < 1, \\ 1 & x = 1. \end{cases}$$

注意 $f$ 在 $x = 1$ 处不连续（左极限为 0，函数值为 1）。

(b) **在 $[0, 1]$ 上不一致收敛**：

一致收敛要求：$\forall \varepsilon > 0$，$\exists N \in \mathbb{N}$，使得对所有 $n \geq N$ 和所有 $x \in [0, 1]$，有 $|f_n(x) - f(x)| < \varepsilon$。

取 $\varepsilon_0 = \frac{1}{2}$。对任意 $N$，取 $n = N$ 和 $x = (\frac{1}{2})^{1/N} \in [0, 1)$（满足 $x^N = \frac{1}{2}$）。

则 $f(x) = 0$，故
$$|f_N(x) - f(x)| = |x^N - 0| = \frac{1}{2} = \varepsilon_0 \not< \varepsilon_0.$$

更简洁地：对任意 $n$，
$$\sup_{x \in [0, 1]} |x^n - f(x)| = \sup_{x \in [0, 1)} x^n = 1$$
（上确界在 $x \to 1^-$ 时趋近于 1，但永远达不到；实际上 $\sup_{x \in [0, 1)} x^n = 1$，因为可以任意接近 1）。

由于上确界不趋于 0，$f_n$ 不一致收敛于 $f$。

（标准证法：对任意 $n$，取 $x_n = (1/2)^{1/n} \in [0, 1)$，则 $|f_n(x_n) - f(x_n)| = 1/2 \not\to 0$。）

(c) **在 $[0, a]$ 上一致收敛**（$0 < a < 1$）：

对 $x \in [0, a]$，$f(x) = 0$，故
$$|f_n(x) - f(x)| = |x^n - 0| = x^n \leq a^n.$$

由于 $0 < a < 1$，$a^n \to 0$（$n \to \infty$）。

对任意 $\varepsilon > 0$，取 $N$ 使得 $a^N < \varepsilon$（这样的 $N$ 存在，因为 $a^n \to 0$）。

则当 $n \geq N$ 时，对所有 $x \in [0, a]$：
$$|f_n(x) - f(x)| \leq a^n \leq a^N < \varepsilon.$$

这正是一致收敛的定义。故 $f_n \rightrightarrows f$ 在 $[0, a]$ 上。

(d) **解释**：

(b) 和 (c) 不矛盾，因为**一致收敛依赖于所考虑的定义域**。

- 在 $[0, 1]$ 上，问题出在 $x = 1$ 附近：无论 $n$ 多大，总存在充分接近 1 的点使得 $x^n$ 不接近 0。$\sup$ 范数不能任意小。
- 在 $[0, a]$ 上，$x$ 与 1 保持一个正的距离（$\leq a < 1$），因此 $x^n$ 被 $a^n$ 一致控制，而 $a^n \to 0$ 与 $x$ 无关。

这说明一致收敛是一种"整体性"性质：不能仅看点态行为，而要看整个定义域上"最坏情况"的行为是否趋于 0。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确写出点态极限 | 2 | 分段函数，$x = 1$ 处为 1 |
| (b) 正确写出不一致收敛定义 | 1 | |
| (b) 正确构造反例或计算 $\sup$ | 3 | 关键：$\sup |f_n - f| = 1$ 不趋于 0 |
| (c) 正确利用 $a^n \to 0$ | 2 | 与 $x$ 无关 |
| (c) 验证一致收敛定义 | 1 | 给出统一的 $N$ |
| (d) 正确解释域依赖关系 | 1 | "整体性质"、"最坏情况" |
| **合计** | **10** | |

---

## 附录：题目与课程定理对应总表

| 题号 | 测试阶段 | 模块 | 对应定理/章节 | 核心概念 | 难度 |
|------|----------|------|--------------|----------|------|
| Q1 | 课前基线 | — | Ch 1 — 确界原理 | 完备性、确界 | ★★☆ |
| Q2 | 课前基线 | — | Ch 2 — 序列极限 | $\varepsilon$-$N$ 定义 | ★★☆ |
| Q3 | 课前基线 | — | Ch 3 — 连续性 | $\varepsilon$-$\delta$、Dirichlet 函数 | ★★★ |
| Q4 | 课前基线 | — | Ch 2 — 级数 | 比较、Leibniz、比值 | ★★☆ |
| Q5 | 课前基线 | — | Ch 4 — 导数 | 导数定义、夹逼 | ★★☆ |
| Q6 | 期末综合 | 定理证明 | BW 定理 | 二分法、子列 | ★★★ |
| Q7 | 期末综合 | 定理证明 | Heine-Cantor | 一致连续、紧性 | ★★★☆ |
| Q8 | 期末综合 | 定理证明 | IVT | 二分法、闭区间套 | ★★★ |
| Q9 | 期末综合 | 定理证明 | Rolle + MVT | 辅助函数、极值 | ★★★ |
| Q10 | 期末综合 | 综合拓展 | 一致收敛 | 点态 vs 一致、$\sup$ 范数 | ★★★★ |
| Q1(期末) | 期末综合 | 定义复述 | Ch 2–3 | Cauchy、一致连续 | ★★☆ |
| Q2(期末) | 期末综合 | 定义复述 | Ch 5 | Riemann 可积 | ★★★ |
| Q7(期末) | 期末综合 | 计算应用 | Ch 2, Ch 4 | 极限、Taylor | ★★★ |
| Q8(期末) | 期末综合 | 计算应用 | Ch 5 | Riemann 和、FTC | ★★★ |
| Q9(期末) | 期末综合 | 综合拓展 | Ch 2 | 级数判别综合 | ★★★☆ |
| Q10(期末) | 期末综合 | 综合拓展 | Ch 6 | 函数序列一致收敛 | ★★★★ |

---

**文档版本**：v1.0（2026-04-18）

**关联文件**：
- `project/MIT-18.100A-课堂验证模块设计.md`
- `project/MIT-18.100A-讲义逐章拆解索引.md`
- `project/MIT-18.100A-L4-定理对齐表.md`
'''

with open('project/adaptive-learning-system/validation/测试题库-MIT-18.100A.md', 'w', encoding='utf-8') as f:
    f.write(content)
print('Done, length:', len(content))
