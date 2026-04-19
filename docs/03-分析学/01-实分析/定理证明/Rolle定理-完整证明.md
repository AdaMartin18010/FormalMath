---
title: Rolle 定理（Rolle's Theorem）
level: silver
course: MIT 18.100A Real Analysis
msc_primary: 26

  - 26A06
  - 26A24
  - 26A27
target_courses:
  - "MIT 18.100A Ch.4"
references:
  textbooks:
    - title: "Basic Analysis I: Introduction to Real Analysis, Volume 1"
      author: "Jiri Lebl"
      edition: "1st"
      chapters: ["Ch. 4: The Derivative"]
      pages: "101-103"
    - title: "Principles of Mathematical Analysis"
      author: "Walter Rudin"
      edition: "3rd"
      chapters: ["Ch. 5: Differentiation"]
      pages: "108-109"
  databases:
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/Rolle+theorem"
review_status: mathematical_reviewed
processed_at: '2026-04-20'
---

# Rolle 定理（Rolle's Theorem）

> **课程**: MIT 18.100A 实分析 | **章节**: Ch.4 — 导数
> **学习目标**: 理解 Rolle 定理的条件与结论；掌握辅助函数构造法；能够运用 Rolle 定理证明中值定理及解决方程根的存在性问题

---

## 一、定理陈述

**定理（Rolle / 罗尔, 1691）**：设函数 $f: [a, b] \to \mathbb{R}$ 满足：

1. **闭区间连续**：$f$ 在闭区间 $[a, b]$ 上连续；
2. **开区间可微**：$f$ 在开区间 $(a, b)$ 上可微；
3. **端点值相等**：$f(a) = f(b)$。

则存在至少一点 $c \in (a, b)$，使得

$$f'(c) = 0.$$

**几何解释**：若一条光滑曲线在两个端点处高度相同，则在这两点之间必存在一条水平切线（即导数为零的点）。

---

## 二、证明思路

Rolle 定理的证明是分析学中**极值定理 + 导数定义**联合运用的经典范例。核心策略分为三步：

1. **利用极值定理**：闭区间上的连续函数必取得最大值和最小值。
2. **分类讨论极值点位置**：
   - 若最大值或最小值落在区间内部 $(a, b)$，则该点为局部极值点，由 Fermat 引理知导数为零。
   - 若最大值和最小值都落在端点，则由 $f(a)=f(b)$ 知函数恒为常数，导数处处为零。
3. **结论**：无论哪种情况，都存在 $c \in (a, b)$ 使 $f'(c) = 0$。

---

## 三、详细证明

**给定**：$f: [a, b] \to \mathbb{R}$ 连续，在 $(a, b)$ 上可微，且 $f(a) = f(b)$。

**目标**：证明存在 $c \in (a, b)$ 使得 $f'(c) = 0$。

---

### 步骤 1：应用极值定理

由**极值定理**（Extreme Value Theorem），$f$ 在 $[a, b]$ 上取得最大值 $M$ 和最小值 $m$。即存在 $x_M, x_m \in [a, b]$ 使得：

$$f(x_M) = M = \sup_{x \in [a, b]} f(x), \quad f(x_m) = m = \inf_{x \in [a, b]} f(x).$$

---

### 步骤 2：分类讨论

#### 情形 A：$M > m$（函数非常数）

由于 $f(a) = f(b)$，端点处的函数值不可能同时等于最大值 $M$ 和最小值 $m$（否则 $M = m$，与假设矛盾）。因此，$M$ 和 $m$ 中**至少有一个**在开区间 $(a, b)$ 内取得。

不妨设最大值 $M$ 在内部某点 $c \in (a, b)$ 处取得，即 $f(c) = M$。

**应用 Fermat 引理**：

由于 $f$ 在 $(a, b)$ 上可微，且 $c \in (a, b)$ 是 $f$ 的**局部极大值点**（实际上是全局最大值点），由 Fermat 引理（可微函数在内部极值点处导数为零）：

$$f'(c) = 0.$$

> **Fermat 引理回顾**：若 $f$ 在 $c$ 处可微且 $c$ 是局部极值点，则 $f'(c) = 0$。
> 
> **简要证明**：设 $c$ 是局部极大值点，则对足够小的 $h > 0$：
> - 右差商：$\dfrac{f(c+h) - f(c)}{h} \leq 0$，令 $h \to 0^+$ 得 $f'(c) \leq 0$；
> - 左差商：$\dfrac{f(c-h) - f(c)}{-h} \geq 0$，令 $h \to 0^+$ 得 $f'(c) \geq 0$。
> 
> 故 $f'(c) = 0$。∎

同理，若最小值 $m$ 在内部某点取得，该点导数也为零。

#### 情形 B：$M = m$（函数为常数）

若 $M = m$，则 $f(x) = M = m$ 对所有 $x \in [a, b]$ 成立，即 $f$ 是**常数函数**。

对常数函数，$f'(x) = 0$ 对所有 $x \in (a, b)$ 成立。任取 $c \in (a, b)$ 即有 $f'(c) = 0$。

---

### 步骤 3：结论

无论情形 A 还是情形 B，都存在 $c \in (a, b)$ 使得 $f'(c) = 0$。

$$\tag*{$\square$}$$

---

## 四、与 MIT 18.100A / Lebl 教材对齐

| 要素 | MIT 18.100A (Lebl Ch.4) | 本文档 | 对齐状态 |
|------|------------------------|--------|---------|
| 定理条件 | 连续、可微、$f(a)=f(b)$ | 完全一致 | ✅ 严格等价 |
| 证明策略 | 极值定理 + Fermat 引理 | 完全一致 | ✅ 严格等价 |
| 分类讨论 | 常数 / 非常数 | 完全一致 | ✅ 严格等价 |
| Fermat 引理引用 | 作为前置引理 | 完整陈述并附简要证明 | ✅ 强化 |

**教材原文定位**：Lebl, *Basic Analysis I*, Theorem 4.2.1 (p.101-103)。

---

## 五、常见误区与诊断

| 误区 | 错误表现 | 纠正 |
|------|---------|------|
| **忽略端点条件** | 认为"连续可微函数内部必有导数为零的点" | 必须 $f(a)=f(b)$，反例：$f(x)=x$ 在 $[0,1]$ 上 |
| **混淆可微范围** | 只在闭区间 $[a,b]$ 上假设可微 | Rolle 定理只要求开区间 $(a,b)$ 可微，端点可不可微无所谓 |
| **认为 $c$ 唯一** | 误以为满足条件的 $c$ 只有一个 | 可以有多个，例如 $f(x)=\sin x$ 在 $[0, 2\pi]$ 上 |
| **跳过 Fermat 引理** | 直接说"最大值点导数为零"而不证明 | 需要 Fermat 引理的严格保证 |

---

## 六、应用：从中值定理的视角

Rolle 定理是**中值定理**（Mean Value Theorem）的直接前身。事实上，中值定理可通过构造辅助函数从 Rolle 定理导出：

**辅助函数构造**：设 $f$ 在 $[a,b]$ 上连续、在 $(a,b)$ 上可微。定义

$$g(x) = f(x) - \left( f(a) + \frac{f(b)-f(a)}{b-a}(x-a) \right).$$

则 $g(a) = g(b) = 0$，且 $g$ 满足 Rolle 定理条件。于是存在 $c \in (a,b)$ 使 $g'(c) = 0$，即

$$f'(c) = \frac{f(b)-f(a)}{b-a}.$$

> 本文档专注于 Rolle 定理本身。关于中值定理的完整证明，请参阅 `docs/03-分析学/01-实分析/定理证明/中值定理-完整证明.md`。

---

## 七、习题

### 习题 1（基础）

验证 $f(x) = x^3 - 3x + 1$ 在区间 $[0, 2]$ 上是否满足 Rolle 定理条件。若满足，求出所有满足 $f'(c)=0$ 的 $c \in (0, 2)$。

<details>
<summary>解答</summary>

$f(0) = 1$，$f(2) = 8 - 6 + 1 = 3$。由于 $f(0) \neq f(2)$，**不满足** Rolle 定理的端点条件。

> 注意：此题旨在训练学生首先验证三个条件，而非盲目套用结论。
</details>

### 习题 2（标准）

设 $f$ 在 $[a, b]$ 上连续，在 $(a, b)$ 上二阶可微，且 $f(a) = f(b) = 0$。证明：对任意 $d \in (a, b)$，存在 $c \in (a, b)$ 使得

$$f(d) = \frac{f''(c)}{2}(d-a)(d-b).$$

<details>
<summary>提示</summary>

构造辅助函数 $g(x) = f(x) - K(x-a)(x-b)$，选取适当的 $K$ 使得 $g(d) = 0$，然后对 $g$ 在 $[a,d]$ 和 $[d,b]$ 上分别应用 Rolle 定理。
</details>

### 习题 3（反例构造）

构造一个函数，说明"可微"条件不能减弱为"几乎处处可微"或"连续"。

<details>
<summary>解答</summary>

取 $f(x) = |x|$ 在 $[-1, 1]$ 上。$f(-1) = f(1) = 1$，连续，但在 $x=0$ 处不可微。不存在 $c \in (-1, 1)$ 使 $f'(c) = 0$（在 $x \neq 0$ 处 $f'(x) = \pm 1$）。
</details>

---

## 八、Lean4 形式化对应

```lean4
import Mathlib

-- Rolle 定理：满足端点相等条件的可微函数在内部必有导数为零的点
 theorem rolle_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hf_eq : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  -- 证明思路：极值定理 + Fermat 引理
  -- 详细证明需要 Mathlib4 中的极值定理和导数工具
  sorry
```

> 完整形式化证明请参阅 `docs/09-形式化证明/Lean4/09-罗尔定理.lean`。

### 习题 4（标准）

证明：方程 $e^x = 3 - x$ 在 $\mathbb{R}$ 上**至多有一个实根**。

<details>
<summary>解答</summary>

设 $f(x) = e^x + x - 3$。假设存在两个不同的根 $a < b$，即 $f(a) = f(b) = 0$。

$f$ 在 $[a, b]$ 上连续，在 $(a, b)$ 上可微（因为 $e^x$ 和 $x$ 都可微）。

由 Rolle 定理，存在 $c \in (a, b)$ 使 $f'(c) = 0$。

但 $f'(x) = e^x + 1 > 0$ 对所有 $x \in \mathbb{R}$ 成立，矛盾！

故方程至多有一个实根。

> **注**: 结合介值定理（$f(0) = -2 < 0$, $f(1) = e - 2 > 0$），可进一步证明恰有一个根。
</details>

### 习题 5（标准）

设 $f$ 在 $[a, b]$ 上连续，在 $(a, b)$ 上二阶可微，且 $f(a) = f(b) = 0$。证明：对任意 $x_0 \in (a, b)$，存在 $c \in (a, b)$ 使得

$$f(x_0) = \frac{f''(c)}{2}(x_0 - a)(x_0 - b).$$

<details>
<summary>解答</summary>

**构造辅助函数**。令

$$g(x) = f(x) - K(x - a)(x - b),$$

其中 $K$ 选取使得 $g(x_0) = 0$，即 $K = \dfrac{f(x_0)}{(x_0 - a)(x_0 - b)}$。

验证：$g(a) = f(a) - K \cdot 0 = 0$，$g(b) = f(b) - K \cdot 0 = 0$，$g(x_0) = 0$。

在 $[a, x_0]$ 上应用 Rolle 定理：存在 $c_1 \in (a, x_0)$ 使 $g'(c_1) = 0$。

在 $[x_0, b]$ 上应用 Rolle 定理：存在 $c_2 \in (x_0, b)$ 使 $g'(c_2) = 0$。

在 $[c_1, c_2]$ 上再对 $g'$ 应用 Rolle 定理：存在 $c \in (c_1, c_2) \subseteq (a, b)$ 使 $g''(c) = 0$。

计算：$g''(x) = f''(x) - 2K$，故 $g''(c) = 0 \Rightarrow f''(c) = 2K = \dfrac{2f(x_0)}{(x_0 - a)(x_0 - b)}$。

整理即得所求等式。
</details>

### 习题 6（概念辨析）

下列函数在 $[-1, 1]$ 上是否满足 Rolle 定理条件？若满足，求出所有满足 $f'(c) = 0$ 的 $c \in (-1, 1)$。

(a) $f(x) = x^2$

(b) $f(x) = |x|$

(c) $f(x) = x^3 - x$

<details>
<summary>解答</summary>

**(a)** $f(x) = x^2$：
- 连续：✅
- 可微：✅（$f'(x) = 2x$）
- $f(-1) = f(1) = 1$：✅

满足 Rolle 定理。$f'(c) = 2c = 0 \Rightarrow c = 0$。

**(b)** $f(x) = |x|$：
- 连续：✅
- 可微：❌（在 $x = 0$ 处不可微，左导数为 $-1$，右导数为 $1$）

**不满足** Rolle 定理条件。注意：即使 "$f'(c) = 0$" 在 $c$ 不存在处"形式上成立"，定理的前提条件不满足，不能直接应用。

**(c)** $f(x) = x^3 - x = x(x-1)(x+1)$：
- 连续：✅（多项式）
- 可微：✅
- $f(-1) = f(1) = 0$：✅

满足 Rolle 定理。$f'(x) = 3x^2 - 1 = 0 \Rightarrow x = \pm \dfrac{1}{\sqrt{3}}$。

两个解都在 $(-1, 1)$ 内。**Rolle 定理不保证唯一性**。
</details>

### 习题 7（证明型）

设 $f$ 在 $[0, 1]$ 上可微，且 $f(0) = 0$，$f(1) = 1$。证明：对任意正实数 $a, b$，存在 $c \in (0, 1)$ 使得

$$\frac{a}{f'(c)} + \frac{b}{f'(c)} = a + b.$$

<details>
<summary>提示</summary>

实际上，所求等式可简化为 $\dfrac{a+b}{f'(c)} = a+b$，即 $f'(c) = 1$。

构造 $g(x) = f(x) - x$，则 $g(0) = g(1) = 0$，应用 Rolle 定理即可。

> 此题旨在训练学生简化问题，而非被复杂形式迷惑。
</details>

### 习题 8（证明型）

设 $f$ 在 $[a, b]$ 上连续，在 $(a, b)$ 上可微，且 $f(a) = f(b) = 0$。证明：对任意实数 $\lambda$，存在 $c \in (a, b)$ 使得

$$f'(c) = \lambda f(c).$$

<details>
<summary>解答</summary>

**构造辅助函数**。令 $g(x) = e^{-\lambda x} f(x)$。

则 $g(a) = e^{-\lambda a} f(a) = 0$，$g(b) = e^{-\lambda b} f(b) = 0$。

$g$ 在 $[a, b]$ 上连续，在 $(a, b)$ 上可微。

由 Rolle 定理，存在 $c \in (a, b)$ 使 $g'(c) = 0$。

计算：$g'(x) = e^{-\lambda x}(f'(x) - \lambda f(x))$。

$g'(c) = 0$ 且 $e^{-\lambda c} \neq 0$，故 $f'(c) - \lambda f(c) = 0$，即 $f'(c) = \lambda f(c)$。
</details>

### 习题 9（反例构造）

构造一个函数 $f: [0, 1] \to \mathbb{R}$，使得 $f$ 在 $[0, 1]$ 上连续，$f(0) = f(1)$，但 $f$ 在 $(0, 1)$ 上**没有**任何点可微。

<details>
<summary>解答</summary>

取 $f$ 为 **Weierstrass 函数** 的变体，或更简单地：

令 $f(x) = \operatorname{dist}(x, \mathbb{Z})$ 在 $[0, 1]$ 上的限制，即锯齿波函数：

$$f(x) = \begin{cases} x, & 0 \leq x \leq \dfrac{1}{2}, \\ 1 - x, & \dfrac{1}{2} < x \leq 1. \end{cases}$$

此函数在 $x = 1/2$ 处**不可微**（左导数为 $1$，右导数为 $-1$），但这不是处处不可微。

**真正的处处不可微构造**（满足端点条件）：

令 $g$ 为经典的 Weierstrass 函数（在 $\mathbb{R}$ 上连续但处处不可微），定义

$$f(x) = g(x) - x(g(1) - g(0)).$$

则 $f(0) = g(0)$，$f(1) = g(1) - (g(1) - g(0)) = g(0)$，故 $f(0) = f(1)$。

$f$ 是连续函数与线性函数的差，仍连续。但 $f$ 在 $(0, 1)$ 上处处不可微（因为 $g$ 处处不可微，线性项不改变不可微性）。

> 此题说明：**可微性条件不能省略**，即使连续性和端点条件满足。
</details>

### 习题 10（高阶推广）

**广义 Rolle 定理**：设 $f$ 在 $[a, b]$ 上 $n$ 阶可微，且 $f(a) = f'(a) = \cdots = f^{(n-1)}(a) = 0$，$f(b) = 0$。证明：存在 $c \in (a, b)$ 使得 $f^{(n)}(c) = 0$。

<details>
<summary>解答</summary>

对 $n$ 使用**数学归纳法**。

**基础 $n = 1$**：即标准 Rolle 定理，已知成立。

**归纳假设**：设结论对 $n = k$ 成立。

**归纳步骤**（$n = k + 1$）：

设 $f$ 满足 $f(a) = f'(a) = \cdots = f^{(k)}(a) = 0$ 且 $f(b) = 0$。

令 $g(x) = f'(x)$。则 $g$ 在 $[a, b]$ 上 $k$ 阶可微，且

$$g(a) = f'(a) = 0,\; g'(a) = f''(a) = 0,\; \ldots,\; g^{(k-1)}(a) = f^{(k)}(a) = 0.$$

此外，由 Rolle 定理（对 $f$ 在 $[a, b]$ 上），存在 $c_1 \in (a, b)$ 使 $f'(c_1) = g(c_1) = 0$。

对 $g$ 在 $[a, c_1]$ 上应用归纳假设（$n = k$）：存在 $c \in (a, c_1) \subseteq (a, b)$ 使 $g^{(k)}(c) = 0$。

而 $g^{(k)}(c) = f^{(k+1)}(c)$，故 $f^{(k+1)}(c) = 0$。

归纳完成。
</details>

---

## 九、## 相关文档

- [MIT-18.100A-学习诊断手册](..\MIT-18.100A-学习诊断手册.md)
- [01-确界原理与Archimedean性质](..\MIT-18.100A\01-确界原理与Archimedean性质.md)
- [02-介值定理](..\MIT-18.100A\02-介值定理.md)
- [03-一致连续性](..\MIT-18.100A\03-一致连续性.md)
- [04-中值定理](..\MIT-18.100A\04-中值定理.md)

参考文献

1. Lebl, J. *Basic Analysis I: Introduction to Real Analysis, Volume 1*. CreateSpace, 2018. §4.2.
2. Rudin, W. *Principles of Mathematical Analysis*. 3rd ed. McGraw-Hill, 1976. Theorem 5.10.
3. nLab, "Rolle theorem", https://ncatlab.org/nlab/show/Rolle+theorem.
## 参考文献

1. Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.). McGraw-Hill. ISBN: 978-0070542358.
2. Tao, T. (2006). *Analysis I*. Hindustan Book Agency. ISBN: 978-8185931623.
3. Abbott, S. (2015). *Understanding Analysis* (2nd ed.). Springer. ISBN: 978-1493927111.