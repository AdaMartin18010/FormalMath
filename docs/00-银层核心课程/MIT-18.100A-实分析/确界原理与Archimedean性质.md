---
course: MIT 18.100A 实分析

title: "确界原理与 Archimedean 性质"
level: "silver"
msc_primary: "26-01"
target_courses:
  - "MIT 18.100A"
references:
  textbooks:
    - title: "Introduction to Analysis"
      author: "Arthur Mattuck"
      edition: "1st"
      chapters: "Ch. 2–3"
      pages: "25–45"
    - title: "Principles of Mathematical Analysis"
      author: "Walter Rudin"
      edition: "3rd"
      chapters: "Ch. 1"
      pages: "3–11"
  lectures:
    - institution: "MIT"
      course_code: "18.100A"
      lecture: "Lecture 3–4"
      url: "https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/"
keywords:
  - "确界原理"
  - "上确界"
  - "下确界"
  - "Archimedean 性质"
  - "实数完备性"
status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# 确界原理与 Archimedean 性质

> **课程**: MIT 18.100A Real Analysis | **章节**: Ch. 2–3
> **学习目标**: 掌握确界的严格定义与存在性证明，理解 Archimedean 性质的等价表述及其在分析学中的基础性作用。

---

## 一、核心定义

### 定义 1.1（上界与下界）

**严格陈述**: 设 $S \subseteq \mathbb{R}$ 为实数集的一个非空子集。

- 若存在实数 $M \in \mathbb{R}$，使得对一切 $x \in S$ 都有 $x \leq M$，则称 $M$ 为集合 $S$ 的一个**上界**（upper bound）。此时称 $S$ **有上界**（bounded above）。
- 若存在实数 $m \in \mathbb{R}$，使得对一切 $x \in S$ 都有 $x \geq m$，则称 $m$ 为集合 $S$ 的一个**下界**（lower bound）。此时称 $S$ **有下界**（bounded below）。
- 若 $S$ 既有上界又有下界，则称 $S$ **有界**（bounded）。

**直观解释**: 上界就是"在集合 $S$ 的右边"的数——集合中没有任何元素能超过它。下界同理在"左边"。注意：上界和下界**不一定属于**集合 $S$ 本身。

---

### 定义 1.2（上确界与下确界）

**严格陈述**: 设 $S \subseteq \mathbb{R}$ 为非空子集。

- 实数 $s \in \mathbb{R}$ 称为 $S$ 的**上确界**（supremum，记作 $\sup S$），如果满足以下两个条件：
  1. **上界性**: $s$ 是 $S$ 的上界，即对一切 $x \in S$，有 $x \leq s$；
  2. **最小性**: 对任意 $\varepsilon > 0$，存在 $x_\varepsilon \in S$ 使得 $x_\varepsilon > s - \varepsilon$。

  等价地，最小性也可表述为：若 $M$ 是 $S$ 的任意上界，则 $s \leq M$。

- 实数 $t \in \mathbb{R}$ 称为 $S$ 的**下确界**（infimum，记作 $\inf S$），如果满足以下两个条件：
  1. **下界性**: $t$ 是 $S$ 的下界，即对一切 $x \in S$，有 $x \geq t$；
  2. **最大性**: 对任意 $\varepsilon > 0$，存在 $x_\varepsilon \in S$ 使得 $x_\varepsilon < t + \varepsilon$。

  等价地，最大性也可表述为：若 $m$ 是 $S$ 的任意下界，则 $t \geq m$。

**直观解释**: 上确界是"最贴近集合右侧的那个数"。它不一定在集合内部，但任何比它小的数都不再是上界——集合中总有元素能跑到那个更小数的右边去。下确界则是"最贴近集合左侧的那个数"。

> **双语对照**:
>
> ```lean4
> -- 上确界的 Mathlib4 定义：IsLUB S s 表示 s 是集合 S 的最小上界
> def IsLUB (S : Set ℝ) (s : ℝ) : Prop :=
>   s ∈ upperBounds S ∧ ∀ x ∈ upperBounds S, s ≤ x
>
> -- 下确界的 Mathlib4 定义：IsGLB S s 表示 s 是集合 S 的最大下界
> def IsGLB (S : Set ℝ) (s : ℝ) : Prop :=
>   s ∈ lowerBounds S ∧ ∀ x ∈ lowerBounds S, x ≤ s
> ```

---

### 定义 1.3（最大值与最小值）

**严格陈述**: 设 $S \subseteq \mathbb{R}$ 为非空子集。

- 若存在 $M \in S$ 使得对一切 $x \in S$ 都有 $x \leq M$，则称 $M$ 为 $S$ 的**最大值**（maximum），记作 $\max S$。
- 若存在 $m \in S$ 使得对一切 $x \in S$ 都有 $x \geq m$，则称 $m$ 为 $S$ 的**最小值**（minimum），记作 $\min S$。

**关键区别**: 最大值**必须属于**集合 $S$，而上确界**不一定属于** $S$。因此，若 $\max S$ 存在，则必有 $\max S = \sup S$；反之不然。

---

## 二、核心定理与完整证明

### 定理 2.1（确界原理 / Supremum Principle）

**定理陈述**: 设 $S \subseteq \mathbb{R}$ 为非空子集。若 $S$ 有上界，则 $S$ 必有上确界，即存在唯一的实数 $s = \sup S$ 满足定义 1.2 中的两个条件。同理，若 $S$ 有下界，则 $S$ 必有下确界。

> **证明要点提示**: 确界原理的证明依赖于实数的**完备性**（completeness）。从戴德金分割的视角，我们将所有上界组成一个"右集"，其分割点即为上确界；从柯西序列的视角，我们构造一个单调递增的序列逼近上确界。

---

**证明**（戴德金分割视角）:

设 $S \subseteq \mathbb{R}$ 为非空有上界的实数集。我们利用实数的戴德金分割构造来证明上确界的存在性。

**步骤 1：构造分割。**

定义两个集合：
$$A = \{a \in \mathbb{Q} : \exists x \in S,\, a < x\}, \quad B = \{b \in \mathbb{Q} : \forall x \in S,\, x \leq b\}.$$

换言之，$A$ 包含所有小于 $S$ 中某个元素的有理数，$B$ 包含所有 $S$ 的上界中的有理数。

**步骤 2：验证 $(A, B)$ 构成戴德金分割。**

我们需要验证以下三条性质：

1. **$A \neq \emptyset$ 且 $B \neq \emptyset$**:
   - 因 $S$ 非空，取 $x_0 \in S$。由有理数的稠密性，存在有理数 $a < x_0$，故 $a \in A$，$A \neq \emptyset$。
   - 因 $S$ 有上界，设 $M$ 为其上界。由有理数的稠密性，存在有理数 $b \geq M$（例如取 $b = \lceil M \rceil + 1$），则对一切 $x \in S$ 有 $x \leq M \leq b$，故 $b \in B$，$B \neq \emptyset$。

2. **$A \cup B = \mathbb{Q}$ 且 $A \cap B = \emptyset$**:
   - 若 $q \in \mathbb{Q}$ 且 $q \notin A$，则不存在 $x \in S$ 使得 $q < x$，即对所有 $x \in S$ 有 $x \leq q$，故 $q \in B$。因此 $A \cup B = \mathbb{Q}$。
   - 若 $q \in A \cap B$，则既存在 $x \in S$ 使 $q < x$，又对一切 $x \in S$ 有 $x \leq q$，矛盾。故 $A \cap B = \emptyset$。

3. **$A$ 中无最大元**:
   - 设 $a \in A$，则存在 $x \in S$ 使 $a < x$。由有理数的稠密性，存在有理数 $a'$ 使得 $a < a' < x$。于是 $a' \in A$ 且 $a' > a$，故 $A$ 中不存在最大元。

因此 $(A, B)$ 构成一个戴德金分割，它对应唯一的实数 $s \in \mathbb{R}$。

**步骤 3：验证 $s$ 是 $S$ 的上确界。**

首先证明 $s$ 是 $S$ 的上界。假设存在 $x \in S$ 使得 $x > s$。由有理数的稠密性，存在有理数 $q$ 使得 $s < q < x$。因为 $q > s$，所以 $q \in B$；但因为 $q < x$ 且 $x \in S$，所以 $q \in A$。这与 $A \cap B = \emptyset$ 矛盾。故对一切 $x \in S$ 有 $x \leq s$，$s$ 是上界。

其次证明 $s$ 是最小上界。设 $M < s$ 为任意小于 $s$ 的实数。由戴德金分割的定义，$M \in A$（因为 $M < s$ 意味着 $M$ 不在"右集"中）。因此存在 $x \in S$ 使得 $M < x$。这说明任何小于 $s$ 的数 $M$ 都不是上界。故 $s$ 是最小上界。

**步骤 4：唯一性。**

若 $s_1$ 和 $s_2$ 都是 $S$ 的上确界，则 $s_1$ 是最小上界，$s_2$ 也是上界，故 $s_1 \leq s_2$；同理 $s_2 \leq s_1$。因此 $s_1 = s_2$，上确界唯一。

下确界的存在性可通过上确界推导：令 $S' = \{-x : x \in S\}$，则 $S'$ 非空有上界，设 $\sup S' = s'$，则 $\inf S = -s'$。

$\square$

---

> **双语对照**（确界原理）:
>
> ```lean4
> -- 确界原理：非空有上界的实数集必有上确界
> theorem supremum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
>     ∃ s : ℝ, IsLUB S s := by
>   /- 这是实数完备性的直接推论，Mathlib4 中由 Real 的完备格结构保证 -/
>   exact Real.exists_isLUB S hne hbdd
>
> -- 下确界原理：非空有下界的实数集必有下确界
> theorem infimum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S) :
>     ∃ s : ℝ, IsGLB S s := by
>   exact Real.exists_isGLB S hne hbdd
> ```

---

### 定理 2.2（Archimedean 性质）

**定理陈述**: 实数域 $\mathbb{R}$ 满足 **Archimedean 性质**，即以下三个命题等价且成立：

1. **标准形式**: 对任意正实数 $x > 0$ 和任意实数 $y$，存在正整数 $n \in \mathbb{N}^+$ 使得 $n \cdot x > y$。
2. **整数形式**: 对任意实数 $x$，存在整数 $n \in \mathbb{Z}$ 使得 $n > x$。
3. **有理数稠密**: 对任意实数 $a < b$，存在有理数 $q \in \mathbb{Q}$ 使得 $a < q < b$。

> **证明要点提示**: Archimedean 性质的证明直接依赖于确界原理。用反证法：假设不存在这样的 $n$，则所有 $n \cdot x$ 都被 $y$ 所界，从而有上确界，导出矛盾。

---

**证明**（标准形式 ⟹ 整数形式 ⟹ 有理数稠密性）:

**第一部分：标准形式 ⟹ 整数形式。**

设 $x \in \mathbb{R}$ 为任意实数。取标准形式中的 $x_0 = 1 > 0$，$y = x$，则存在 $n \in \mathbb{N}^+$ 使得 $n \cdot 1 > x$，即 $n > x$。整数形式得证。

**第二部分：整数形式 ⟹ 标准形式。**

设 $x > 0$，$y \in \mathbb{R}$。由整数形式，存在 $n \in \mathbb{Z}$ 使得 $n > y/x$。因 $x > 0$，两边乘以 $x$ 得 $n \cdot x > y$。若 $n \leq 0$，则取 $n' = 1$，因 $x > 0$ 且 $y$ 为任意实数，需仔细处理：实际上因 $x > 0$，可取 $n = \max\{1, \lfloor y/x \rfloor + 1\}$，则 $n \in \mathbb{N}^+$ 且 $n \cdot x > y$。

**第三部分：标准形式的直接证明（反证法）。**

假设标准形式不成立，即存在 $x > 0$ 和 $y \in \mathbb{R}$，使得对所有 $n \in \mathbb{N}^+$ 都有 $n \cdot x \leq y$。

考虑集合 $A = \{n \cdot x : n \in \mathbb{N}^+\}$。由假设，$A$ 有上界 $y$，且 $A$ 显然非空（例如 $x \in A$）。根据**确界原理**，$A$ 有上确界，记 $s = \sup A$。

由确界的定义，$s - x$ 不是 $A$ 的上界（因为 $s$ 是最小上界，而 $x > 0$）。因此存在 $n_0 \in \mathbb{N}^+$ 使得 $n_0 \cdot x > s - x$。

整理得：
$$(n_0 + 1) \cdot x > s.$$

但 $(n_0 + 1) \cdot x \in A$，这与 $s$ 是 $A$ 的上界矛盾。

因此假设不成立，标准形式成立。

**第四部分：整数形式 ⟹ 有理数稠密性。**

设 $a < b$ 为任意实数。我们需要找有理数 $q$ 使得 $a < q < b$。

由 Archimedean 性质的标准形式（取 $x = b - a > 0$，$y = 1$），存在 $n \in \mathbb{N}^+$ 使得 $n(b - a) > 1$，即 $nb - na > 1$。

这意味着区间 $(na, nb)$ 的长度大于 1。由整数形式，存在整数 $m$ 使得 $m - 1 \leq na < m$。于是：
$$na < m \leq na + 1 < nb.$$

最后一步利用了 $nb - na > 1$。两边除以 $n > 0$ 得：
$$a < \frac{m}{n} < b.$$

令 $q = \frac{m}{n} \in \mathbb{Q}$，则 $a < q < b$。有理数稠密性得证。

$\square$

---

> **双语对照**（Archimedean 性质）:
>
> ```lean4
> -- Archimedean 性质：对任意正实数 x 和 y，存在自然数 n 使得 n * x > y
> theorem archimedean_property (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
>     ∃ n : ℕ, y < n * x := by
>   /- 利用实数的 Archimedean 结构 -/
>   rcases Archimedean.arch y hx with ⟨n, hn⟩
>   use n
>   exact hn
>
> -- 等价表述：对任意实数 x，存在自然数 n 使得 n > x
> theorem archimedean_nat (x : ℝ) : ∃ n : ℕ, x < n := by
>   rcases exists_nat_gt x with ⟨n, hn⟩
>   use n
>   exact hn
>
> -- 有理数在实数中稠密（由 Archimedean 性质导出）
> theorem rationals_dense (x y : ℝ) (hxy : x < y) :
>     ∃ q : ℚ, x < q ∧ q < y := by
>   exact exists_rat_btwn hxy
> ```

---

## 三、典型例题

### 例题 3.1

**题目**: 设 $S = \{x \in \mathbb{R} : x^2 < 2\}$。证明 $\sup S = \sqrt{2}$，且 $S$ 没有最大元。

**解答**:

**步骤 1：证明 $\sqrt{2}$ 是 $S$ 的上界。**

对任意 $x \in S$，由定义 $x^2 < 2$。若 $x > 0$，则 $x^2 < 2 = (\sqrt{2})^2$，因两边均为正，开方得 $x < \sqrt{2}$。若 $x \leq 0$，则显然 $x \leq 0 < \sqrt{2}$。因此对所有 $x \in S$ 有 $x \leq \sqrt{2}$，$\sqrt{2}$ 是上界。

**步骤 2：证明 $\sqrt{2}$ 是最小上界。**

设 $\varepsilon > 0$ 为任意正数。我们需要找到 $x_\varepsilon \in S$ 使得 $x_\varepsilon > \sqrt{2} - \varepsilon$。

取 $x_\varepsilon = \sqrt{2} - \varepsilon/2$。若 $\varepsilon$ 足够小（例如 $\varepsilon < 2\sqrt{2}$），则 $x_\varepsilon > 0$。此时：
$$x_\varepsilon^2 = \left(\sqrt{2} - \frac{\varepsilon}{2}\right)^2 = 2 - \varepsilon\sqrt{2} + \frac{\varepsilon^2}{4}.$$

我们需要 $x_\varepsilon^2 < 2$，即 $-\varepsilon\sqrt{2} + \frac{\varepsilon^2}{4} < 0$，等价于 $\varepsilon < 4\sqrt{2}$。

若 $\varepsilon \geq 4\sqrt{2}$，则 $\sqrt{2} - \varepsilon < -\sqrt{2} < 0$，此时直接取 $x_\varepsilon = 0 \in S$（因 $0^2 = 0 < 2$），则 $x_\varepsilon = 0 > \sqrt{2} - \varepsilon$。

综上，对任意 $\varepsilon > 0$，总能找到 $x_\varepsilon \in S$ 使得 $x_\varepsilon > \sqrt{2} - \varepsilon$。因此 $\sqrt{2}$ 是最小上界，即 $\sup S = \sqrt{2}$。

**步骤 3：证明 $S$ 没有最大元。**

假设 $S$ 有最大元 $M = \max S$。则 $M \in S$ 且对所有 $x \in S$ 有 $x \leq M$。由最大元的定义，$M$ 也是上界，且 $M \in S$，故 $M \leq \sup S = \sqrt{2}$。

但 $M \in S$ 意味着 $M^2 < 2$。由有理数（或实数）的稠密性，存在实数 $y$ 使得 $M < y < \sqrt{2}$。取 $y = \frac{M + \sqrt{2}}{2}$，则：
$$M < y < \sqrt{2} \implies y^2 < 2 \implies y \in S.$$

这与 $M$ 是最大元矛盾（因为 $y > M$ 且 $y \in S$）。因此 $S$ 没有最大元。

$\square$

**关键步骤解析**: 本题的核心技巧在于利用**均值插值**构造一个比假设的最大元更大但仍属于集合的元素。$y = \frac{M + \sqrt{2}}{2}$ 这个构造是证明"开区间型"集合无最大元的标准技巧。

---

### 例题 3.2

**题目**: 构造一个有上界但没有最大元的非空实数集，并验证其上确界的存在性。

**解答**:

**构造**: 令 $T = \{1 - \frac{1}{n} : n \in \mathbb{N}^+\} = \{0, \frac{1}{2}, \frac{2}{3}, \frac{3}{4}, \frac{4}{5}, \ldots\}$。

**验证有上界**: 对任意 $n \in \mathbb{N}^+$，$1 - \frac{1}{n} < 1$，故 $1$ 是 $T$ 的一个上界。

**验证无最大元**: 假设 $M = \max T$ 存在。则存在 $n_0 \in \mathbb{N}^+$ 使得 $M = 1 - \frac{1}{n_0}$。但考虑元素 $1 - \frac{1}{n_0 + 1} \in T$：
$$1 - \frac{1}{n_0 + 1} = \frac{n_0}{n_0 + 1} > \frac{n_0 - 1}{n_0} = 1 - \frac{1}{n_0} = M.$$

这与 $M$ 是最大元矛盾。故 $T$ 没有最大元。

**验证上确界存在且 $\sup T = 1$**:

- **上界性**: 已验证 $1$ 是上界。
- **最小性**: 对任意 $\varepsilon > 0$，由 Archimedean 性质，存在 $n \in \mathbb{N}^+$ 使得 $n > \frac{1}{\varepsilon}$，即 $\frac{1}{n} < \varepsilon$。于是：
  $$1 - \frac{1}{n} > 1 - \varepsilon.$$
  而 $1 - \frac{1}{n} \in T$，故 $1$ 是最小上界。

因此 $\sup T = 1$，但 $\max T$ 不存在。

$\square$

**关键步骤解析**: 本题的构造利用了序列 $1 - \frac{1}{n}$ 单调递增趋向于 1 的特性。Archimedean 性质在这里直接用于验证确界的最小性——这是 Archimedean 性质的典型应用场景。

---

## 四、常见误区与纠正

### 误区 4.1: "上确界就是最大值"

**错误观点**: 许多初学者认为，如果一个集合有上确界，那么这个上确界一定在集合内部，即集合一定有最大值。这种混淆在直觉上很自然地发生，因为有限集合中"最大的那个数"既是最小上界也是最大元。

**反例或纠正**:

考虑开区间 $S = (0, 1) = \{x \in \mathbb{R} : 0 < x < 1\}$。

- **$\sup S = 1$**: 对任意 $x \in S$ 有 $x < 1$，故 $1$ 是上界。对任意 $\varepsilon > 0$，取 $x_\varepsilon = \max\{\frac{1}{2}, 1 - \frac{\varepsilon}{2}\}$，则 $x_\varepsilon \in S$ 且 $x_\varepsilon > 1 - \varepsilon$。故 $\sup S = 1$。
- **$\max S$ 不存在**: 假设 $M = \max S$ 存在，则 $M < 1$。取 $y = \frac{M + 1}{2}$，则 $M < y < 1$，故 $y \in S$ 且 $y > M$，矛盾。

因此 $\sup S = 1 \notin S$，最大值不存在。

再考虑例题 3.2 中的 $T = \{1 - \frac{1}{n} : n \in \mathbb{N}^+\}$。这里 $\sup T = 1$，但 $1 \notin T$，故最大值不存在。

> **为什么错**: 最大值要求元素**属于**集合，而上确界只要求是"最紧的上界"。对于"开放"的集合（如开区间或收敛到极限点但不包含极限点的序列），极限点本身不在集合中，但它仍然是最小上界。确界原理保证了上确界的存在性，但**不保证**该上确界落在原集合内。这一区别是实分析中许多反例的基础，也是理解闭集、紧集等概念的关键。

---

## 五、思想方法提炼

**本章核心思想**:

1. **完备性是分析的根基**: 确界原理是实数完备性的核心表述。没有完备性，单调有界序列可能不收敛，连续函数可能在闭区间上取不到最大值，微积分基本定理将失去支撑。确界原理、单调收敛原理、区间套定理、有限覆盖定理、聚点原理——这些表述在 $\mathbb{R}$ 中彼此等价，共同构成了分析学的逻辑基础。

2. **$\varepsilon$-语言刻画"无限接近"**: 确界定义中的"对任意 $\varepsilon > 0$，存在 $x_\varepsilon \in S$ 使得 $x_\varepsilon > s - \varepsilon$"是分析学中第一次出现的 $\varepsilon$-语言。它精确刻画了"无限接近"这一直觉概念，是后续极限、连续性、可微性、可积性定义的模板。

3. **构造性证明与反证法的结合**: 确界原理的证明（戴德金分割）是构造性的——我们实际"造出了"上确界；Archimedean 性质的证明则是反证法的典范——假设性质不成立，利用确界原理导出矛盾。两种证明技巧在分析学中交替使用，各有优势。

**与后续章节的联系**:

- **单调收敛原理**（下一章）: 单调有界序列必收敛，其证明直接依赖确界原理。
- **Bolzano-Weierstrass 定理**: 有界序列必有收敛子列，依赖确界原理构造收敛子列。
- **闭区间上连续函数的性质**（极值定理、介值定理）: 极值定理的证明需要确界原理来定位"最大值的候选点"。
- **级数理论**: 比较判别法、比值判别法等收敛判别法，其底层逻辑都建立在实数完备性之上。

---

## 六、习题

### 习题 6.1

**题目**: 设 $A, B \subseteq \mathbb{R}$ 均为非空有上界的集合。定义 $A + B = \{a + b : a \in A, b \in B\}$。证明：
$$\sup(A + B) = \sup A + \sup B.$$

**提示**: 先证 $\sup A + \sup B$ 是 $A + B$ 的上界；再证它是**最小**上界——对任意 $\varepsilon > 0$，分别在 $A$ 和 $B$ 中找到元素，使其和超过 $(\sup A + \sup B) - \varepsilon$。

**解答**:

令 $\alpha = \sup A$，$\beta = \sup B$。

**上界性**: 对任意 $x \in A + B$，存在 $a \in A$，$b \in B$ 使得 $x = a + b$。因 $a \leq \alpha$，$b \leq \beta$，故 $x = a + b \leq \alpha + \beta$。因此 $\alpha + \beta$ 是 $A + B$ 的上界。

**最小性**: 设 $\varepsilon > 0$。由确界定义：

- 存在 $a_\varepsilon \in A$ 使得 $a_\varepsilon > \alpha - \frac{\varepsilon}{2}$；
- 存在 $b_\varepsilon \in B$ 使得 $b_\varepsilon > \beta - \frac{\varepsilon}{2}$。

于是 $a_\varepsilon + b_\varepsilon \in A + B$ 且：
$$a_\varepsilon + b_\varepsilon > \left(\alpha - \frac{\varepsilon}{2}\right) + \left(\beta - \frac{\varepsilon}{2}\right) = \alpha + \beta - \varepsilon.$$

因此 $\alpha + \beta$ 是最小上界，$\sup(A + B) = \alpha + \beta$。

$\square$

---

### 习题 6.2

**题目**: 利用 Archimedean 性质证明：对任意实数 $x > 0$，存在唯一的整数 $n \in \mathbb{Z}$ 使得 $n \leq x < n + 1$（此 $n$ 称为 $x$ 的**整数部分**，记作 $\lfloor x \rfloor$）。

**提示**: 考虑集合 $S = \{m \in \mathbb{Z} : m \leq x\}$，证明 $S$ 非空有上界，从而有最大元。

**解答**:

**存在性**:

由 Archimedean 性质的整数形式，存在 $k \in \mathbb{Z}$ 使得 $k > x$，故 $k$ 是 $S = \{m \in \mathbb{Z} : m \leq x\}$ 的一个上界。

又由 Archimedean 性质（取负值），存在 $l \in \mathbb{Z}$ 使得 $l < -x$，即 $-l > x$，故 $-l - 1 \leq x$（否则 $-l > x + 1 > x$，但这不直接给出下界）。更直接地，由整数形式的 Archimedean 性质，存在 $n_0 \in \mathbb{Z}$ 使得 $n_0 > -x$，即 $-n_0 < x$，故 $-n_0 \in S$（若 $-n_0$ 为整数）。实际上 $-n_0$ 是整数且 $-n_0 < x$，但我们需要 $m \leq x$。取 $m = \lfloor -x \rfloor - 1$ 或更简单地：由 Archimedean 性质，存在 $N \in \mathbb{N}$ 使得 $N > |x|$，则 $-N < x$，且 $-N \in \mathbb{Z}$，$-N \leq x$，故 $S$ 非空。

因此 $S$ 是非空有上界的整数集。由整数的良序性（或确界原理：$S$ 作为 $\mathbb{R}$ 的子集有上确界 $s$，证明 $s \in S$ 且 $s$ 是整数），$S$ 有最大元 $n = \max S$。

由 $n \in S$ 得 $n \leq x$。由 $n$ 是最大元，$n + 1 \notin S$，故 $n + 1 > x$。因此 $n \leq x < n + 1$。

**唯一性**: 若 $n_1, n_2 \in \mathbb{Z}$ 都满足 $n_i \leq x < n_i + 1$，则 $n_1 \leq x < n_2 + 1$，故 $n_1 \leq n_2$；同理 $n_2 \leq n_1$。因此 $n_1 = n_2$。

$\square$

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
