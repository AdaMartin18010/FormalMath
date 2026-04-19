---
title: 确界原理与 Archimedean 性质
msc_primary: 26A99
course: MIT 18.100A Real Analysis
level: silver
target_courses:
- MIT 18.100A
difficulty: 核心定理
importance: 极高
prerequisites:
- 实数定义
- 集合论基础
- 不等式技巧
related:
- 单调收敛定理
- 区间套定理
- Cauchy收敛准则
tags:
- 实分析
- 实数完备性
- 确界
- Archimedean
- 核心定理
date: 2026-04-17
references:
  textbooks:
  - id: rudin_pma
    type: textbook
    title: Principles of Mathematical Analysis
    authors:
    - Walter Rudin
    publisher: McGraw-Hill
    edition: 3rd
    year: 1976
    isbn: 978-0070542358
    msc: 26-01
    chapters:
    - 'Chapter 1: The Real and Complex Number Systems'
    url: null
    pages: 1-5
  databases:
  - id: nlab
    type: database
    name: nLab
    entry_url: https://ncatlab.org/nlab/show/{entry}
    consulted_at: 2026-04-17
  - id: stacks_project
    type: database
    name: Stacks Project
    entry_url: https://stacks.math.columbia.edu/tag/{tag}
    consulted_at: 2026-04-17
  - id: zbmath
    type: database
    name: zbMATH Open
    entry_url: https://zbmath.org/?q=an:{zb_id}
    consulted_at: 2026-04-17
---

# 确界原理与 Archimedean 性质

## 一、确界原理

### 定理陈述

**定理（确界原理 / Supremum Principle）**：设 $S
eq \emptyset$ 是 $\mathbb{R}$ 的一个子集，且 $S$ 有上界，则 $S$ 在 $\mathbb{R}$ 中必存在**上确界**（least upper bound / supremum）。即：

$$\exists \alpha \in \mathbb{R} \text{ 使得 } \alpha = \sup S$$

**定义（上确界）**：$\alpha = \sup S$ 当且仅当满足以下两个条件：

1. **上界性**：$\forall x \in S, \, x \leq \alpha$
2. **最小性**：$\forall \varepsilon > 0, \, \exists x \in S \text{ 使得 } x > \alpha - \varepsilon$

等价地，最小性也可表述为：若 $\beta < \alpha$，则 $\beta$ 不是 $S$ 的上界（即 $\exists x \in S$ 使得 $x > \beta$）。

---

### 证明思路

确界原理是实数完备性的**核心公理**。从公理化角度，它可以作为实数域的完备性公理之一。如果我们从**Dedekind 分割**构造实数，则确界原理是定理；如果采用**完备有序域公理化**定义实数，则确界原理是公理。

本证明采用经典的**区间套二分法**，它直接体现了实数轴"无空隙"的本质：

1. 从一个包含 $S$ 中元素的区间和一个上界出发
2. 反复二分区间，选择"仍然包含上界"且"包含 $S$ 中元素"的那一半
3. 利用区间套定理（它本身依赖完备性）得到唯一的极限点
4. 证明该极限点满足上确界的两个条件

---

### 详细证明

**给定**：$S \subseteq \mathbb{R}$，$S \neq \emptyset$，且 $S$ 有上界。设 $M$ 是 $S$ 的一个上界，$a \in S$ 是 $S$ 中的一个元素。

**目标**：证明 $\sup S$ 存在。

---

#### 步骤 1：构造初始区间

令 $I_0 = [a_0, b_0] = [a, M]$。

**性质**：

- $I_0$ 包含 $S$ 中至少一个元素（因为 $a \in S$）
- $b_0 = M$ 是 $S$ 的上界

---

#### 步骤 2：递归构造区间套

假设已构造区间 $I_n = [a_n, b_n]$，满足：

- $I_n$ 包含 $S$ 中至少一个元素
- $b_n$ 是 $S$ 的上界

**二分操作**：令 $c_n = \dfrac{a_n + b_n}{2}$。

**选择规则**：

- 若 $c_n$ 是 $S$ 的上界，则令 $I_{n+1} = [a_n, c_n]$
- 若 $c_n$ **不是** $S$ 的上界，则存在 $s \in S$ 使得 $s > c_n$。此时令 $I_{n+1} = [c_n, b_n]$

**验证归纳假设**：

- **情形 1**（$c_n$ 是上界）：$I_{n+1} = [a_n, c_n]$。由于 $a_n$ 所在的一侧不变，$I_{n+1}$ 仍包含 $S$ 中元素（因为 $a_n \leq a$ 不一定，但 $a_n$ 是由之前步骤保证的）。更准确地说，由于 $a_n$ 在情形 2 中会被更新为 $c_{n-1}$（一个非上界点之下的值），我们需要更精细的论证：

  实际上，由归纳假设，$I_n$ 的左端点 $a_n$ 要么等于 $a$（初始），要么等于某个 $c_k$（在步骤 $k$ 中 $c_k$ 不是上界）。因此 $a_n$ 本身不是 $S$ 的上界，故 $I_n$ 中必包含 $S$ 的元素。在情形 1 中，$I_{n+1} = [a_n, c_n] \subseteq I_n$，因此 $I_{n+1}$ 仍包含 $S$ 中元素。同时 $c_n$ 是上界，故 $b_{n+1} = c_n$ 是上界。

- **情形 2**（$c_n$ 不是上界）：$I_{n+1} = [c_n, b_n]$。由于 $c_n$ 不是上界，存在 $s \in S$ 使得 $s > c_n$，故 $s \in [c_n, b_n] = I_{n+1}$（因为 $b_n$ 是上界，$s \leq b_n$）。同时 $b_{n+1} = b_n$ 仍是上界。

因此归纳假设对 $I_{n+1}$ 成立。

---

#### 步骤 3：应用区间套定理

**区间套性质**：
$$I_0 \supseteq I_1 \supseteq I_2 \supseteq \cdots$$
$$|I_n| = b_n - a_n = \frac{M - a}{2^n} \to 0 \quad (n \to \infty)$$

由**区间套定理**，存在唯一的 $\alpha \in \mathbb{R}$ 使得：
$$\bigcap_{n=0}^{\infty} I_n = \{\alpha\}$$

---

#### 步骤 4：证明 $\alpha$ 是 $S$ 的上界

**反证法**：假设 $\alpha$ 不是上界，则存在 $s \in S$ 使得 $s > \alpha$。

令 $\delta = s - \alpha > 0$。取 $n$ 足够大使得 $|I_n| = \dfrac{M-a}{2^n} < \delta$。

由于 $\alpha \in I_n = [a_n, b_n]$，有 $b_n - \alpha \leq |I_n| < \delta = s - \alpha$。

因此 $b_n < s$。但这与"$b_n$ 是 $S$ 的上界"矛盾！

故 $\alpha$ 是 $S$ 的上界。

---

#### 步骤 5：证明 $\alpha$ 是最小上界

**给定**：任意 $\varepsilon > 0$。

取 $n$ 足够大使得 $|I_n| = \dfrac{M-a}{2^n} < \varepsilon$。

由于 $\alpha \in I_n = [a_n, b_n]$，有 $\alpha - a_n \leq |I_n| < \varepsilon$，即：
$$a_n > \alpha - \varepsilon$$

**关键观察**：在构造过程中，$a_n$ **永远不是** $S$ 的上界（若 $a_n = a$，显然不是；若 $a_n = c_k$ 对某个 $k$，则由情形 2 的选取规则，$c_k$ 不是上界）。

因此，存在 $s \in S$ 使得 $s > a_n > \alpha - \varepsilon$。

这正满足了上确界的最小性条件。

**结论**：$\alpha = \sup S$ 存在。∎

---

## 二、Archimedean 性质

### 定理陈述

**定理（Archimedean 性质）**：对于任意正实数 $x, y > 0$，存在自然数 $n \in \mathbb{N}$ 使得：

$$n \cdot x > y$$

等价表述：

- 自然数集 $\mathbb{N}$ 在 $\mathbb{R}$ 中**无上界**
- 对任意 $\varepsilon > 0$，存在 $n \in \mathbb{N}$ 使得 $\dfrac{1}{n} < \varepsilon$

---

### 证明思路

Archimedean 性质看起来"显然"，但它**不能**仅由有序域的公理推出——它依赖于实数的**完备性**（即确界原理）。

本证明采用反证法：假设 $\mathbb{N}$ 有上界，则由确界原理存在最小上界 $\alpha = \sup \mathbb{N}$。但 $\alpha - 1$ 不再是上界，故存在 $n \in \mathbb{N}$ 使得 $n > \alpha - 1$，从而 $n + 1 > \alpha$，与 $\alpha$ 是上界矛盾。

---

### 详细证明

**目标**：证明 $\mathbb{N}$ 在 $\mathbb{R}$ 中无上界。

**反证法**：假设 $\mathbb{N}$ 有上界。

由于 $\mathbb{N} \neq \emptyset$ 且有上界，由**确界原理**，存在 $\alpha = \sup \mathbb{N} \in \mathbb{R}$。

**应用最小性**：取 $\varepsilon = 1 > 0$。由上确界的最小性，存在 $n \in \mathbb{N}$ 使得：
$$n > \alpha - 1$$

**推导**：
$$n + 1 > \alpha$$

但 $n \in \mathbb{N}$ 蕴含 $n + 1 \in \mathbb{N}$。因此 $n + 1 > \alpha$ 与"$\alpha$ 是 $\mathbb{N}$ 的上界"矛盾！

**结论**：$\mathbb{N}$ 在 $\mathbb{R}$ 中无上界。∎

**推论（标准形式）**：对任意 $x, y > 0$，由于 $\dfrac{y}{x}$ 不是 $\mathbb{N}$ 的上界，存在 $n \in \mathbb{N}$ 使得：
$$n > \frac{y}{x} \quad \Rightarrow \quad n \cdot x > y$$

---

## 三、与 Lean4 形式化的对应

确界原理和 Archimedean 性质在 Mathlib4 中有直接实现：

```lean4
import Mathlib

open Set Real

-- 确界原理：非空有上界的实数集必有上确界
theorem supremum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ α : ℝ, IsLUB S α := by
  -- 这是实数域作为完备有序域的直接推论
  exact Real.exists_isLUB hne hbdd
```

```lean4
-- Archimedean 性质：自然数在实数中无上界
theorem archimedean_property (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∃ n : ℕ, y < n * x := by
  -- 利用实数的 Archimedean 性质
  rcases exists_nat_gt (y / x) with ⟨n, hn⟩
  use n
  have : y / x < (n : ℝ) := hn
  have : y < (n : ℝ) * x := by
    apply (lt_div_iff' hx).mp at this
    linarith
  linarith
```

### 关键对应点

| 数学概念 | Lean4 对应 |
|---------|-----------|
| 上确界 | `IsLUB` (Least Upper Bound) |
| 有上界 | `BddAbove` |
| 非空 | `Set.Nonempty` |
| Archimedean 性质 | `exists_nat_gt` |

---

## 四、典型例题

### 例题 1：证明 $\sqrt{2}$ 存在

**问题**：证明存在正实数 $x$ 使得 $x^2 = 2$。

**证明**：

令 $S = \{r \in \mathbb{R} : r \geq 0, \, r^2 < 2\}$。

1. **非空**：$1 \in S$（因为 $1^2 = 1 < 2$）
2. **有上界**：$2$ 是上界（若 $r > 2$，则 $r^2 > 4 > 2$，故 $r \notin S$）

由**确界原理**，$x = \sup S$ 存在。下面证明 $x^2 = 2$。

**反证法**：

- **假设 $x^2 < 2$**：取 $\varepsilon = \min\left\{1, \dfrac{2 - x^2}{2x + 1}\right\} > 0$。则：
  $$(x + \varepsilon)^2 = x^2 + 2x\varepsilon + \varepsilon^2 \leq x^2 + 2x\varepsilon + \varepsilon = x^2 + \varepsilon(2x + 1) \leq x^2 + (2 - x^2) = 2$$
  因此 $x + \varepsilon \in S$，与 $x = \sup S$ 矛盾。

- **假设 $x^2 > 2$**：取 $\varepsilon = \dfrac{x^2 - 2}{2x} > 0$。则：
  $$(x - \varepsilon)^2 = x^2 - 2x\varepsilon + \varepsilon^2 > x^2 - 2x\varepsilon = x^2 - (x^2 - 2) = 2$$
  因此 $x - \varepsilon$ 是 $S$ 的上界（因为对所有 $r \in S$，$r^2 < 2 < (x - \varepsilon)^2$ 蕴含 $r < x - \varepsilon$）。这与 $x$ 是最小上界矛盾。

故 $x^2 = 2$。∎

---

### 例题 2：证明 $\dfrac{1}{n} \to 0$

**问题**：用 Archimedean 性质证明数列 $\left\{\dfrac{1}{n}\right\}$ 收敛于 $0$。

**证明**：

给定任意 $\varepsilon > 0$。

由 Archimedean 性质（取 $x = \varepsilon, y = 1$），存在 $N \in \mathbb{N}$ 使得：
$$N \cdot \varepsilon > 1 \quad \Rightarrow \quad \frac{1}{N} < \varepsilon$$

对任意 $n \geq N$：
$$\left|\frac{1}{n} - 0\right| = \frac{1}{n} \leq \frac{1}{N} < \varepsilon$$

由收敛定义，$\displaystyle\lim_{n \to \infty} \frac{1}{n} = 0$。∎

---

## 五、常见误区分析

### ❌ 误区：混淆"上确界"与"最大值"

**错误陈述**："有上界的集合必有最大值。"

**纠正**：上确界是**最小上界**，它不一定被集合中的元素取到。只有当上确界 $\sup S \in S$ 时，它才称为最大值 $\max S$。

**反例**：

- 集合 $S = (0, 1)$ 的上确界是 $\sup S = 1$，但 $S$ 没有最大值（因为 $1 \notin S$）
- 集合 $T = \left\{1 - \dfrac{1}{n} : n \in \mathbb{N}\right\}$ 的上确界是 $\sup T = 1$，但 $1 \notin T$

**正确关系**：
$$\max S \text{ 存在} \Rightarrow \max S = \sup S$$
但逆命题不成立。

---

## 六、关键洞察

1. **确界原理 = 完备性的核心**：所有其他完备性定理（单调收敛、区间套、Bolzano-Weierstrass、Cauchy 准则）都可以从确界原理推导出来。

2. **Archimedean 性质依赖完备性**：虽然 Archimedean 性质看起来"显然"，但确实存在**非 Archimedean 有序域**（如有理函数域按某种序结构）。在实数中它成立，是因为我们要求了完备性。

3. **稠密性的来源**：由 Archimedean 性质可推出**有理数在实数中稠密**——对任意实数 $x < y$，存在有理数 $q$ 使得 $x < q < y$。

---

*文档版本: 1.0 | 创建日期: 2026-04-17 | 对应课程: MIT 18.100A*


## 习题

**习题 1.1**。求集合 $S = \\{1/n : n \\in \\mathbb{N}\\}$ 的上确界和下确界。

*解答*：$\\sup S = 1$（最大元），$\\inf S = 0$（0是下界，且对任意 $\\epsilon > 0$，存在 $n$ 使 $1/n < \\epsilon$）。$\\square$

---

**习题 1.2**。用 Archimedean 性质证明 $\\mathbb{Q}$ 在 $\\mathbb{R}$ 中稠密。

*解答*：对任意 $a < b$，需找有理数 $q \\in (a,b)$。由 Archimedean 性质，存在 $n$ 使 $1/n < b-a$。再取 $m = \\lfloor na \\rfloor + 1$，则 $a < m/n < b$。$\\square$
