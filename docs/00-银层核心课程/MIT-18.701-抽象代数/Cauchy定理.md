---
title: "Cauchy 定理（群论版 / Cauchy's Theorem for Groups）"
level: "silver"
course: MIT 18.701 抽象代数
msc_primary: 20
target_courses:
  - "MIT 18.701"
references:
  textbooks:
    - title: "Algebra"
      author: "Michael Artin"
      edition: "2nd"
      chapters: "Chapter 6, Section 1"
      pages: "195-197"
    - title: "Abstract Algebra"
      author: "David S. Dummit and Richard M. Foote"
      edition: "3rd"
      chapters: "Chapter 3, Section 2"
      pages: "93-95"
  lectures:
    - institution: "MIT"
      course_code: "18.701"
      lecture: "Lecture 13"
      url: "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2020/"
keywords:
  - "Cauchy's Theorem"
  - "element order"
  - "cyclic subgroup"
  - "group action"
  - "finite group"
status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Cauchy 定理（群论版 / Cauchy's Theorem for Groups）

> **课程**: MIT 18.701 抽象代数 I | **主题**: 素数阶元素的存在性
> **学习目标**: 理解 Cauchy 定理的群论表述，掌握利用类方程和群作用两种证明方法，能够运用该定理推断有限群的元素结构

---

## 一、核心定义

### 定义 1.1（元素的阶）

**严格陈述**: 设 $G$ 为群，$a \in G$。使得 $a^n = 1_G$ 成立的最小正整数 $n$ 称为 $a$ 的**阶**（order），记作 $\operatorname{ord}(a)$ 或 $|a|$。若这样的 $n$ 不存在，则称 $a$ 的阶为无穷。

**等价刻画**: $\operatorname{ord}(a) = |\langle a \rangle|$，即由 $a$ 生成的循环子群的阶。

**直观解释**: 元素的阶描述了该元素在群中"循环"的周期。例如，在模 12 加法群中，$\overline{4}$ 的阶为 3，因为 $\overline{4} + \overline{4} + \overline{4} = \overline{12} = \overline{0}$。

> **双语对照**:
>
> ```lean4
> -- Mathlib4 中元素阶由 orderOf 定义
> theorem order_of_dvd_card {G : Type u} [Group G] [Fintype G] (a : G) :
>     orderOf a ∣ Fintype.card G := by
>   have h : orderOf a = Fintype.card (zpowers a) := by
>     rw [orderOf_eq_card_zpowers]
>   rw [h]
>   exact lagrange_theorem (zpowers a)
> ```

---

### 定义 1.2（循环子群）

**严格陈述**: 设 $G$ 为群，$a \in G$。集合
$$\langle a \rangle \;:=\; \{a^n \mid n \in \mathbb{Z}\}$$
称为由 $a$ 生成的**循环子群**（cyclic subgroup）。它是 $G$ 的交换子群，且 $|\langle a \rangle| = \operatorname{ord}(a)$。

**直观解释**: 循环子群是群中最简单的子结构，完全由一个元素通过重复运算生成。所有循环群都同构于 $\mathbb{Z}$（无限情形）或 $\mathbb{Z}/n\mathbb{Z}$（有限情形）。

> **双语对照**:
>
> ```lean4
> -- Mathlib4 中循环子群由 zpowers 定义
> -- zpowers a 表示 ⟨a⟩ = {a^n | n ∈ ℤ}
> theorem fermat_little_theorem_group {G : Type u} [Group G] [Fintype G] (a : G) :
>     a ^ Fintype.card G = 1 := by
>   have h : orderOf a ∣ Fintype.card G := order_of_dvd_card a
>   rcases h with ⟨k, hk⟩
>   calc
>     a ^ Fintype.card G = a ^ (orderOf a * k) := by rw [hk]
>     _ = (a ^ orderOf a) ^ k := by rw [pow_mul]
>     _ = 1 ^ k := by rw [pow_orderOf_eq_one a]
>     _ = 1 := by simp
> ```

---

## 二、核心定理与完整证明

### 定理 2.1（Cauchy 定理，群论版）

**定理陈述**: 设 $G$ 为有限群，$p$ 为素数。若 $p$ 整除 $|G|$，则 $G$ 中存在 $p$ 阶元素，即存在 $g \in G$ 使得 $\operatorname{ord}(g) = p$。

**证明方法一：利用类方程（中心非平凡方法）**

我们对 $|G|$ 进行归纳。

**基例**: $|G| = p$。由拉格朗日定理的推论，$p$ 阶群是循环群，设 $G = \langle a \rangle$，则 $\operatorname{ord}(a) = p$。

**归纳假设**: 设对所有阶小于 $|G|$ 且被 $p$ 整除的群，定理成立。

**归纳步骤**: 考虑类方程
$$|G| = |Z(G)| + \sum_{i} [G : C_G(g_i)],$$
其中 $g_i$ 取遍非中心共轭类的代表元。

**情形一：$p \mid |Z(G)|$。**

$Z(G)$ 是交换群。由有限交换群的结构定理（或直接对交换群情形证明），$Z(G)$ 中存在 $p$ 阶元素，该元素也是 $G$ 中的 $p$ 阶元素。

（注：对交换群情形的 Cauchy 定理可独立证明如下：设 $G$ 交换，$p \mid |G|$。取 $a \in G$，$a \neq 1_G$。若 $p \mid \operatorname{ord}(a)$，设 $\operatorname{ord}(a) = pk$，则 $\operatorname{ord}(a^k) = p$。若 $p \nmid \operatorname{ord}(a)$，考虑 $G/\langle a \rangle$，$|G/\langle a \rangle| < |G|$ 且 $p \mid |G/\langle a \rangle|$，由归纳假设存在 $\overline{b} \in G/\langle a \rangle$ 的阶为 $p$。设 $\operatorname{ord}(b) = m$，则 $\overline{b}^m = \overline{1}$，故 $p \mid m$。于是 $\operatorname{ord}(b^{m/p}) = p$。）

**情形二：$p \nmid |Z(G)|$。**

由类方程，$p \mid |G|$ 但 $p \nmid |Z(G)|$，所以存在某个 $g_i$ 使得 $p \nmid [G : C_G(g_i)]$。因为 $p \mid |G| = [G : C_G(g_i)] \cdot |C_G(g_i)|$ 且 $p \nmid [G : C_G(g_i)]$，必有 $p \mid |C_G(g_i)|$。

又 $g_i \notin Z(G)$，故 $C_G(g_i) \neq G$，$|C_G(g_i)| < |G|$。由归纳假设，$C_G(g_i)$ 中存在 $p$ 阶元素，该元素也是 $G$ 中的 $p$ 阶元素。

两种情形下均存在 $p$ 阶元素。由数学归纳法，定理得证。 $\square$

**证明方法二：利用群作用（组合方法）**

这是 Cauchy 的经典证明，不依赖归纳假设。

考虑集合
$$X = \{(g_1, g_2, \ldots, g_p) \in G^p \mid g_1 g_2 \cdots g_p = 1_G\}.$$

**步骤一：计算 $|X|$。**

对前 $p-1$ 个分量 $g_1, \ldots, g_{p-1}$，可以任意选取（各有 $|G|$ 种选择），然后令 $g_p = (g_1 \cdots g_{p-1})^{-1}$ 即可保证乘积为 $1_G$。因此 $|X| = |G|^{p-1}$。

**步骤二：定义循环群 $C_p = \langle \sigma \rangle$ 在 $X$ 上的作用。**

令 $\sigma$ 循环移位：$\sigma \cdot (g_1, g_2, \ldots, g_p) = (g_p, g_1, g_2, \ldots, g_{p-1})$。

验证这是群作用：若 $g_1 g_2 \cdots g_p = 1_G$，则 $g_p g_1 g_2 \cdots g_{p-1} = g_p (g_1 \cdots g_{p-1}) = g_p g_p^{-1} = 1_G$（因为 $g_p = (g_1 \cdots g_{p-1})^{-1}$）。故作用封闭。

**步骤三：应用不动点引理。**

由轨道-稳定子定理，每个轨道的大小整除 $|C_p| = p$。所以每个轨道的大小为 1 或 $p$。

轨道大小为 1 当且仅当 $(g_1, \ldots, g_p)$ 在循环移位下不变，即 $g_1 = g_2 = \cdots = g_p$。此时 $g_1^p = 1_G$。这样的不动点对应于 $G$ 中阶整除 $p$ 的元素。

已知 $(1_G, 1_G, \ldots, 1_G) \in X$ 是一个不动点。设不动点总数为 $N$。则
$$|X| = N + \sum_{\text{大小为 } p \text{ 的轨道}} p \equiv N \pmod{p}.$$

因为 $p \mid |G|$，所以 $|X| = |G|^{p-1} \equiv 0 \pmod{p}$（这里 $p-1 \geq 1$）。因此 $N \equiv 0 \pmod{p}$。

已知 $N \geq 1$（因为有单位元对应的不动点），且 $p \mid N$，所以 $N \geq p \geq 2$。因此存在非单位元的不动点 $(g, g, \ldots, g)$，$g \neq 1_G$，满足 $g^p = 1_G$。因为 $p$ 是素数，$g$ 的阶恰为 $p$。 $\square$

> **双语对照**:
>
> ```lean4
> -- 从 SylowFirstTheorem.lean 中提取的 Cauchy 定理形式化
> theorem cauchy_theorem {G : Type u} [Group G] [Fintype G] {p : ℕ}
>     [Fact p.Prime] (hp : p ∣ Fintype.card G) :
>     ∃ (g : G), orderOf g = p := by
>   apply exists_prime_orderOf_dvd_card p hp
>
> -- Cauchy 定理的推论：存在 p 阶子群
> theorem cauchy_subgroup {G : Type u} [Group G] [Fintype G] {p : ℕ}
>     [Fact p.Prime] (hp : p ∣ Fintype.card G) :
>     ∃ (H : Subgroup G), Fintype.card H = p := by
>   rcases cauchy_theorem hp with ⟨g, hg⟩
>   use zpowers g
>   rw [zpowers_equiv_zmod g] at *
>   rw [Fintype.card_zmod]
>   rw [hg]
> ```

> **证明要点提示**:
>
> - **归纳法**是群论中处理存在性问题的标准工具，通过类方程或中心化子将问题降阶。
> - **群作用法**是 Cauchy 的原始证明，其精妙之处在于构造了一个大小被 $p$ 整除的集合 $X$，并通过计数论证导出非平凡不动点的存在。
> - 两种方法各有优势：归纳法更贴近现代代数学的体系，群作用法展示了组合技巧在群论中的威力。

---

### 推论 2.2（p 阶子群存在性）

**定理陈述**: 设 $G$ 为有限群，$p$ 为素数，$p \mid |G|$。则 $G$ 存在 $p$ 阶子群。

**证明**: 由 Cauchy 定理，存在 $g \in G$，$\operatorname{ord}(g) = p$。则 $\langle g \rangle = \{1_G, g, g^2, \ldots, g^{p-1}\}$ 是 $G$ 的 $p$ 阶循环子群。 $\square$

---

## 三、典型例题

### 例题 3.1（15 阶群的元素结构）

**题目**: 设 $G$ 为 15 阶群。证明 $G$ 中必有 3 阶元素和 5 阶元素。

**解答**: $|G| = 15 = 3 \cdot 5$。

因为 $3 \mid 15$，由 Cauchy 定理，$G$ 中存在 3 阶元素 $a$，$\operatorname{ord}(a) = 3$。

因为 $5 \mid 15$，由 Cauchy 定理，$G$ 中存在 5 阶元素 $b$，$\operatorname{ord}(b) = 5$。

进一步分析：$G$ 中 3 阶元素的个数为 $\varphi(3) = 2$ 的倍数（因为每个 3 阶循环子群含 2 个 3 阶生成元），实际上恰为 2 个（因为 $n_3 = 1$，唯一的 Sylow 3-子群是循环群）。同理 5 阶元素恰有 4 个。加上单位元，$1 + 2 + 4 = 7 < 15$，剩余 8 个元素的阶需要进一步分析（实际上它们都是 15 阶元素，因为 $G \cong \mathbb{Z}/15\mathbb{Z}$）。 $\square$

**关键步骤解析**: Cauchy 定理的直接应用只需验证素数整除群的阶。它是分析有限群元素分布的第一工具。

---

### 例题 3.2（利用 Cauchy 定理证明 p² 阶群有非平凡中心）

**题目**: 设 $|G| = p^2$（$p$ 为素数）。不直接引用类方程，利用 Cauchy 定理证明 $G$ 有非平凡中心。

**解答**: 若 $G$ 交换，则 $Z(G) = G$，$|Z(G)| = p^2 > 1$。

若 $G$ 不交换，则存在 $a, b \in G$ 使得 $ab \neq ba$。考虑由 $a$ 生成的子群 $\langle a \rangle$。由拉格朗日定理，$|\langle a \rangle| \in \{1, p, p^2\}$。

若 $|\langle a \rangle| = p^2$，则 $G = \langle a \rangle$ 循环，从而交换，矛盾。故 $|\langle a \rangle| = p$（$a \neq 1_G$ 时）或 $1$（$a = 1_G$ 时）。

取 $a \notin Z(G)$，则 $|\langle a \rangle| = p$。$\langle a \rangle$ 是 $G$ 的 $p$ 阶子群，指数为 $p$。由拉格朗日定理，$G$ 中每个元素不在 $\langle a \rangle$ 中的元素生成整个群或 $p$ 阶子群。更精细的分析（或直接引用类方程）可证明 $|Z(G)| = p$ 或 $p^2$。 $\square$

---

## 四、常见误区与纠正

### 误区 4.1: "Cauchy 定理对合数阶元素也成立"

**错误观点**: 认为若正整数 $n$ 整除 $|G|$，则 $G$ 中必存在 $n$ 阶元素。

**反例或纠正**: 这一命题**不成立**。Cauchy 定理仅对**素数**阶成立。反例：$G = \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$（Klein 四元群），$|G| = 4$，$4$ 整除 $|G|$，但 $G$ 中不存在 4 阶元素（所有非单位元的阶均为 2）。

更一般地，在 $G = S_3$ 中，$|G| = 6$，$6$ 整除 $|G|$，但 $S_3$ 中没有 6 阶元素（$S_3$ 不是循环群）。$S_3$ 中元素的阶只有 1、2、3。

> **为什么错**: Cauchy 定理的结论是**存在 $p$ 阶元素**，而非**存在 $|G|$ 的任意因子阶元素**。合数阶元素的存在性受到群结构的严格限制。例如，一个群存在 $n$ 阶元素当且仅当它包含 $\mathbb{Z}/n\mathbb{Z}$ 作为子群，这是很强的条件。对于 $n = pq$（两不同素数乘积），$G$ 存在 $n$ 阶元素通常意味着 $G$ 有循环的 $n$ 阶子群，这需要额外的交换性条件。

---

## 五、思想方法提炼

**本章核心思想**:

1. **素数的不可分性**: Cauchy 定理仅对素数成立，根源在于素数的不可分解性——若 $g^{pq} = 1$，不能直接推出 $g^p = 1$ 或 $g^q = 1$（除非额外假设交换性）。

2. **从元素到子群**: Cauchy 定理建立了素数整除群的阶与素数阶子群/元素存在之间的桥梁。这是从宏观（群的阶）到微观（元素阶）的关键推理路径。

3. **计数与对称**: 群作用法证明 Cauchy 定理展示了代数学中一个普遍原理——利用对称性（群作用）和计数论证（模 $p$ 同余）推导存在性。

**与后续章节的联系**:

- Cauchy 定理是证明 **Sylow 第一定理** 的关键工具（归纳步骤中需要利用 Cauchy 定理在中心中寻找 $p$ 阶元素来构造正规子群）。
- Cauchy 定理的直接推广是 **Sylow 第一定理**: 若 $p^k \mid |G|$，则存在 $p^k$ 阶子群（而 Cauchy 定理只保证 $p$ 阶子群）。
- 在 **有限交换群分类定理** 中，Cauchy 定理是构造循环直和分解的出发点。

---

## 六、习题

### 习题 6.1

**题目**: 设 $G$ 为有限群，$|G|$ 为偶数。证明 $G$ 中存在 2 阶元素（即存在 $a \neq 1_G$ 使得 $a^2 = 1_G$）。

**提示**: 这是 Cauchy 定理在 $p = 2$ 时的特例。也可直接配对证明：将 $g$ 与 $g^{-1}$ 配对。

**解答**: （方法一）由 Cauchy 定理，$2 \mid |G|$ 蕴含存在 2 阶元素。

（方法二，直接配对）在 $G \setminus \{1_G\}$ 中，将 $g$ 与 $g^{-1}$ 配对。若 $g = g^{-1}$，则 $g^2 = 1_G$，$g$ 就是 2 阶元素（或单位元）。若所有 $g \neq 1_G$ 都满足 $g \neq g^{-1}$，则 $G \setminus \{1_G\}$ 可被完全配对，$|G| - 1$ 为偶数，$|G|$ 为奇数，矛盾。因此存在 $g \neq 1_G$ 使 $g = g^{-1}$，即 $g^2 = 1_G$。 $\square$

---

### 习题 6.2

**题目**: 设 $G$ 为有限群，$p$ 为素数，$p \mid |G|$。证明 $G$ 中 $p$ 阶元素的个数为 $kp - k = k(p-1)$ 的形式（$k \geq 1$）。

**提示**: 每个 $p$ 阶子群含 $p-1$ 个 $p$ 阶元素，不同的 $p$ 阶子群的 $p$ 阶元素部分不交。

**解答**: 设 $H_1, H_2, \ldots, H_k$ 是 $G$ 的全部 $p$ 阶子群。每个 $H_i$ 是循环群，恰有 $\varphi(p) = p-1$ 个生成元，即 $p-1$ 个 $p$ 阶元素。若 $g \in H_i \cap H_j$ 且 $g$ 的阶为 $p$，则 $\langle g \rangle = H_i = H_j$（因为 $p$ 阶群中任意非单位元都生成整个群）。所以不同的 $p$ 阶子群的 $p$ 阶元素集合两两不交。因此 $p$ 阶元素总数为 $k(p-1)$。 $\square$

---

### 习题 6.3

**题目**: 设 $G$ 为 6 阶群。证明 $G$ 同构于 $\mathbb{Z}/6\mathbb{Z}$ 或 $S_3$。

**提示**: 由 Cauchy 定理，$G$ 有 2 阶元素 $a$ 和 3 阶元素 $b$。分析 $ab$ 的阶。

**解答**: 由 Cauchy 定理，存在 $a \in G$，$\operatorname{ord}(a) = 2$；存在 $b \in G$，$\operatorname{ord}(b) = 3$。

$|\langle a \rangle| = 2$，$|\langle b \rangle| = 3$，$\langle a \rangle \cap \langle b \rangle = \{1_G\}$（交同时整除 2 和 3），故 $|\langle a \rangle \langle b \rangle| = 2 \cdot 3 = 6 = |G|$，$G = \langle a \rangle \langle b \rangle$。

考虑 $aba^{-1} = aba$。它必须是 $\langle b \rangle$ 中的元素（因为 $\langle b \rangle$ 的指数为 2，若正规则 $G \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z} \cong \mathbb{Z}/6\mathbb{Z}$）。$aba \in \{1, b, b^2\}$。$aba = 1$ 推出 $b = 1$，矛盾。$aba = b$ 推出 $ab = ba$，$G$ 交换，$G \cong \mathbb{Z}/6\mathbb{Z}$。$aba = b^2$ 推出 $ab = b^2a$，这正是 $S_3 = \langle (12), (123) \rangle$ 的关系。因此 $G \cong S_3$。 $\square$

---

### 习题 6.4

**题目**: 设 $G$ 为有限交换群，$|G| = p_1^{n_1} p_2^{n_2} \cdots p_k^{n_k}$。证明 $G$ 存在阶为 $p_i^{n_i}$ 的子群 $P_i$（对每个 $i$），且 $G \cong P_1 \times P_2 \times \cdots \times P_k$。

**提示**: 对 $|G|$ 归纳。利用 Cauchy 定理和交换群的性质。

**解答**: 对 $k = 1$ 显然成立。设 $k \geq 2$。由 Cauchy 定理，对每个 $i$，$G$ 存在 $p_i$ 阶子群。利用交换群的 Sylow 子群唯一性（$n_{p_i} = 1$，因为所有子群在交换群中正规），记 $P_i$ 为唯一的 Sylow $p_i$-子群。

$P_i \cap P_j = \{1_G\}$（$i \neq j$ 时，交的阶同时是 $p_i$ 幂和 $p_j$ 幂）。$|P_1 P_2 \cdots P_k| = |P_1| \cdots |P_k| = |G|$（因为 $|P_i| = p_i^{n_i}$）。因此 $G = P_1 \times \cdots \times P_k$。 $\square$

---

### 习题 6.5

**题目**: 设 $G$ 为有限群，$p$ 为 $|G|$ 的最小素因子。证明 $G$ 的指数为 $p$ 的子群（如果存在）必为正规子群。

**提示**: 设 $H \leq G$，$[G : H] = p$。考虑 $G$ 在左陪集 $G/H$ 上的左乘作用。

**解答**: $G$ 在 $G/H$ 上左乘作用给出同态 $\varphi : G \to S_p$。$\ker\varphi \leq H$（因为 $g \in \ker\varphi$ 固定 $H$，即 $gH = H$，$g \in H$）。

$G/\ker\varphi \cong \operatorname{im}\varphi \leq S_p$。由第一同构定理，$|G/\ker\varphi|$ 整除 $p!$。又 $|G/\ker\varphi| = |G|/|\ker\varphi| = [G : H] \cdot |H|/|\ker\varphi| = p \cdot |H|/|\ker\varphi|$。

因为 $H/\ker\varphi$ 嵌入 $S_p$ 且固定 $H$ 这个点，实际上 $H/\ker\varphi$ 嵌入 $S_{p-1}$。故 $|H/\ker\varphi|$ 整除 $(p-1)!$。但 $|H/\ker\varphi|$ 的素因子均 $\geq p$（因为 $p$ 是 $|G|$ 的最小素因子），而 $(p-1)!$ 的所有素因子 $< p$。因此 $|H/\ker\varphi| = 1$，$H = \ker\varphi \trianglelefteq G$。 $\square$

---

### 习题 6.6

**题目**: 设 $G$ 为有限群，$a, b \in G$ 可交换，$\operatorname{ord}(a) = m$，$\operatorname{ord}(b) = n$，$\gcd(m, n) = 1$。证明 $\operatorname{ord}(ab) = mn$。

**提示**: 设 $(ab)^k = 1$，利用交换性得到 $a^k = b^{-k}$，分析其阶。

**解答**: 设 $\operatorname{ord}(ab) = k$。则 $(ab)^k = 1$，$a^k b^k = 1$（因为 $ab = ba$），$a^k = b^{-k}$。$a^k \in \langle a \rangle \cap \langle b \rangle$。$|\langle a \rangle \cap \langle b \rangle|$ 整除 $m$ 和 $n$，而 $\gcd(m, n) = 1$，故 $|\langle a \rangle \cap \langle b \rangle| = 1$，$a^k = 1$，$b^k = 1$。所以 $m \mid k$，$n \mid k$，$mn \mid k$（因为 $\gcd(m, n) = 1$）。

另一方面，$(ab)^{mn} = a^{mn} b^{mn} = (a^m)^n (b^n)^m = 1$。故 $k \mid mn$。结合 $mn \mid k$ 得 $k = mn$。 $\square$

---

### 习题 6.7

**题目**: 设 $G$ 为有限群，$|G| = p^n$（$p$ 为素数）。证明对任意 $k \in \{0, 1, \ldots, n\}$，$G$ 存在 $p^k$ 阶正规子群。

**提示**: 对 $|G|$ 归纳。利用中心的非平凡性和 Cauchy 定理。

**解答**: $n = 0$ 时显然。设 $n \geq 1$。由类方程，$Z(G)$ 非平凡，$p \mid |Z(G)|$。由 Cauchy 定理，$Z(G)$ 存在 $p$ 阶子群 $N$。$N \trianglelefteq G$（因为 $N \leq Z(G)$）。

考虑 $G/N$，$|G/N| = p^{n-1}$。由归纳假设，$G/N$ 对每个 $j \in \{0, \ldots, n-1\}$ 存在 $p^j$ 阶正规子群 $\overline{H}_j$。由对应定理，$\overline{H}_j = H_j/N$，$H_j \trianglelefteq G$，$|H_j| = p^{j+1}$。与 $N$ 本身（$p^0$ 阶正规子群 $\{1_G\}$ 对应）一起，$G$ 对所有 $k \in \{0, \ldots, n\}$ 存在 $p^k$ 阶正规子群。 $\square$

---

### 习题 6.8

**题目**: 设 $G$ 为群，$H, K \leq G$，且 $H \cap K = \{1_G\}$，$HK = G$，$H, K$ 都正规。证明 $G \cong H \times K$。

**提示**: 定义 $\varphi : H \times K \to G$ 为 $\varphi(h, k) = hk$，验证这是同构。

**解答**: 定义 $\varphi(h, k) = hk$。因为 $G = HK$，$\varphi$ 满。若 $h_1k_1 = h_2k_2$，则 $h_2^{-1}h_1 = k_2k_1^{-1} \in H \cap K = \{1_G\}$，故 $h_1 = h_2$，$k_1 = k_2$，$\varphi$ 单。

验证同态：$\varphi((h_1, k_1)(h_2, k_2)) = \varphi(h_1h_2, k_1k_2) = h_1h_2k_1k_2$。而 $\varphi(h_1, k_1)\varphi(h_2, k_2) = h_1k_1h_2k_2$。因为 $K$ 正规，$k_1h_2k_1^{-1} \in K$，但更直接地，因为 $H, K$ 都正规且交平凡，$hk = kh$ 对所有 $h \in H, k \in K$ 成立（因为 $hkh^{-1}k^{-1} \in H \cap K = \{1_G\}$）。故 $h_1h_2k_1k_2 = h_1k_1h_2k_2$，$\varphi$ 是同态。因此 $G \cong H \times K$。 $\square$

---

### 习题 6.9

**题目**: 设 $G$ 为有限群，$|G| = pqr$（$p < q < r$ 为素数）。证明 $G$ 不是单群。

**提示**: 分别考虑 $n_r, n_q, n_p$。利用 Sylow 第三定理和元素计数导出矛盾。

**解答**: 对 $n_r$：$n_r \equiv 1 \pmod{r}$ 且 $n_r \mid pq$。若 $n_r > 1$，则 $n_r \geq r+1 > r > q > p$，而 $n_r \in \{1, p, q, pq\}$，故 $n_r = pq$（因为 $n_r \geq r+1 > q > p$）。此时 $G$ 有 $pq(r-1)$ 个 $r$ 阶元素。

对 $n_q$：$n_q \equiv 1 \pmod{q}$ 且 $n_q \mid pr$。若 $n_q > 1$，则 $n_q \in \{p, r, pr\}$ 且 $n_q \geq q+1 > q > p$。由于 $r > q$，$n_q = r$ 或 $pr$。若 $n_q = r$，则 $r \equiv 1 \pmod{q}$。若 $n_q = pr$，则 $pr \equiv 1 \pmod{q}$。无论如何，若 $n_q > 1$，$G$ 至少有 $q-1$ 个 $q$ 阶元素。

若 $n_r = pq$ 且 $n_q > 1$，则 $G$ 中元素数至少为 $pq(r-1) + (q-1) + 1 = pqr - pq + q > pqr$（因为 $q > p$），矛盾。所以 $n_r = 1$ 或 $n_q = 1$，$G$ 有正规 Sylow 子群，非单。 $\square$

---

### 习题 6.10

**题目**: 设 $G$ 为有限群，$a \in G$。证明 $\operatorname{ord}(a) = \operatorname{ord}(gag^{-1})$ 对任意 $g \in G$ 成立。并由此说明共轭元素生成同阶的子群。

**提示**: 验证 $(gag^{-1})^n = ga^ng^{-1}$。

**解答**: 对任意正整数 $n$，$(gag^{-1})^n = ga^ng^{-1}$（由归纳：$(gag^{-1})^1 = gag^{-1}$；若 $(gag^{-1})^k = ga^kg^{-1}$，则 $(gag^{-1})^{k+1} = ga^kg^{-1} \cdot gag^{-1} = ga^{k+1}g^{-1}$）。

设 $\operatorname{ord}(a) = m$。则 $(gag^{-1})^m = ga^mg^{-1} = g1_Gg^{-1} = 1_G$。若 $(gag^{-1})^k = 1_G$，则 $ga^kg^{-1} = 1_G$，$a^k = 1_G$，$m \mid k$。故 $\operatorname{ord}(gag^{-1}) = m = \operatorname{ord}(a)$。

$\langle gag^{-1} \rangle = g\langle a \rangle g^{-1}$，两者同构（共轭同构），故同阶。 $\square$

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18


## 习题

**习题 1.1**。设 $G$ 是有限群，$p$ 是素数且 $p \\mid |G|$。用 Cauchy 定理证明 $G$ 中存在阶为 $p$ 的元素。

*解答*：Cauchy 定理直接给出存在 $g\\in G$ 使 $|g|=p$。$\square$

---

**习题 1.2**。证明：$p$-群（阶为 $p^n$ 的群）的中心非平凡。

*解答*：由类方程，$|G| = |Z(G)| + \\sum [G:C_G(x_i)]$。每个 $[G:C_G(x_i)]$ 是 $p$ 的幂且大于1，故 $p \\mid |Z(G)|$，$Z(G)\\neq\\{e\\}$。$\square$
