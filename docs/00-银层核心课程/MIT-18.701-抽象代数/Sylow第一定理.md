---
title: "Sylow 第一定理（Sylow's First Theorem）"
level: "silver"
course: MIT 18.701 抽象代数
msc_primary: "20-02"
target_courses:
  - "MIT 18.701"
references:
  textbooks:
    - title: "Algebra"
      author: "Michael Artin"
      edition: "2nd"
      chapters: "Chapter 6, Section 4"
      pages: "205-208"
    - title: "Abstract Algebra"
      author: "David S. Dummit and Richard M. Foote"
      edition: "3rd"
      chapters: "Chapter 4, Section 5"
      pages: "139-143"
  lectures:
    - institution: "MIT"
      course_code: "18.701"
      lecture: "Lecture 14-15"
      url: "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2020/"
keywords:
  - "Sylow's First Theorem"
  - "p-group"
  - "Sylow p-subgroup"
  - "group action"
  - "finite group"
status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Sylow 第一定理（Sylow's First Theorem）

> **课程**: MIT 18.701 抽象代数 I | **主题**: 有限群的 p-子群存在性
> **学习目标**: 掌握 p-群、Sylow p-子群的定义，理解 Sylow 第一定理的归纳证明，能够运用 Sylow 定理分析具体群的结构

---

## 一、核心定义

### 定义 1.1（p-群）

**严格陈述**: 设 $p$ 为素数。有限群 $G$ 称为 **$p$-群**（$p$-group），若 $|G| = p^n$ 对某个非负整数 $n$ 成立。一般地，若 $H \leq G$ 且 $H$ 是 $p$-群，则称 $H$ 为 $G$ 的 **$p$-子群**（$p$-subgroup）。

**直观解释**: $p$-群是"仅由素数 $p$ 构成"的群。它们是有限群结构的基本"砖块"，类似于素数在整数分解中的作用。

> **双语对照**:
>
> ```lean4
> -- Mathlib4 中 p-群由 IsPGroup 定义
> def IsPGroup' {G : Type u} [Group G] [Fintype G] (p : ℕ) : Prop :=
>   ∃ (n : ℕ), Fintype.card G = p ^ n
> ```

---

### 定义 1.2（Sylow p-子群）

**严格陈述**: 设 $G$ 为有限群，$|G| = p^n \cdot m$，其中 $p$ 为素数且 $p \nmid m$。$G$ 的 **Sylow $p$-子群**（Sylow $p$-subgroup）是指阶恰为 $p^n$ 的子群，即 $G$ 的极大 $p$-子群。

Sylow $p$-子群的全体记作 $\operatorname{Syl}_p(G)$，其个数记作 $n_p = |\operatorname{Syl}_p(G)|$。

**直观解释**: 若将 $|G|$ 进行素因子分解，Sylow $p$-子群对应于 $p$ 部分的"最大可能"子群。例如 $|G| = 12 = 2^2 \cdot 3$，则 Sylow 2-子群的阶为 4，Sylow 3-子群的阶为 3。

> **双语对照**:
>
> ```lean4
> -- Mathlib4 中 Sylow p-子群由 Sylow 类型表示
> def IsSylowPSubgroup {G : Type u} [Group G] [Fintype G]
>     (p : ℕ) [Fact p.Prime] (H : Subgroup G) : Prop :=
>   let n := (Fintype.card G).factorization p
>   Fintype.card H = p ^ n
> ```

---

### 定义 1.3（群作用）

**严格陈述**: 设 $G$ 为群，$X$ 为集合。$G$ 在 $X$ 上的一个**作用**（group action）是一个映射 $G \times X \to X$，记作 $(g, x) \mapsto g \cdot x$，满足：

1. $1_G \cdot x = x$（单位元作用平凡）；
2. $(gh) \cdot x = g \cdot (h \cdot x)$（作用与群乘法相容）。

等价地，群作用对应于同态 $G \to \operatorname{Sym}(X)$（$G$ 到 $X$ 上对称群的同态）。

**直观解释**: 群作用描述了群的元素如何"移动"或"变换"集合中的元素。它是连接抽象群论与具体几何/组合结构的桥梁。

---

## 二、核心定理与完整证明

### 定理 2.1（Sylow 第一定理）

**定理陈述**: 设 $G$ 为有限群，$p$ 为素数，$|G| = p^n \cdot m$ 且 $p \nmid m$。则 $G$ 存在 Sylow $p$-子群，即存在 $P \leq G$ 使得 $|P| = p^n$。

**证明**: 我们对 $|G|$ 进行归纳证明。

**基例**: $|G| = 1$ 时，$n = 0$，$P = \{1_G\}$ 即为 Sylow $p$-子群。

**归纳假设**: 设对所有阶小于 $|G|$ 的群，Sylow $p$-子群存在。

**归纳步骤**: 考虑群 $G$ 在自身上的共轭作用，其**类方程**为
$$|G| = |Z(G)| + \sum_{i} [G : C_G(g_i)],$$
其中 $Z(G)$ 是 $G$ 的中心，$C_G(g_i)$ 是非中心元素 $g_i$ 的中心化子，求和遍历所有非平凡共轭类的代表元。

**情形一：$p \nmid |Z(G)|$。**

由类方程，$p^n m = |Z(G)| + \sum_i [G : C_G(g_i)]$。因为 $p \mid |G|$ 但 $p \nmid |Z(G)|$，所以存在某个 $g_i$ 使得 $p \nmid [G : C_G(g_i)]$。

对该 $g_i$，由拉格朗日定理，$|G| = [G : C_G(g_i)] \cdot |C_G(g_i)|$。因为 $p^n \mid |G|$ 且 $p \nmid [G : C_G(g_i)]$，所以 $p^n \mid |C_G(g_i)|$。同时 $g_i \notin Z(G)$，故 $C_G(g_i) \neq G$，$|C_G(g_i)| < |G|$。

由归纳假设，$C_G(g_i)$ 存在 Sylow $p$-子群 $P$，且 $|P| = p^n$（因为 $p^n \mid |C_G(g_i)|$ 且 $|C_G(g_i)| \mid |G| = p^n m$）。于是 $P \leq C_G(g_i) \leq G$ 也是 $G$ 的 Sylow $p$-子群。

**情形二：$p \mid |Z(G)|$。**

由 Cauchy 定理（群论版，见后续主题），$Z(G)$ 中存在 $p$ 阶元素 $x$。令 $N = \langle x \rangle$，则 $N \leq Z(G)$，故 $N \trianglelefteq G$（中心中的子群都是正规的）。

考虑商群 $G/N$，$|G/N| = |G|/|N| = p^{n-1} m < |G|$。由归纳假设，$G/N$ 存在 Sylow $p$-子群 $\overline{P}$，$|\overline{P}| = p^{n-1}$。

由对应定理（第四同构定理），$\overline{P} = P/N$ 对某个满足 $N \leq P \leq G$ 的子群 $P$。于是
$$|P| = |P/N| \cdot |N| = p^{n-1} \cdot p = p^n.$$
因此 $P$ 是 $G$ 的 Sylow $p$-子群。

两种情形均证明了 Sylow $p$-子群的存在性。由数学归纳法，定理得证。 $\square$

> **双语对照**:
>
> ```lean4
> theorem sylow_first_theorem {G : Type u} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
>     (n : ℕ) (m : ℕ) (hm : p.Coprime m) (hG : Fintype.card G = p ^ n * m) :
>     ∃ (P : Sylow p G), Fintype.card P = p ^ n := by
>   have h : ∃ (P : Sylow p G), True := by
>     use default
>   rcases h with ⟨P, -⟩
>   use P
>   have h_card_P : Fintype.card P = p ^ n := by
>     have h_pgroup : IsPGroup p P := by
>       exact Sylow.isPGroup' P
>     rcases h_pgroup with ⟨k, hk⟩
>     have h_dvd : Fintype.card P ∣ Fintype.card G := by
>       exact card_subgroup_dvd_card (P.toSubgroup)
>     rw [hG] at h_dvd
>     rw [hk] at h_dvd
>     have h_k_le_n : k ≤ n := by
>       have h : p ^ k ∣ p ^ n * m := h_dvd
>       have h_coprime : p ^ n.Coprime m := by
>         exact Nat.Coprime.pow_left n hm
>       have h_pk_pn : p ^ k ∣ p ^ n := by
>         exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h
>       exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le h_pk_pn
>     have h_k_eq_n : k = n := by
>       have h_max : ∀ (k' : ℕ), p ^ k' ∣ Fintype.card G → k' ≤ n := by
>         intro k' h_pk'
>         rw [hG] at h_pk'
>         have h_coprime : p ^ n.Coprime m := by
>           exact Nat.Coprime.pow_left n hm
>         have h_pk'_pn : p ^ k' ∣ p ^ n := by
>           exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_pk'
>         exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le h_pk'_pn
>       have h_k_max : ∀ (k' : ℕ), k' > k → ¬(p ^ k' ∣ Fintype.card P) := by
>         intro k' hk' h_pk'
>         rw [hk] at h_pk'
>         have : p ^ k' ∣ p ^ k := h_pk'
>         have : k' ≤ k := by
>           exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le this
>         linarith
>       have h_n_le_k : n ≤ k := by
>         by_contra h
>         push_neg at h
>         have : p ^ n ∣ Fintype.card P := by
>           rw [hk]
>           exact pow_dvd_pow p h
>         exact h_k_max n h this
>       linarith
>     rw [h_k_eq_n] at hk
>     exact hk
>   exact h_card_P
> ```

> **证明要点提示**: Sylow 第一定理的证明是有限群论中最经典的归纳论证之一。关键技巧是：
>
> 1. 利用类方程将问题分解为"中心情形"和"非中心情形"；
> 2. 非中心情形通过中心化子降阶；
> 3. 中心情形通过 Cauchy 定理和商群降阶。
> 两种路径最终都将群的阶降低了 $p$ 的至少一次幂，从而可以应用归纳假设。

---

### 推论 2.2（p-子群存在性）

**定理陈述**: 设 $G$ 为有限群，$p^k \mid |G|$（$p$ 为素数）。则 $G$ 存在阶为 $p^k$ 的子群。

**证明**: 设 $|G| = p^n \cdot m$（$p \nmid m$），$k \leq n$。由 Sylow 第一定理，$G$ 存在 Sylow $p$-子群 $P$，$|P| = p^n$。由有限 $p$-群的理论（或再次归纳），$P$ 存在阶为 $p^k$ 的子群，该子群也是 $G$ 的子群。 $\square$

---

## 三、典型例题

### 例题 3.1（$S_4$ 的 Sylow 子群）

**题目**: 求对称群 $S_4$ 的所有 Sylow 2-子群和 Sylow 3-子群。

**解答**: $|S_4| = 24 = 2^3 \cdot 3$。

**Sylow 2-子群**: 阶应为 $2^3 = 8$。$S_4$ 中由两个不相交对换生成的子群同构于二面体群 $D_4$（正方形的对称群），阶恰为 8。具体地，$P = \langle (1234), (13) \rangle$ 是一个 Sylow 2-子群。$S_4$ 中 Sylow 2-子群的个数 $n_2$ 满足 $n_2 \equiv 1 \pmod{2}$ 且 $n_2 \mid 3$，故 $n_2 = 1$ 或 $3$。由于 $S_4$ 的 Sylow 2-子群不唯一（例如 $\langle (1243), (14) \rangle$ 是另一个），所以 $n_2 = 3$。

**Sylow 3-子群**: 阶应为 $3$。$S_4$ 中的 3-阶子群由 3-循环生成，如 $\langle (123) \rangle = \{e, (123), (132)\}$。$n_3$ 满足 $n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 8$，故 $n_3 = 1$ 或 $4$。由于不同的 3-循环生成不同的 3 阶子群，且 $S_4$ 中有 8 个 3-循环，每个 3 阶子群含 2 个 3-循环，所以共有 $8/2 = 4$ 个 Sylow 3-子群。即 $n_3 = 4$。 $\square$

**关键步骤解析**: 利用 Sylow 第三定理的同余和整除条件可以快速缩小 $n_p$ 的可能取值，再结合群的具体结构确定准确值。

---

### 例题 3.2（15 阶群的结构）

**题目**: 设 $|G| = 15 = 3 \cdot 5$。证明 $G$ 是循环群。

**解答**: 由 Sylow 第一定理，$G$ 存在 Sylow 3-子群 $P$（$|P| = 3$）和 Sylow 5-子群 $Q$（$|Q| = 5$）。

对 $n_3$：$n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 5$，故 $n_3 = 1$。因此 $P \trianglelefteq G$（唯一的 Sylow $p$-子群必正规）。

对 $n_5$：$n_5 \equiv 1 \pmod{5}$ 且 $n_5 \mid 3$，故 $n_5 = 1$。因此 $Q \trianglelefteq G$。

$P \cap Q = \{1_G\}$（因为 $|P \cap Q|$ 整除 3 和 5），且 $|PQ| = |P||Q|/|P \cap Q| = 15 = |G|$，所以 $G = PQ \cong P \times Q$（因为两者都正规且交平凡）。而 $P \cong \mathbb{Z}/3\mathbb{Z}$，$Q \cong \mathbb{Z}/5\mathbb{Z}$，且 $\gcd(3, 5) = 1$，故 $P \times Q \cong \mathbb{Z}/15\mathbb{Z}$。因此 $G$ 是循环群。 $\square$

---

## 四、常见误区与纠正

### 误区 4.1: "Sylow p-子群唯一"

**错误观点**: 认为对任意有限群 $G$ 和素数 $p$，Sylow $p$-子群只有一个。

**反例或纠正**: Sylow $p$-子群**不一定唯一**。例如 $S_3$（$|S_3| = 6 = 2 \cdot 3$）中：

- Sylow 2-子群的阶为 2，有 3 个：$\langle (12) \rangle$、$\langle (13) \rangle$、$\langle (23) \rangle$；
- Sylow 3-子群的阶为 3，只有 1 个：$\langle (123) \rangle = A_3$。

> **为什么错**: Sylow 第二定理告诉我们：**所有 Sylow $p$-子群互相共轭**。因此 Sylow $p$-子群唯一当且仅当它是正规子群。只有当 $n_p = 1$ 时（由 Sylow 第三定理的条件可以判断），Sylow $p$-子群才唯一。对 $S_3$，$n_2 = 3$，$n_3 = 1$。

---

## 五、思想方法提炼

**本章核心思想**:

1. **极大性原理**: Sylow $p$-子群是 $p$-子群中"不能再大"的。这种极大性保证了它们承载着群在 $p$ 方向的完整结构信息。

2. **归纳降阶**: Sylow 第一定理的证明展示了处理有限群问题的标准策略——通过中心或类方程将问题转移到更小的群（中心化子或商群），然后应用归纳假设。

3. **存在性 vs. 唯一性**: Sylow 第一定理保证**存在性**，第二、三定理刻画**相互关系和个数**。三者共同构成了有限群论中分析 $p$-部分的完整工具箱。

**与后续章节的联系**:

- Sylow 定理是**有限群分类**的基础工具，低阶群分类几乎完全依赖 Sylow 定理。
- **Cauchy 定理**（若 $p \mid |G|$ 则存在 $p$ 阶元素）是 Sylow 第一定理的推论（$k = 1$ 的情形）。
- 在**可解群**和**幂零群**理论中，Sylow 子群的性质是核心判定条件。

---

## 六、习题

### 习题 6.1

**题目**: 设 $|G| = 20 = 2^2 \cdot 5$。确定 $n_2$ 和 $n_5$ 的所有可能取值，并讨论对应的群结构。

**提示**: 利用 Sylow 第三定理的同余和整除条件。

**解答**: 对 $n_5$：$n_5 \equiv 1 \pmod{5}$ 且 $n_5 \mid 4$，故 $n_5 = 1$。Sylow 5-子群 $P$ 唯一，$P \trianglelefteq G$。

对 $n_2$：$n_2 \equiv 1 \pmod{2}$ 且 $n_2 \mid 5$，故 $n_2 = 1$ 或 $5$。

- 若 $n_2 = 1$，则 $G$ 有唯一的 Sylow 2-子群 $Q \trianglelefteq G$，$G \cong P \times Q \cong \mathbb{Z}/5\mathbb{Z} \times \mathbb{Z}/4\mathbb{Z}$ 或 $\mathbb{Z}/5\mathbb{Z} \times (\mathbb{Z}/2\mathbb{Z})^2$。
- 若 $n_2 = 5$，则 $G$ 是 $P$ 被 $Q$ 的半直积 $G \cong P \rtimes Q$。 $\square$

---

### 习题 6.2

**题目**: 证明 30 阶群不是单群（即存在非平凡正规子群）。

**提示**: $|G| = 30 = 2 \cdot 3 \cdot 5$。分别考虑 $n_2, n_3, n_5$。

**解答**: 对 $n_5$：$n_5 \equiv 1 \pmod{5}$ 且 $n_5 \mid 6$，故 $n_5 = 1$ 或 $6$。若 $n_5 = 1$，则 Sylow 5-子群正规，$G$ 非单。

若 $n_5 = 6$，则 $G$ 有 $6 \cdot (5-1) = 24$ 个 5 阶元素（每个 Sylow 5-子群含 4 个非单位元，且不同 Sylow 5-子群交为平凡）。

对 $n_3$：$n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 10$，故 $n_3 = 1$ 或 $10$。若 $n_3 = 1$，则 Sylow 3-子群正规。

若 $n_3 = 10$，则 $G$ 有 $10 \cdot (3-1) = 20$ 个 3 阶元素。但 $24 + 20 = 44 > 30$，矛盾。因此 $n_3 = 1$ 或 $n_5 = 1$，$G$ 非单。 $\square$

---

### 习题 6.3

**题目**: 设 $P$ 为有限群 $G$ 的 Sylow $p$-子群，$H \leq G$ 满足 $N_G(P) \leq H$。证明 $N_G(H) = H$。

**提示**: 利用 Sylow 第二定理：$H$ 中的 Sylow $p$-子群在 $H$ 中共轭。

**解答**: 显然 $H \leq N_G(H)$。设 $g \in N_G(H)$，则 $gPg^{-1} \leq gHg^{-1} = H$。$gPg^{-1}$ 是 $H$ 的 Sylow $p$-子群（因为 $|gPg^{-1}| = |P|$）。由 Sylow 第二定理在 $H$ 中的应用，存在 $h \in H$ 使得 $gPg^{-1} = hPh^{-1}$。于是 $h^{-1}g \in N_G(P) \leq H$，故 $g \in hH = H$。因此 $N_G(H) \leq H$，$N_G(H) = H$。 $\square$

---

### 习题 6.4

**题目**: 设 $G$ 为 $p$-群，$|G| = p^n$。证明 $G$ 的中心 $Z(G)$ 非平凡，且 $G$ 存在正规子群列
$$\{1\} = G_0 \trianglelefteq G_1 \trianglelefteq \cdots \trianglelefteq G_n = G$$
使得每个商因子 $G_{i+1}/G_i$ 的阶为 $p$（这样的子群列称为**合成列**）。

**提示**: 对 $|G|$ 归纳。利用类方程证明 $Z(G)$ 含 $p$ 阶子群。

**解答**: 由类方程，$p \mid |Z(G)|$（见拉格朗日定理文档中的习题 6.8），故 $Z(G)$ 含 $p$ 阶子群 $N$。$N \trianglelefteq G$（因为 $N \leq Z(G)$）。考虑 $G/N$，$|G/N| = p^{n-1}$。由归纳假设，$G/N$ 有所述正规子群列。由对应定理，这些子群对应 $G$ 中包含 $N$ 的正规子群，与 $N$ 本身拼接即得 $G$ 的正规子群列。 $\square$

---

### 习题 6.5

**题目**: 设 $|G| = 56 = 2^3 \cdot 7$。证明 $G$ 不是单群。

**提示**: 分析 $n_2$ 和 $n_7$ 的可能值。

**解答**: 对 $n_7$：$n_7 \equiv 1 \pmod{7}$ 且 $n_7 \mid 8$，故 $n_7 = 1$ 或 $8$。

若 $n_7 = 1$，则 Sylow 7-子群正规，$G$ 非单。

若 $n_7 = 8$，则 $G$ 有 $8 \cdot 6 = 48$ 个 7 阶元素。剩余 $56 - 48 = 8$ 个元素构成唯一的 Sylow 2-子群，故 $n_2 = 1$，Sylow 2-子群正规。因此 $G$ 非单。 $\square$

---

### 习题 6.6

**题目**: 设 $P$ 为 $G$ 的 Sylow $p$-子群，$Q$ 为 $G$ 的 Sylow $q$-子群，$p \neq q$ 为素数。证明 $P \cap Q = \{1_G\}$。

**提示**: 考虑 $P \cap Q$ 的阶同时整除 $|P|$ 和 $|Q|$。

**解答**: $P \cap Q \leq P$，故 $|P \cap Q|$ 整除 $|P| = p^n$，所以 $|P \cap Q| = p^k$（$k \geq 0$）。同理 $|P \cap Q| = q^l$（$l \geq 0$）。因此 $p^k = q^l$。由于 $p, q$ 是不同的素数，这仅在 $k = l = 0$ 时成立，即 $|P \cap Q| = 1$，$P \cap Q = \{1_G\}$。 $\square$

---

### 习题 6.7

**题目**: 设 $G$ 为有限群，$P \in \operatorname{Syl}_p(G)$。证明 $N_G(N_G(P)) = N_G(P)$。

**提示**: 利用习题 6.3 的结论。

**解答**: 取 $H = N_G(P)$，则 $P \trianglelefteq H$，且 $N_G(P) = H \leq H$。由习题 6.3（取 $H = N_G(P)$），$N_G(N_G(P)) = N_G(H) = H = N_G(P)$。 $\square$

---

### 习题 6.8

**题目**: 设 $|G| = p^2 q$（$p, q$ 为不同素数）。证明 $G$ 有正规 Sylow 子群。

**提示**: 不妨设 $p < q$，分析 $n_p$ 和 $n_q$。

**解答**: 对 $n_q$：$n_q \equiv 1 \pmod{q}$ 且 $n_q \mid p^2$，故 $n_q \in \{1, p, p^2\}$。

- 若 $n_q = 1$，Sylow $q$-子群正规。
- 若 $n_q = p$，则 $p \equiv 1 \pmod{q}$，即 $q \mid (p-1)$。但 $q > p > p-1 \geq 1$，矛盾。
- 若 $n_q = p^2$，则 $p^2 \equiv 1 \pmod{q}$，即 $q \mid (p^2-1) = (p-1)(p+1)$。因为 $q > p$，$q \nmid (p-1)$，故 $q \mid (p+1)$。于是 $q \leq p+1$，结合 $q > p$ 得 $q = p+1$。由于 $p, q$ 均为素数，这仅当 $p = 2, q = 3$ 时成立。

若 $(p, q) \neq (2, 3)$，则 $n_q = 1$，Sylow $q$-子群正规。

若 $(p, q) = (2, 3)$，则 $|G| = 12$。$n_3 = 1$ 或 $4$。若 $n_3 = 1$，Sylow 3-子群正规。若 $n_3 = 4$，$G$ 有 8 个 3 阶元素，剩余 4 个元素构成唯一的 Sylow 2-子群，$n_2 = 1$，Sylow 2-子群正规。 $\square$

---

### 习题 6.9

**题目**: 设 $G$ 为有限群，$H \trianglelefteq G$。若 $P$ 是 $H$ 的 Sylow $p$-子群，证明 $G = H \cdot N_G(P)$，且 $[G : H] = [N_G(P) : N_H(P)]$。

**提示**: 利用 Frattini 论证（Frattini argument）。对任意 $g \in G$，$gPg^{-1}$ 是 $H$ 的 Sylow $p$-子群。

**解答**: （Frattini 论证）设 $g \in G$。因为 $H \trianglelefteq G$，$gPg^{-1} \leq gHg^{-1} = H$，且 $|gPg^{-1}| = |P|$，故 $gPg^{-1}$ 也是 $H$ 的 Sylow $p$-子群。由 Sylow 第二定理在 $H$ 中的应用，存在 $h \in H$ 使得 $gPg^{-1} = hPh^{-1}$。于是 $h^{-1}g \in N_G(P)$，$g \in hN_G(P) \subseteq H \cdot N_G(P)$。因此 $G = H \cdot N_G(P)$。

由第二同构定理，$HN_G(P)/N_G(P) \cong H/(H \cap N_G(P)) = H/N_H(P)$。而 $HN_G(P) = G$，故 $G/N_G(P) \cong H/N_H(P)$。比较阶得 $[G : N_G(P)] = [H : N_H(P)]$。进一步由 $[G : H][H : N_H(P)] = [G : N_H(P)] = [G : N_G(P)][N_G(P) : N_H(P)]$ 和 $[G : N_G(P)] = [H : N_H(P)]$，消去得 $[G : H] = [N_G(P) : N_H(P)]$。 $\square$

---

### 习题 6.10

**题目**: 设 $G$ 为 $p$-群，作用在有限集合 $X$ 上。令 $X^G = \{x \in X \mid g \cdot x = x,\; \forall g \in G\}$ 为不动点集。证明 $|X| \equiv |X^G| \pmod{p}$。

**提示**: 利用轨道-稳定子定理，证明非不动点的轨道大小均被 $p$ 整除。

**解答**: $X$ 被轨道划分：$X = X^G \sqcup \bigsqcup_{\text{非平凡轨道 } O} O$。对 $x \in X^G$，轨道 $\{x\}$ 大小为 1。对 $x \notin X^G$，稳定子 $G_x \neq G$，故 $[G : G_x] = |O_x| > 1$。因为 $G$ 是 $p$-群，$|G_x|$ 是 $p$ 的幂且 $|G_x| < |G|$，所以 $p \mid |O_x| = |G|/|G_x|$。因此每个非平凡轨道的大小被 $p$ 整除，$|X| = |X^G| + \sum_{\text{非平凡}} |O| \equiv |X^G| \pmod{p}$。 $\square$

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
