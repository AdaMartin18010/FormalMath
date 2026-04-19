---
msc_primary: "20D20"
msc_secondary:
  - 20D15
  - 20E28
---

# 概念卡片：Sylow第一定理

## 严格定义

设 $G$ 为有限群，$|G| = p^n \cdot m$，其中 $p$ 为素数，$n \geq 1$，且 $p \nmid m$。

**Sylow $p$-子群**：$G$ 的阶恰为 $p^n$ 的子群 $P \leq G$ 称为 Sylow $p$-子群。所有 Sylow $p$-子群的集合记为 $\mathrm{Syl}_p(G)$。

**Sylow 第一定理（存在性）**：对任意素数 $p$ 整除 $|G|$，Sylow $p$-子群存在。即 $\mathrm{Syl}_p(G) \neq \varnothing$。

**Sylow 三大定理**的完整表述：

1. **存在性**：$\mathrm{Syl}_p(G) \neq \varnothing$；
2. **共轭性**：任意 $P, Q \in \mathrm{Syl}_p(G)$ 共轭，即存在 $g \in G$ 使得 $Q = gPg^{-1}$；
3. **计数**：$n_p = |\mathrm{Syl}_p(G)|$ 满足 $n_p \equiv 1 \pmod p$ 且 $n_p \mid m$。

## 历史背景

Sylow 定理的历史是有限群论从案例研究走向系统理论的转折点。

**Cauchy 定理（1845）**：Augustin-Louis Cauchy 证明了若素数 $p$ 整除 $|G|$，则 $G$ 中存在 $p$ 阶元（因而存在 $p$ 阶子群）。这是 Sylow 第一定理在 $n = 1$ 时的特例。Cauchy 的证明利用了 $G$ 通过左平移作用在自身上的置换表示。

**Sylow 的突破（1872）**：挪威数学家 Peter Ludwig Mejdell Sylow（1832–1918）在 1872 年的论文中将 Cauchy 定理推广到 $p$-幂阶子群。Sylow 的证明核心是让 $G$ 通过左平移作用在自身上，将 $G$ 嵌入对称群 $S_{|G|}$，然后利用 $S_{|G|}$ 中已知的 $p$-子群结构来提取 $G$ 中的 Sylow 子群。

**现代证明的演变**：20 世纪初，Burnside 和 Frobenius 发展了基于群作用和特征标的替代证明。现代教材通常采用以下两种证明之一：

- **Wielandt 的证明**：让 $G$ 作用在 $p$-元子集族上，利用轨道-稳定子定理计数；
- **基于上同调的证明**：利用第一上同调群 $H^1(G, M)$ 分类群扩张。

## 直观理解

Sylow 第一定理的核心信息是：**无论群 $G$ 的整体结构多么复杂，其 $p$-部分（最大可能的 $p$-幂阶子群）总是存在的。**

可以将群的阶 $|G| = p^n m$（$p \nmid m$）想象为一个"建筑"：$p^n$ 是建筑的"$p$-核心"，$m$ 是"剩余结构"。Sylow 第一定理保证这个核心总是可以被"隔离"出来——存在一个子群恰好捕捉了全部的 $p$-部分。

**与 Lagrange 定理的对比**：Lagrange 定理说子群的阶整除群的阶，但逆命题不成立——$d \mid |G|$ 不保证存在 $d$ 阶子群。Sylow 定理填补了部分空白：它保证所有 $p$-幂阶（$p$ 为素数）的子群存在。例如，$A_4$（12 阶）没有 6 阶子群（尽管 $6 \mid 12$），但它有 Sylow 2-子群（4 阶）和 Sylow 3-子群（3 阶）。

## 数学例子

### 第一定理的标准证明（Wielandt）

设 $|G| = p^n m$。考虑 $G$ 通过左平移作用在 $G$ 的所有 $p^n$-元子集构成的集合 $X$ 上，$|X| = \binom{p^n m}{p^n}$。

**关键数论引理**：$p \nmid \binom{p^n m}{p^n}$。

证明：由 Lucas 定理或直接计算 $p$-进赋值，$\nu_p\left(\binom{p^n m}{p^n}\right) = \nu_p((p^n m)!) - \nu_p((p^n)!) - \nu_p(((p^n(m-1))!)) = 0$。

因 $|X| \not\equiv 0 \pmod p$，而 $X$ 被分解为 $G$-轨道，故至少有一个轨道的长度不被 $p$ 整除。设 $O$ 为这样的轨道，$A \in O$ 为一个 $p^n$-元子集，$P = \mathrm{Stab}_G(A)$。

由轨道-稳定子定理，$|O| = [G : P] = |G|/|P|$。因 $p \nmid |O|$ 且 $|G| = p^n m$，有 $p^n \mid |P|$。另一方面，$P$ 作用在 $A$ 上，对任意 $g \in P$，$gA = A$，故 $P$ 可嵌入 $S_A$（$A$ 上的对称群），$|P| \leq |A|! = (p^n)!$。更精细的分析表明 $|P| \leq p^n$。

因此 $|P| = p^n$，$P$ 即为 Sylow $p$-子群。

### 对称群 $S_4$ 的 Sylow 子群

$|S_4| = 24 = 2^3 \cdot 3$。

**Sylow 2-子群**：阶为 8。$D_4$（二面体群，正方形的对称群）可嵌入 $S_4$：
$$D_4 = \langle (1234), (13) \rangle = \{e, (1234), (13)(24), (1432), (13), (24), (12)(34), (14)(23)\}。$$
$n_2 = 3$，共 3 个 Sylow 2-子群。

**Sylow 3-子群**：阶为 3。$\langle (123) \rangle = \{e, (123), (132)\}$。$n_3 = 4$。

### $GL_2(\mathbb{F}_3)$ 的 Sylow 子群

$|GL_2(\mathbb{F}_3)| = (3^2 - 1)(3^2 - 3) = 8 \cdot 6 = 48 = 2^4 \cdot 3$。

**Sylow 3-子群**：阶为 3。例如 $\left\langle \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \right\rangle$。$n_3 \in \{1, 4, 16\}$，实际 $n_3 = 4$。

**Sylow 2-子群**：阶为 16。$GL_2(\mathbb{F}_3)$ 有一个 Sylow 2-子群同构于半二面体群 $SD_{16}$。

### 应用：15 阶群必循环

$|G| = 15 = 3 \cdot 5$。

$n_5 \mid 3$ 且 $n_5 \equiv 1 \pmod 5$ $\Rightarrow$ $n_5 = 1$。唯一的 Sylow 5-子群 $P_5 \trianglelefteq G$。

$n_3 \mid 5$ 且 $n_3 \equiv 1 \pmod 3$ $\Rightarrow$ $n_3 = 1$。唯一的 Sylow 3-子群 $P_3 \trianglelefteq G$。

$P_3 \cap P_5 = \{e\}$（因阶互素），$|P_3 P_5| = 3 \cdot 5 = 15 = |G|$。故 $G = P_3 \times P_5 \cong C_3 \times C_5 \cong C_{15}$。

## 与其他概念的联系

### 与群上同调的联系

Sylow 第一定理可从群上同调的角度理解。设 $G$ 为有限群，$p \mid |G|$。第一上同调群 $H^1(G, M)$ 分类了 $G$-模 $M$ 的某种扩张。Sylow 子群的存在性与 $G$ 的 $p$-进完备化密切相关。

更具体地，转移映射（transfer）$V: G \to G/[G,G]$ 在 Sylow $p$-子群上的限制提供了从 $G$ 的 Abel 化到 Sylow 子群的映射，这是研究 $G$ 的 $p$-部分结构的重要工具。

### 与局部-整体原则的联系

在有限群论中，Sylow 定理提供了一种"局部到整体"的分析路径：先研究每个素数 $p$ 处的局部结构（Sylow $p$-子群），再通过融合系统（fusion system）和群扩张理论将这些局部信息拼接为全局结构。

这类似于代数数论中的局部-整体原则：研究 $\mathbb{Q}_p$ 上的结构，然后推断 $\mathbb{Q}$ 上的结构。

### 与有限单群分类的联系

Sylow 定理是有限单群分类（CFSG）的基本工具。单群没有非平凡的正规子群，因此对所有 $p$ 都有 $n_p > 1$。通过分析 Sylow 子群的计数约束，可以排除大量可能的群结构，将候选群缩小到已知的单群族。

例如，Feit-Thompson 定理（奇数阶群可解）的证明中，Sylow 分析是核心步骤之一。

## 参考

- Sylow, L. (1872). Théorèmes sur les groupes de substitutions. *Mathematische Annalen*, 5(4), 584–594.
- Wielandt, H. (1959). Ein Beweis für die Existenz der Sylowgruppen. *Archiv der Mathematik*, 10, 401–402.
- Dummit, D. S., & Foote, R. M. (2004). *Abstract Algebra* (3rd ed.). Wiley.
- Rose, J. S. (1978). *A Course on Group Theory*. Cambridge University Press.
