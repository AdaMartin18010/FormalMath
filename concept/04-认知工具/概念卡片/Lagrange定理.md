---
msc_primary: "20Dxx"
msc_secondary:
  - 20F16
  - 20E07
---

# 概念卡片：Lagrange定理

## 严格定义

设 $G$ 为有限群，$H \leq G$ 为 $G$ 的子群。

**Lagrange 定理**：子群 $H$ 的阶整除群 $G$ 的阶，即
$$|H| \mid |G|。$$
等价地，指数 $[G : H] = |G| / |H|$ 是整数。

**推广**：对无限群，Lagrange 定理以指数形式表述：$H \leq G$ 则 $|G| = |H| \cdot [G : H]$（在基数算术意义下）。

**推论**：
1. 任意元素 $g \in G$ 的阶整除 $|G|$；
2. $g^{|G|} = e$ 对所有 $g \in G$；
3. 若 $|G|$ 为素数，则 $G$ 为循环群。

## 历史背景

Lagrange 定理是群论中最古老的结果之一，但其现代形式经历了漫长的演化。

**Lagrange 的原始工作（1771）**：Joseph-Louis Lagrange（1736–1813）在 1771 年的论文《关于代数方程解的反思》中研究了对称群 $S_n$ 的子群。他证明了：若 $H \leq S_n$，则 $|H|$ 整除 $n!$。Lagrange 的证明基于陪集分解的思想，但他并未使用"群"的现代概念——他讨论的是"根的置换"。

**群概念的形成（1850–1900）**：Cayley（1854）给出了群的抽象定义；Jordan（1870）在《置换与代数方程》中系统发展了置换群理论，明确陈述了 Lagrange 定理的陪集证明；Frobenius 和 Burnside 将结果推广到抽象群。

**现代教学地位**：Lagrange 定理通常作为群论入门课程的第一个重要定理。它的证明（陪集划分）极为简洁优美，同时引入了**陪集**、**指数**和**正规化子**等核心概念。

## 直观理解

Lagrange 定理的直观是**"均匀划分"**。

想象群 $G$ 为一个由 $|G|$ 个元素组成的"社会"。子群 $H$ 是一个由 $|H|$ 人组成的"俱乐部"。Lagrange 定理说：整个社会可以被均匀地划分为若干个大小相同的"俱乐部聚会"（陪集），每个聚会恰好有 $|H|$ 人，聚会的总数为 $|G|/|H|$。

**陪集的可视化**：对 $g \in G$，左陪集 $gH = \{gh : h \in H\}$ 是 $H$ 经 $g$ 左乘后的"平移"。关键观察：
- 每个陪集的大小恰好为 $|H|$（因左乘是双射）；
- 不同的陪集互不相交（若 $g_1 H \cap g_2 H \neq \varnothing$，则 $g_1 H = g_2 H$）；
- 所有陪集的并等于 $G$。

因此，$G$ 被分解为 $[G:H]$ 个互不相交的大小为 $|H|$ 的块，$|G| = |H| \cdot [G:H]$。

## 数学例子

### 标准证明

**定理**：$H \leq G$ $\Rightarrow$ $|H| \mid |G|$。

**证明**：在 $G$ 上定义等价关系：$g_1 \sim g_2$ 当且仅当 $g_1^{-1} g_2 \in H$（即 $g_2 \in g_1 H$）。等价类即为左陪集 $gH$。

- 映射 $\phi: H \to gH$，$\phi(h) = gh$ 是双射。故 $|gH| = |H|$。
- 若 $g_1 H \cap g_2 H \neq \varnothing$，则存在 $h_1, h_2 \in H$ 使得 $g_1 h_1 = g_2 h_2$。于是 $g_1 = g_2 h_2 h_1^{-1} \in g_2 H$，故 $g_1 H \subseteq g_2 H$。同理 $g_2 H \subseteq g_1 H$。

因此 $G$ 被划分为互不相交的陪集，每个大小为 $|H|$。设陪集个数为 $[G:H]$，则 $|G| = |H| \cdot [G:H]$。

### 元素的阶

**推论**：$g \in G$ 的阶 $o(g)$ 整除 $|G|$。

**证明**：$\langle g \rangle = \{e, g, g^2, \ldots, g^{o(g)-1}\}$ 是 $G$ 的 $o(g)$ 阶循环子群。由 Lagrange 定理，$o(g) = |\langle g \rangle| \mid |G|$。

### Fermat 小定理与 Euler 定理

**Fermat 小定理**：$p$ 为素数，$p \nmid a$ $\Rightarrow$ $a^{p-1} \equiv 1 \pmod p$。

**证明**：$(\mathbb{Z}/p\mathbb{Z})^\times$ 是 $p-1$ 阶乘法群。$a$ 的剩余类 $\bar{a}$ 属于此群，故 $o(\bar{a}) \mid p-1$。于是 $\bar{a}^{p-1} = \bar{1}$。

**Euler 定理**：$\gcd(a, m) = 1$ $\Rightarrow$ $a^{\varphi(m)} \equiv 1 \pmod m$。

**证明**：$(\mathbb{Z}/m\mathbb{Z})^\times$ 是 $\varphi(m)$ 阶群，同上。

### 素数阶群必循环

**推论**：若 $|G| = p$（素数），则 $G \cong C_p$。

**证明**：取 $g \in G \setminus \{e\}$。$o(g) > 1$ 且 $o(g) \mid p$，故 $o(g) = p$。$\langle g \rangle = G$。

## 与其他概念的联系

### 与 Sylow 定理的联系

Lagrange 定理说：若 $H \leq G$，则 $|H|$ 整除 $|G|$。其逆命题不成立——$d \mid |G|$ 不保证存在 $d$ 阶子群。Sylow 定理部分修复了这一点：对素数幂 $p^n \mid |G|$，存在 $p^n$ 阶子群（Sylow $p$-子群）。

Burnside 的 $p^a q^b$ 定理说：若 $|G| = p^a q^b$，则 $G$ 可解。这一定理的证明中，Sylow 计数与 Lagrange 约束的交互是核心。

### 与数论的联系

Lagrange 定理的数论对应是模算术中的基本约束。例如，证明 Wilson 定理 $(p-1)! \equiv -1 \pmod p$ 时，利用了 $(\mathbb{Z}/p\mathbb{Z})^\times$ 中每个元素都有唯一逆元，且只有 $\pm 1$ 是自逆的——这一观察直接源于 Lagrange 约束下的群结构。

### 与 Galois 理论的联系

在 Galois 理论中，Lagrange 定理对应于域扩张次数的乘法性：若 $F \subseteq K \subseteq L$ 为域塔，则
$$[L : F] = [L : K] \cdot [K : F]。$$
这不是巧合——Galois 群的阶等于对应域扩张的次数，而 Lagrange 定理正是这一乘法性的群论版本。

## 参考

- Dummit, D. S., & Foote, R. M. (2004). *Abstract Algebra* (3rd ed.). Wiley.
- Artin, M. (2011). *Algebra* (2nd ed.). Pearson.
- Lagrange, J.-L. (1771). Réflexions sur la résolution algébrique des équations. *Nouveaux Mémoires de l'Académie royale des Sciences et Belles-Lettres de Berlin*.
- Roth, R. (2001). A history of Lagrange's theorem on groups. *Mathematics Magazine*, 74(2), 99–108.
