---
title: "README"
msc_primary: 68

  - 68V20
msc_secondary: ["08A99", "03B35", "68T99"]
processed_at: '2026-04-05'
references:
  textbooks:
    - id: artin_algebra
      type: textbook
      title: Algebra
      authors:
      - Michael Artin
      publisher: Pearson
      edition: 2nd
      year: 2011
      isbn: 978-0132413770
      msc: 16-01
      chapters: 
      url: ~
    - id: strang_la
      type: textbook
      title: Introduction to Linear Algebra
      authors:
      - Gilbert Strang
      publisher: Wellesley-Cambridge Press
      edition: 5th
      year: 2016
      isbn: 978-0980232776
      msc: 15-01
      chapters: 
      url: ~
    - id: dummit_foote_aa
      type: textbook
      title: Abstract Algebra
      authors:
      - David S. Dummit
      - Richard M. Foote
      publisher: Wiley
      edition: 3rd
      year: 2003
      isbn: 978-0471433347
      msc: 13-01
      chapters: 
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 代数结构教学资源：群论核心定理

本节提供群论、环论与模论中的核心教学材料，聚焦于严格定义、定理证明与典型例子，适用于代数结构课程的补充学习与复习。

## 1. 群的基本结构与 Lagrange 定理

### 1.1 群的定义与子群

**定义 1.1（群）**. 集合 $G$ 配备二元运算 $\cdot$ 称为群，若满足：
1. **结合律**：$(ab)c = a(bc)$ 对所有 $a, b, c \in G$；
2. **单位元**：存在 $e \in G$ 使 $ea = ae = a$；
3. **逆元**：对每个 $a \in G$，存在 $a^{-1} \in G$ 使 $aa^{-1} = a^{-1}a = e$。

**定义 1.2（子群）**. 子集 $H \subseteq G$ 称为子群（记 $H \leq G$），若 $H$ 在 $G$ 的运算下自身构成群。

**命题 1.3（子群判据）**. $H \subseteq G$ 为子群当且仅当 $H \neq \emptyset$ 且对任意 $a, b \in H$ 有 $ab^{-1} \in H$。

### 1.2 Lagrange 定理

**定义 1.4（陪集）**. 设 $H \leq G$。$H$ 的左陪集为 $aH = \{ah : h \in H\}$，右陪集为 $Ha = \{ha : h \in H\}$。

**定理 1.5（Lagrange）**. 设 $G$ 为有限群，$H \leq G$。则 $|H|$ 整除 $|G|$，且 $[G:H] = |G|/|H|$ 为 $H$ 的左陪集个数。

*证明*. 定义映射 $\phi: H \to aH$，$h \mapsto ah$。这是双射（逆为 $ah \mapsto h$），故每个左陪集与 $H$ 等势。左陪集划分 $G$（对 $a, b \in G$，$aH = bH$ 或 $aH \cap bH = \emptyset$），故 $|G| = |H| \cdot [G:H]$。$\square$

**推论 1.6**. 有限群 $G$ 中任意元素 $a$ 的阶整除 $|G|$，故 $a^{|G|} = e$。

## 2. 正规子群与商群

### 2.1 正规子群

**定义 2.1（正规子群）**. 子群 $N \leq G$ 称为正规的（记 $N \trianglelefteq G$），若 $gNg^{-1} = N$ 对所有 $g \in G$ 成立，等价地 $gN = Ng$。

**命题 2.2**. 设 $\phi: G \to H$ 为群同态。则 $\ker(\phi) \trianglelefteq G$。

*证明*. 对 $g \in G$，$n \in \ker(\phi)$，$\phi(gng^{-1}) = \phi(g)\phi(n)\phi(g)^{-1} = \phi(g)e\phi(g)^{-1} = e$，故 $gng^{-1} \in \ker(\phi)$。$\square$

### 2.2 商群与同态基本定理

**定理 2.3（商群）**. 设 $N \trianglelefteq G$。陪集集合 $G/N = \{gN : g \in G\}$ 配备运算 $(gN)(hN) = (gh)N$ 构成群。

*证明*. 运算良定义：若 $gN = g'N$，$hN = h'N$，则 $g' = gn_1$，$h' = hn_2$，$g'h'N = gn_1hn_2N = gh(h^{-1}n_1h)n_2N = ghN$（因 $N$ 正规，$h^{-1}n_1h \in N$）。群公理继承自 $G$。$\square$

**定理 2.4（第一同构定理）**. 设 $\phi: G \to H$ 为群同态。则：

$$G/\ker(\phi) \cong \operatorname{Im}(\phi).$$

*证明*. 定义 $\bar{\phi}: G/\ker(\phi) \to \operatorname{Im}(\phi)$，$\bar{\phi}(g\ker(\phi)) = \phi(g)$。良定义性：若 $g_1\ker = g_2\ker$，则 $g_1^{-1}g_2 \in \ker$，$\phi(g_1) = \phi(g_2)$。同态性显然。满射显然。单射：若 $\bar{\phi}(g\ker) = e$，则 $\phi(g) = e$，$g \in \ker$。$\square$

## 3. Sylow 定理

**定理 3.1（Sylow 第一定理）**. 设 $G$ 为有限群，$p$ 为素数，$p^n \mid |G|$。则 $G$ 存在阶为 $p^n$ 的子群（称为 Sylow $p$-子群）。

*证明*. 对 $|G|$ 归纳。考虑 $G$ 的类方程：

$$|G| = |Z(G)| + \sum_{i} [G:C_G(g_i)],$$

其中求和遍历非平凡共轭类代表元。若 $p \nmid |Z(G)|$，则某 $[G:C_G(g_i)]$ 不被 $p$ 整除，故 $p^n \mid |C_G(g_i)| < |G|$，由归纳 $C_G(g_i)$ 有 Sylow $p$-子群。若 $p \mid |Z(G)|$，由 Cauchy 定理 $Z(G)$ 有 $p$-阶子群 $N \trianglelefteq G$，对 $G/N$ 用归纳。$\square$

**定理 3.2（Sylow 第二定理）**. $G$ 的任意两个 Sylow $p$-子群共轭。

**定理 3.3（Sylow 第三定理）**. Sylow $p$-子群的个数 $n_p$ 满足 $n_p \equiv 1 \pmod{p}$ 且 $n_p \mid |G|/p^n$。

## 4. 例子

### 4.1 例子：$S_3$ 的结构

对称群 $S_3 = \{e, (12), (13), (23), (123), (132)\}$，阶为 6。
- 子群：$\{e\}$，$\langle (12) \rangle = \{e, (12)\}$，$\langle (123) \rangle = \{e, (123), (132)\}$，$S_3$；
- 正规子群：$\{e\}$，$A_3 = \langle (123) \rangle$，$S_3$；
- 商群：$S_3/A_3 \cong \mathbb{Z}_2$。

验证 Lagrange 定理：$A_3$ 的阶为 3，$[S_3:A_3] = 6/3 = 2$。

### 4.2 例子：二面体群 $D_4$

$D_4 = \{e, r, r^2, r^3, s, sr, sr^2, sr^3\}$，$r^4 = e$，$s^2 = e$，$srs = r^{-1}$，阶为 8。
- Sylow 2-子群：$D_4$ 自身（阶为 8 = $2^3$）；
- 子群 $\langle r \rangle \cong \mathbb{Z}_4$ 为正规子群；
- 另有两个 Klein 四元群正规子群：$\{e, r^2, s, sr^2\}$ 和 $\{e, r^2, sr, sr^3\}$。

## 5. 交叉引用

- [群论基础](docs/02-代数结构/02-核心理论/群论/01-群论-增强版.md) — 更系统的群论内容
- [环论基础](docs/02-代数结构/02-核心理论/环论/01-环论基础.md) — 环与理想的结构
- [模论基础](docs/02-代数结构/02-核心理论/模论-基础.md) — 模与同态序列
- [表示论](docs/02-代数结构/02-核心理论/表示论-基础.md) — 群表示与特征标
- [Galois理论](docs/02-代数结构/02-核心理论/Galois理论/01-Galois理论基础.md) — 域扩张与 Galois 群

---

**适用**：docs/02-代数结构/08-教学资源/
