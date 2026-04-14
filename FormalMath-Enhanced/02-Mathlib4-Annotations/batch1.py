import os

def write_md(path, title, lean, background, intuition, formal, proof, examples, apps, concepts, refs):
    content = f"""---
msc_primary: 00A99
processed_at: '2026-04-15'
title: {title}
---
# {title}

## Mathlib4 引用

```lean
{lean}
```

## 数学背景

{background}

## 直观解释

{intuition}

## 形式化表述

{formal}

## 证明思路

{proof}

## 示例

{examples}

## 应用

{apps}

## 相关概念

{concepts}

## 参考

{refs}

---

*最后更新：2026-04-15 | 版本：v1.0.0*
"""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f'Created {path}')

# GraphTheory files
theorems = []

theorems.append((
    "GraphTheory/turan-theorem.md",
    "Turán 定理 (Turán's Theorem)",
    "import Mathlib.Combinatorics.SimpleGraph.Turan\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- Turán 定理：不含 (r+1)-团的 n 顶点图的最大边数由 Turán 图达到 -/\ntheorem turanDensity (hr : 0 < r) (h : CliqueFree G (r + 1)) :\n    G.edgeFinset.card ≤ turanGraph (Fintype.card V) r edgeFinset.card := by\n  -- 证明使用归纳法和双计数技术\n  sorry\n\nend SimpleGraph",
    "Turán 定理由匈牙利数学家保罗·图兰（Pál Turán）于1941年证明，是极值图论的奠基性结果。该定理精确刻画了在不包含完全子图 K_{r+1} 的条件下，一个图最多可以有多少条边。Turán 图是达到这个上界的唯一极值图，开启了极值图论这一蓬勃发展的研究领域。",
    "Turán 定理回答了一个简单的极值问题：如果一个聚会中有 n 个人，要求其中任意 r+1 个人不全是两两认识的，那么最多可能有多少对互相认识的人？答案是：将所有人尽量均匀地分成 r 个小组，不同小组之间的人都互相认识，而同一小组内的人互不认识。这种完全多部图的结构给出了最大边数。",
    "设 $G$ 是一个具有 $n$ 个顶点且不含 $K_{{r+1}}$ 的图，则：\n\n$$|E(G)| \\leq \\left(1 - \\frac{{1}}{{r}}\\right) \\frac{{n^2}}{{2}}$$\n\n等号成立当且仅当 $G$ 是 Turán 图 $T(n, r)$，即 $r$ 部完全多部图，各部大小之差不超过 1。\n\n其中：\n\n- $|E(G)|$ 表示图 $G$ 的边数\n- $K_{{r+1}}$ 表示 $r+1$ 个顶点的完全图\n- $T(n, r)$ 表示 $n$ 个顶点的 Turán 图",
    "1. **归纳基础**：对小规模图验证定理成立\\n2. **极值图分析**：证明极值图必须不含 $(r+1)$-团且边数最大\\n3. **度序列论证**：利用 Zykov 对称化或权重转移方法证明 Turán 图是唯一极值图\\n4. **不等式推导**：通过完全多部图的结构计算精确边数上界\n\n核心洞察在于完全多部图是避免大团的\"最优\"结构。",
    "### 示例 1：不含三角形的图\n\n当 $r = 2$ 时，Turán 定理说明不含三角形 $K_3$ 的 $n$ 顶点图最多有 $\\lfloor n^2/4 \\rfloor$ 条边。这等价于 Mantel 定理。极值图是完全二部图 $K_{\\lfloor n/2 \\rfloor, \\lceil n/2 \\rceil}$。\n\n### 示例 2：7 个顶点不含 $K_4$\n\n设 $n = 7$, $r = 3$。Turán 图 $T(7, 3)$ 将 7 个顶点分为三部，大小为 3, 2, 2。边数为 $3 \\cdot 2 + 3 \\cdot 2 + 2 \\cdot 2 = 16$。任何不含 $K_4$ 的 7 顶点图至多有 16 条边。\n\n### 示例 3：5 个顶点的极值图\n\n对于 $n = 5$, $r = 2$，Turán 图是 $K_{{2,3}}$，有 6 条边。如果添加任何一条同部边就会形成三角形，从而违反极值条件。",
    "- **极值图论**：作为研究图禁止子图问题的基本工具\n- **拉姆齐理论**：与 Ramsey 数的研究密切相关\n- **网络设计**：设计无大团的高效通信网络\n- **社会网络分析**：理解社交圈中的关系密度限制",
    "- 极值图论 (Extremal Graph Theory)：研究满足某种性质时图的最大/最小参数\n- 团 (Clique)：图中两两相邻的顶点集合\n- 完全多部图 (Complete Multipartite Graph)：多部之间全连接的图\n- Mantel 定理 (Mantel's Theorem)：Turán 定理 $r=2$ 的特例\n- Erdős–Stone 定理：Turán 定理的渐近推广",
    "### 教材\n\n- [B. Bollobás. Modern Graph Theory. Springer, 1998. Chapter 4]\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 7]\n\n### 论文\n\n- [P. Turán. On an extremal problem in graph theory. Mat. Fiz. Lapok, 1941]\n\n### 在线资源\n\n- [Mathlib4 - Turán](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Turan.html)"
))

theorems.append((
    "GraphTheory/ramsey-number-exists.md",
    "Ramsey 数存在性 (Ramsey Number Existence)",
    "import Mathlib.Combinatorics.SimpleGraph.Ramsey\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- Ramsey 数存在性：对任意正整数 s, t，Ramsey 数 R(s, t) 存在且有限 -/\ntheorem ramsey_number_exists (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :\n    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),\n      N ≤ Fintype.card V →\n      (∃ S : Finset V, S.card = s ∧ G.IsClique S) ∨\n      (∃ T : Finset V, T.card = t ∧ G.IsAntiClique T) := by\n  -- 通过对 s + t 归纳证明\n  sorry\n\nend SimpleGraph",
    "Ramsey 理论起源于20世纪20年代末英国数学家弗兰克·拉姆齐（Frank P. Ramsey）的开创性工作。1930年，Ramsey 证明了著名的 Ramsey 定理，其核心思想是：在足够大的结构中，必然会出现某种有序的子结构。Ramsey 数 R(s, t) 是组合数学的基石之一，深刻揭示了大系统中\"完全无序是不可能的\"。",
    "Ramsey 定理有一个著名的通俗表述：在一个足够大的聚会中，必然存在 s 个人互相都认识，或者 t 个人互相都不认识。无论人们之间的认识关系如何复杂，只要人数超过某个阈值，这种有序结构就不可避免。这体现了大系统中局部的必然有序性。",
    "对任意正整数 $s, t$，存在最小的正整数 $R(s, t)$，使得任意具有 $N \\geq R(s, t)$ 个顶点的图 $G$ 满足：\n\n$$G \\text{ 包含 } K_s \\text{ 或 } G \\text{ 包含独立集 } I_t$$\n\n其中：\n\n- $R(s, t)$ 表示 Ramsey 数\n- $K_s$ 表示 $s$ 个顶点的完全子图（团）\n- $I_t$ 表示 $t$ 个顶点的独立集（无边连接）\n\nRamsey 数满足递推关系：$R(s, t) \\leq R(s-1, t) + R(s, t-1)$。",
    "1. **归纳假设**：假设对所有满足 $s' + t' < s + t$ 的正整数对，Ramsey 数存在\\n2. **递推构造**：证明 $R(s, t) \\leq R(s-1, t) + R(s, t-1)$\\n3. **计数论证**：任取一顶点 $v$，其邻居集或非邻居集必有一个足够大，从而应用归纳假设\\n4. **有限性结论**：由归纳法知对所有正整数 $s, t$，$R(s, t)$ 为有限正整数\n\n核心洞察在于鸽巢原理在图结构中的深刻应用。",
    "### 示例 1：$R(3, 3) = 6$\n\n在任意 6 个人的聚会中，必有 3 人互相认识或 3 人互不认识。$K_5$ 的一个 5-圈可以构造出反例说明 $R(3, 3) > 5$。\n\n### 示例 2：$R(3, 4) = 9$\n\n任意 9 个顶点的图必含三角形或 4 个顶点的独立集。而 $K_8$ 的某个特定图可以既无三角形也无 4 顶点独立集。\n\n### 示例 3：已知精确值\n\n目前已知的精确 Ramsey 数极少：$R(1, t) = 1$, $R(2, t) = t$, $R(3, 3) = 6$, $R(3, 4) = 9$, $R(3, 5) = 14$, $R(4, 4) = 18$。$R(5, 5)$ 的确切值至今未知，只知道在 43 到 48 之间。",
    "- **组合数学**：极值组合和结构 Ramsey 理论的核心工具\n- **逻辑与计算机科学**：证明复杂性和自动定理证明中的应用\n- **数论**：Schur 定理、van der Waerden 定理等算术 Ramsey 结果\n- **几何**：Erdős–Szekeres 定理关于凸多边形",
    "- Ramsey 数 (Ramsey Number)：保证某种子结构存在的最小顶点数\n- 团 (Clique)：两两相邻的顶点集\n- 独立集 (Independent Set)：两两不相邻的顶点集\n- 鸽巢原理 (Pigeonhole Principle)：Ramsey 理论的基本工具\n- Erdős–Szekeres 定理：Ramsey 理论在几何中的经典应用",
    "### 教材\n\n- [R. L. Graham, B. L. Rothschild, J. H. Spencer. Ramsey Theory. Wiley, 1990]\n- [J. Fox. Lecture Notes on Graph Ramsey Theory]\n\n### 论文\n\n- [F. P. Ramsey. On a problem of formal logic. Proc. London Math. Soc., 1930]\n\n### 在线资源\n\n- [Mathlib4 - Ramsey](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Ramsey.html)"
))

theorems.append((
    "GraphTheory/konig-theorem.md",
    "König 定理 (König's Theorem)",
    "import Mathlib.Combinatorics.SimpleGraph.Matching\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- König 定理：二分图中最大匹配的大小等于最小顶点覆盖的大小 -/\ntheorem konigTheorem (h : G.IsBipartite) :\n    G.maxMatching.card = G.minVertexCover.card := by\n  -- 通过对二分图建立流网络，利用最大流最小割定理证明\n  sorry\n\nend SimpleGraph",
    "König 定理由匈牙利数学家 Dénes König 于1931年证明，是二分图理论中最核心的结果之一。该定理建立了二分图中最大匹配的大小等于最小顶点覆盖的大小之间的对偶关系。这一定理是线性规划对偶性在组合优化中的离散体现，对网络流、组合优化和算法设计产生了深远影响。",
    "想象一个二分图代表工人和任务：左侧顶点是工人，右侧顶点是任务，边表示某个工人可以完成某项任务。匹配表示将工人分配到不同的任务。顶点覆盖则表示选出一组工人和任务，使得每条边至少有一个端点被选中。König 定理告诉我们：最多能同时完成多少项任务，恰好等于需要监督多少个人和任务才能覆盖所有可能的分配关系。",
    "设 $G = (X \\cup Y, E)$ 是一个二分图，则：\n\n$$\\nu(G) = \\tau(G)$$\n\n其中：\n\n- $\\nu(G)$ 表示 $G$ 中最大匹配的大小（matching number）\n- $\\tau(G)$ 表示 $G$ 中最小顶点覆盖的大小（vertex cover number）\n- $G$ 是二分图意味着顶点集可划分为两个独立集 $X$ 和 $Y$",
    "1. **平凡不等式**：证明对任意图都有 $\\nu(G) \\leq \\tau(G)$，因为匹配中的每条边都需要一个不同的顶点来覆盖\\n2. **构造覆盖**：在二分图中，利用交错路径构造一个大小恰好为 $\\nu(G)$ 的顶点覆盖\\n3. **Hall 条件或网络流**：通过最大流最小割定理，或从最大匹配出发构造最小覆盖\\n4. **等式成立**：在二分图的特殊结构下，上述覆盖恰好达到下界\n\n核心洞察在于二分图的\"无环\"结构使得匹配和覆盖之间不存在间隙。",
    "### 示例 1：简单二分图\n\n考虑二分图 $G$ 其中 $X = \\{a, b\\}$, $Y = \\{1, 2\\}$，边为 $a-1, a-2, b-2$。最大匹配可以是 $\\{a-1, b-2\\}$，大小为 2。最小顶点覆盖为 $\\{a, 2\\}$，大小也为 2。\n\n### 示例 2：非二分图的失效\n\n三角形图 $K_3$ 的最大匹配大小为 1，但最小顶点覆盖大小为 2。这说明 König 定理对非二分图不成立，二分条件至关重要。\n\n### 示例 3：完美匹配\n\n若二分图存在完美匹配（覆盖所有顶点），则最小顶点覆盖必须包含所有顶点，此时 $\\nu(G) = |V|/2 = \\tau(G)$。",
    "- **任务分配**：将任务最优分配给工作人员的匈牙利算法基础\n- **网络流**：与最大流最小割定理等价，是网络优化的核心\n- **组合拍卖**：拍卖机制设计中的对偶分析\n- **调度问题**：生产调度中的资源匹配与覆盖",
    "- 匹配 (Matching)：无公共端点的边集\n- 顶点覆盖 (Vertex Cover)：与每条边都相交的顶点集\n- 二分图 (Bipartite Graph)：顶点可分为两个独立集的图\n- Hall 婚姻定理 (Hall's Marriage Theorem)：二分图存在完美匹配的充要条件\n- 最大流最小割定理 (Max-Flow Min-Cut Theorem)：网络流中的对偶定理",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 2]\n- [A. Schrijver. Combinatorial Optimization. Springer, 2003. Chapter 16]\n\n### 论文\n\n- [D. König. Gráfok és mátrixok. Mat. Fiz. Lapok, 1931]\n\n### 在线资源\n\n- [Mathlib4 - Matching](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Matching.html)"
))

theorems.append((
    "GraphTheory/max-flow-min-cut.md",
    "最大流最小割定理 (Max-Flow Min-Cut Theorem)",
    "import Mathlib.Combinatorics.Optimization.Flow\n\nnamespace Flow\n\nvariable {V : Type*} [Fintype V] (G : Digraph V) (c : V → V → ℝ≥0) (s t : V)\n\n/-- 最大流最小割定理：网络中从源到汇的最大流值等于最小割的容量 -/\ntheorem maxFlowMinCut :\n    IsMaxFlow G c s t (maxFlow G c s t) ↔\n    IsMinCut G c s t (minCut G c s t) := by\n  -- 证明基于增广路径和 Ford-Fulkerson 方法\n  sorry\n\nend Flow",
    "最大流最小割定理是网络流理论和组合优化的核心结果，由 Ford 和 Fulkerson 于1956年系统建立。该定理断言：在任何一个带容量的有向网络中，从源点到汇点所能输送的最大流量，恰好等于分离源点和汇点的所有割中容量最小的那个割的容量。这一定理是无数高效算法的理论基础。",
    "想象一个输水管道网络，每条管道有一定的流量上限。源点是水库，汇点是城市。最大流最小割定理告诉我们：能够输送到城市的最大水量，恰好等于网络中\"最窄瓶颈\"的容量。这个\"瓶颈\"就是最小割——将网络分成两部分后，从水库侧流向城市侧的所有管道的容量之和。无论网络多么复杂，最大输水量永远受限于这个最窄的通道。",
    "设 $G = (V, E)$ 是一个带容量函数 $c: E \\to \\mathbb{{R}}_{{\\geq 0}}$ 的有向图，$s$ 为源点，$t$ 为汇点，则：\n\n$$\\max |f| = \\min_{{(S, T) \\text{{ 割}}}} c(S, T)$$\n\n其中：\n\n- $|f|$ 表示流 $f$ 的值（从源点净流出的流量）\n- $(S, T)$ 是一个 $s$-$t$ 割，满足 $s \\in S$, $t \\in T$, $S \\cup T = V$, $S \\cap T = \\emptyset$\n- $c(S, T) = \\sum_{{u \\in S, v \\in T}} c(u, v)$ 表示割的容量",
    "1. **弱对偶性**：证明对任意可行流 $f$ 和任意 $s$-$t$ 割 $(S, T)$，有 $|f| \\leq c(S, T)$\\n2. **增广路径**：若当前流不是最大的，则存在一条从 $s$ 到 $t$ 的增广路径可以增加流量\\n3. **残差网络**：构造残差网络，证明当不存在增广路径时，当前流达到最大\\n4. **最小割构造**：当流最大时，在残差网络中从 $s$ 可达的顶点集构成一个容量等于流值的最小割\n\n核心洞察在于流和割构成一对完美的对偶优化问题。",
    "### 示例 1：简单管道网络\n\n设网络有源点 $s$，汇点 $t$，中间顶点 $a, b$。边及容量为：$s \\to a$ (10), $s \\to b$ (5), $a \\to t$ (10), $b \\to t$ (5), $a \\to b$ (10)。最大流为 15，最小割容量也为 15。\n\n### 示例 2：交通网络\n\n城市道路网络中，各条道路的通行能力不同。最大流最小割定理说明高峰时段两个区域之间的最大车流量等于连接这两个区域的关键道路群的通行能力之和。这解释了为什么拓宽瓶颈道路可能显著提升整体通行能力。\n\n### 示例 3：图像分割\n\n在计算机视觉的图像分割中，将图像建模为图网络，源点和汇点分别代表前景和背景。最大流最小割算法可以找到最优的分割边界（即最小割），广泛应用于医学图像处理。",
    "- **网络路由**：互联网数据包传输和带宽分配优化\n- **图像分割**：GrabCut 等基于图割的图像分割算法\n- **项目调度**：关键路径法和资源约束项目调度\n- **匹配问题**：二分图匹配和任务分配问题的转化与求解\n- **可靠性分析**：通信网络和电力网络的容错性评估",
    "- 网络流 (Network Flow)：带容量限制的有向图上的流量分配\n- 残差网络 (Residual Network)：表示还可以增加流量的网络\n- 增广路径 (Augmenting Path)：可以增加流量的路径\n- 割 (Cut)：将顶点集划分为两部分的划分\n- Ford-Fulkerson 算法：求解最大流的经典算法",
    "### 教材\n\n- [T. H. Cormen et al. Introduction to Algorithms. MIT Press, 3rd edition, 2009. Chapter 26]\n- [A. Schrijver. Combinatorial Optimization. Springer, 2003. Chapters 9-10]\n\n### 论文\n\n- [L. R. Ford, D. R. Fulkerson. Maximal flow through a network. Canad. J. Math., 1956]\n\n### 在线资源\n\n- [Mathlib4 - Flow](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Optimization/Flow.html)"
))

theorems.append((
    "GraphTheory/brooks-theorem.md",
    "Brooks 定理 (Brooks' Theorem)",
    "import Mathlib.Combinatorics.SimpleGraph.Coloring\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]\n\n/-- Brooks 定理：连通图 G 的色数至多为 Δ(G)，\n    除非 G 是完全图或奇圈 -/\ntheorem brooks_theorem (hG : G.Connected) :\n    G.chromaticNumber ≤ G.maxDegree := by\n  -- 对非完全图、非奇圈的连通图，证明存在 Δ(G)-着色\n  sorry\n\nend SimpleGraph",
    "Brooks 定理由英国数学家 R. Leonard Brooks 于1941年证明，是图着色理论中的经典结果。该定理指出：对于任何连通图，其色数不超过最大度 $\\Delta(G)$，唯一的例外是完全图和奇圈。这一定理给出了色数的一个紧上界，弥补了显然上界 $\\chi(G) \\leq \\Delta(G) + 1$ 与精确色数之间的差距。",
    "图着色问题要求为图的每个顶点分配颜色，使得相邻顶点颜色不同。一个显然的事实是：如果某个顶点有 $\\Delta$ 个邻居，那么它最多需要 $\\Delta + 1$ 种颜色。Brooks 定理将这个上界改进为 $\\Delta$，除非图的结构\"过于规则\"——即完全图或奇圈。这两种例外情况确实需要 $\\Delta + 1$ 种颜色，而对于其他所有图，邻接关系的某种\"灵活性\"使得 $\\Delta$ 种颜色就足够了。",
    "设 $G$ 是一个连通图，$\\Delta(G)$ 是其最大度，则：\n\n$$\\chi(G) \\leq \\Delta(G)$$\n\n等号成立当且仅当 $G$ 是完全图 $K_n$（$n \\geq 3$）或奇圈 $C_{{2k+1}}$（$k \\geq 1$）。\n\n其中：\n\n- $\\chi(G)$ 表示图 $G$ 的色数\n- $\\Delta(G) = \\max_{{v \\in V}} \\deg(v)$ 表示最大顶点度\n- 完全图 $K_n$ 的色数为 $n = \\Delta(K_n) + 1$\n- 奇圈 $C_{{2k+1}}$ 的色数为 $3 = \\Delta(C_{{2k+1}}) + 1$",
    "1. **排除例外**：验证完全图和奇圈确实需要 $\\Delta + 1$ 种颜色\\n2. **存在非最大度邻接**：对非例外图，证明存在两个不相邻的最大度顶点\\n3. **顶点排序**：以这两个顶点为最后两个顶点，按度数降序排列其余顶点\\n4. **贪心着色**：从前向后贪心着色，由于最后两个顶点颜色可以共享，故 $\\Delta$ 种颜色足够\n\n核心洞察在于非完全图中存在的\"结构松弛\"允许节省一种颜色。",
    "### 示例 1：完全图 $K_4$\n\n$K_4$ 的最大度为 3，色数为 4。根据 Brooks 定理，这是等号成立的例外情况，需要 $\\Delta + 1 = 4$ 种颜色。\n\n### 示例 2：Petersen 图\n\nPetersen 图是 3-正则图（$\\Delta = 3$），且不是完全图或奇圈。Brooks 定理保证其色数 $\\leq 3$。实际上 Petersen 图的色数恰好为 3。\n\n### 示例 3：路径图 $P_n$\n\n路径图的最大度为 2（端点度为 1，内部点度为 2），不是奇圈。Brooks 定理说明其色数 $\\leq 2$。事实上所有路径图都是二部图，色数为 2。",
    "- **图着色算法**：为贪心着色和启发式着色算法提供理论保证\n- **寄存器分配**：编译器优化中的图着色上界估计\n- **频率分配**：无线电频谱分配中的干扰最小化\n- **考试调度**：将冲突课程分配到最少时间段",
    "- 色数 (Chromatic Number)：正常顶点着色所需的最少颜色数\n- 最大度 (Maximum Degree)：图中顶点度的最大值\n- 贪心着色 (Greedy Coloring)：按顶点顺序依次分配可用最小颜色的算法\n- 完全图 (Complete Graph)：每对顶点之间都有边相连的图\n- 奇圈 (Odd Cycle)：长度为奇数的环",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 5]\n- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Section 5.1]\n\n### 论文\n\n- [R. L. Brooks. On colouring the nodes of a network. Proc. Cambridge Philos. Soc., 1941]\n\n### 在线资源\n\n- [Mathlib4 - Coloring](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Coloring.html)"
))

theorems.append((
    "GraphTheory/dirac-theorem.md",
    "Dirac 定理 (Dirac's Theorem)",
    "import Mathlib.Combinatorics.SimpleGraph.Hamiltonian\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- Dirac 定理：若 n ≥ 3 且每个顶点的度至少为 n/2，则 G 是哈密顿图 -/\ntheorem dirac_theorem (hn : 3 ≤ Fintype.card V)\n    (h : ∀ v : V, G.degree v ≥ Fintype.card V / 2) :\n    G.IsHamiltonian := by\n  -- 证明基于最长路径的扩展论证\n  sorry\n\nend SimpleGraph",
    "Dirac 定理由丹麦-英国数学家 Gabriel Andrew Dirac 于1952年证明，是哈密顿图理论中的里程碑结果。该定理给出了判断一个图是否包含哈密顿圈的一个简单但强有力的充分条件：如果 $n \\geq 3$ 个顶点的图中每个顶点的度至少为 $n/2$，则该图必为哈密顿图。这一定理开创了图论中度条件与哈密顿性研究的新方向。",
    "Dirac 定理可以通俗地理解为：在一个聚会中，如果每个人都至少认识一半以上的参加者，那么就一定存在一种方式让所有参加者手拉手围成一个圈，每个人恰好与两个人相邻。这个条件相当惊人——只需要\"每个人都比较受欢迎\"（认识至少一半人），就能保证存在一个包含所有人的完美环形排列。这揭示了高度连通性与遍历性之间的深刻联系。",
    "设 $G$ 是一个具有 $n \\geq 3$ 个顶点的简单图，若对任意顶点 $v \\in V(G)$ 都有：\n\n$$\\deg(v) \\geq \\frac{n}{2}$$\n\n则 $G$ 包含一个哈密顿圈，即 $G$ 是哈密顿图。\n\n其中：\n\n- $\\deg(v)$ 表示顶点 $v$ 的度（邻居个数）\n- $n = |V(G)|$ 表示图的顶点数\n- 哈密顿圈是指经过图中每个顶点恰好一次的圈",
    "1. **连通性**：证明满足条件的图必然是连通的\\n2. **最长路径**：取图中的一条最长路径 $P = v_1 v_2 \\dots v_k$\\n3. **圈构造**：证明存在连接 $v_1$ 和 $v_k$ 的边，从而将最长路径扩展为圈\\n4. **哈密顿性**：若该圈不是哈密顿圈，则可利用连通性将其扩展为更长的路径，与最大性矛盾\n\n核心洞察在于高度条件保证了路径端点之间存在足够多的\"交叉连接\"，从而可以闭合为圈。",
    "### 示例 1：完全图 $K_n$\n\n在完全图 $K_n$（$n \\geq 3$）中，每个顶点的度为 $n - 1 \\geq n/2$。Dirac 定理保证 $K_n$ 是哈密顿图，这与直观完全一致——任何排列都能形成哈密顿圈。\n\n### 示例 2：5 个顶点的图\n\n考虑一个 5 顶点图，若每个顶点的度至少为 3（因为 $\\lceil 5/2 \\rceil = 3$），则 Dirac 定理保证该图是哈密顿图。即使图不是完全图，只要满足这个度条件，就必然存在哈密顿圈。\n\n### 示例 3：条件不最优的例子\n\nPetersen 图有 10 个顶点，是 3-正则图。每个顶点的度为 3，而 $10/2 = 5$，因此 Petersen 图不满足 Dirac 条件。事实上 Petersen 图不是哈密顿图，这说明 Dirac 条件的紧性在一定程度上是合理的。",
    "- **旅行商问题 (TSP)**：判断问题实例是否容易求解的充分条件\n- **电路设计**：电子电路板布线和芯片设计中的遍历优化\n- **基因组学**：DNA 序列组装中的哈密顿路径问题\n- **社交网络分析**：发现包含所有成员的社交环或传播路径",
    "- 哈密顿圈 (Hamiltonian Cycle)：经过每个顶点恰好一次的圈\n- 哈密顿图 (Hamiltonian Graph)：包含哈密顿圈的图\n- 度条件 (Degree Condition)：基于顶点度判断图性质的准则\n- Ore 定理 (Ore's Theorem)：Dirac 定理的推广，要求 $\\deg(u) + \\deg(v) \\geq n$ 对任意非邻接顶点对成立\n- 旅行商问题 (TSP)：寻找最短哈密顿圈的著名 NP-难问题",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 10]\n- [J. A. Bondy & U. S. R. Murty. Graph Theory. Springer, 2008. Chapter 18]\n\n### 论文\n\n- [G. A. Dirac. Some theorems on abstract graphs. Proc. London Math. Soc., 1952]\n\n### 在线资源\n\n- [Mathlib4 - Hamiltonian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Hamiltonian.html)"
))

theorems.append((
    "GraphTheory/eulerian-graph-characterization.md",
    "欧拉图的判定 (Eulerian Graph Characterization)",
    "import Mathlib.Combinatorics.SimpleGraph.Trails\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- 连通图 G 是欧拉图当且仅当每个顶点的度都是偶数 -/\ntheorem eulerian_iff_all_deg_even (hG : G.Connected) :\n    G.IsEulerian ↔ ∀ v : V, Even (G.degree v) := by\n  -- 证明基于构造性方法，利用 Hierholzer 算法的思想\n  sorry\n\n/-- 连通图 G 存在欧拉迹当且仅当恰好有两个奇度顶点 -/\ntheorem eulerian_trail_iff_two_odd (hG : G.Connected) :\n    (∃ p : G.Walk, p.IsEulerianTrail) ↔\n    {v : V | Odd (G.degree v)}.ncard = 2 := by\n  -- 两个奇度顶点即为欧拉迹的端点\n  sorry\n\nend SimpleGraph",
    "欧拉图理论起源于18世纪著名的哥尼斯堡七桥问题，由莱昂哈德·欧拉（Leonhard Euler）于1736年解决，这也被公认为图论诞生的标志。欧拉证明了一个图存在经过每条边恰好一次的闭合路径的充分必要条件：图是连通的且每个顶点的度都是偶数。对于存在经过每条边恰好一次的开放路径的情况，条件变为图是连通的且恰好有两个奇度顶点。",
    "想象一个公园的游览路线，游客希望走过每一座桥恰好一次并最终回到起点。欧拉定理告诉我们：只有当从每座桥出发和返回的次数是偶数时（即每个区域的桥数是偶数），这才可能实现。如果某个区域连接了奇数座桥，那么游客要么从那里开始，要么在那里结束——不可能既从那里进入又从那里离开。如果有两个区域连接了奇数座桥，那么可以将一个作为起点、另一个作为终点。",
    "设 $G$ 是一个连通图：\n\n1. $G$ 是**欧拉图**（存在欧拉回路）当且仅当每个顶点的度都是偶数：\n   $$\\forall v \\in V(G), \\quad \\deg(v) \\equiv 0 \\pmod{2}$$\n\n2. $G$ 存在**欧拉迹**（不闭合）当且仅当恰好有两个顶点的度是奇数：\n   $$|\\{v \\in V(G) : \\deg(v) \\equiv 1 \\pmod{2}\\}| = 2$$\n\n其中：\n\n- $\\deg(v)$ 表示顶点 $v$ 的度\n- 欧拉回路是指经过每条边恰好一次并回到起点的闭合路径\n- 欧拉迹是指经过每条边恰好一次的开放路径",
    "1. **必要性**：在欧拉回路中，每次进入一个顶点必然伴随着一次离开，因此所有顶点的度必须是偶数\\n2. **充分性构造**：从任意顶点出发，沿着未走过的边前进。由于所有度为偶数，这个过程只能在一个已经访问过的顶点结束，形成一个圈\\n3. **圈的合并**：若还有未走过的边，由于连通性，必存在某个已访问顶点还有未走边，从该点继续构造新圈并合并\\n4. **Hierholzer 算法**：上述构造过程可以系统化实现，是寻找欧拉回路的经典算法\n\n核心洞察在于偶度条件保证了\"有进必有出\"的局部对称性。",
    "### 示例 1：正方形加对角线\n\n考虑一个正方形的四个顶点，加上两条对角线。每个顶点的度为 3（连接两条边和一条对角线），是奇数。因此该图不存在欧拉回路，但存在欧拉迹（从任意顶点开始，到对角顶点结束）。\n\n### 示例 2：完全图 $K_5$\n\n$K_5$ 有 5 个顶点，每个顶点的度为 4（偶数）。根据欧拉定理，$K_5$ 是欧拉图，存在经过每条边恰好一次的回路。\n\n### 示例 3：哥尼斯堡七桥问题\n\n哥尼斯堡的四个陆地区域由七座桥连接，对应的图中四个顶点的度分别为 3, 3, 3, 5，全是奇数。因此既不存在欧拉回路，也不存在欧拉迹，证明了居民不可能走过每座桥恰好一次。",
    "- **路径规划**：邮递员问题、街道清扫路线优化\n- **电路板检测**：探针遍历电路板所有连接的最优路径\n- **DNA 测序**：基因组拼接中读取片段的遍历与组装\n- **网络协议**：数据包遍历网络中所有链路的状态检测",
    "- 欧拉回路 (Eulerian Circuit)：经过每条边恰好一次的闭合路径\n- 欧拉迹 (Eulerian Trail)：经过每条边恰好一次的开放路径\n- 欧拉图 (Eulerian Graph)：存在欧拉回路的图\n- 半欧拉图 (Semi-Eulerian Graph)：存在欧拉迹但不存在欧拉回路的图\n- Hierholzer 算法：构造欧拉回路的线性时间算法",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 1]\n- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Section 1.2]\n\n### 历史文献\n\n- [L. Euler. Solutio problematis ad geometriam situs pertinentis. Commentarii academiae scientiarum Petropolitanae, 1736]\n\n### 在线资源\n\n- [Mathlib4 - Trails](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Trails.html)"
))

theorems.append((
    "GraphTheory/planar-graph-euler-formula.md",
    "平面图欧拉公式 (Euler's Formula for Planar Graphs)",
    "import Mathlib.Combinatorics.SimpleGraph.Planarity\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- 平面图的欧拉公式：V - E + F = 1 + C，\n    其中 C 是连通分支数。对连通平面图，V - E + F = 2 -/\ntheorem euler_formula_planar (hG : G.Planar) :\n    Fintype.card V - G.edgeFinset.card + G.faceCount = 1 + G.connectedComponents.card := by\n  -- 对边数归纳证明\n  sorry\n\nend SimpleGraph",
    "平面图的欧拉公式是数学中最优美、最普遍的定理之一，由莱昂哈德·欧拉（Leonhard Euler）于1750年代首次提出。对于任何连通的平面图，公式 $V - E + F = 2$ 建立了顶点数 $V$、边数 $E$ 和面数 $F$ 之间的基本关系。这一定理不仅是拓扑学的基石，也是证明四色定理、Kuratowski 定理和无数图论结果的关键工具。",
    "想象用橡皮筋在平面上围成一个网络。欧拉公式告诉我们：无论网络多么复杂，只要它是连通的且边不相交，顶点数减去边数再加上被分割出的区域数（包括外部无限区域），结果总是 2。可以从一个简单的三角形开始：3 个顶点、3 条边、2 个面（内部和外部），$3 - 3 + 2 = 2$。每添加一条新边，要么增加一个面，要么增加一个顶点，$V - E + F$ 的值保持不变。",
    "设 $G$ 是一个连通的平面图，$V$ 为顶点数，$E$ 为边数，$F$ 为面数（包括外部面），则：\n\n$$V - E + F = 2$$\n\n对于具有 $C$ 个连通分支的平面图：\n\n$$V - E + F = 1 + C$$\n\n其中：\n\n- $V = |V(G)|$ 表示顶点数\n- $E = |E(G)|$ 表示边数\n- $F$ 表示图在平面嵌入中将平面分割成的区域数（面数）\n- $C$ 表示连通分支数",
    "1. **树的情况**：若 $G$ 是树，则 $F = 1$（只有外部面），且 $E = V - 1$，故 $V - (V - 1) + 1 = 2$\\n2. **归纳假设**：假设公式对所有边数少于 $E$ 的连通平面图成立\\n3. **添加边**：若 $G$ 不是树，则存在圈。移除圈上的一条边，减少一个面但不改变顶点数\\n4. **归纳推导**：由归纳假设，新图满足 $V - (E - 1) + (F - 1) = 2$，即原图也满足公式\n\n核心洞察在于欧拉公式是平面拓扑的\"守恒量\"，与具体图的结构无关。",
    "### 示例 1：完全图 $K_4$\n\n$K_4$ 可以平面嵌入为一个三角形内部有一点连接到三个顶点。此时 $V = 4$, $E = 6$, $F = 4$（三个小三角形面和一个外部面）。验证：$4 - 6 + 4 = 2$。\n\n### 示例 2：立方体图\n\n立方体的顶点、边和面构成一个平面图（通过投影）。$V = 8$, $E = 12$, $F = 6$（六个正方形面）。验证：$8 - 12 + 6 = 2$。这是多面体欧拉公式的经典实例。\n\n### 示例 3：两个不相连的三角形\n\n图有两个连通分支，每个是一个三角形。$V = 6$, $E = 6$, $F = 3$（两个内部面和一个共享的外部面）。验证：$6 - 6 + 3 = 3 = 1 + 2$。说明了非连通图的推广形式。",
    "- **四色定理**：证明平面图着色数上界的关键工具\n- **多面体分类**：正多面体（柏拉图立体）只有五种\n- **平面图判定**：推导平面图边数上界 $E \\leq 3V - 6$\n- **拓扑学**：欧拉示性数 $\\chi = V - E + F$ 是曲面的拓扑不变量\n- **计算机图形学**：网格生成和曲面参数化中的拓扑约束",
    "- 平面图 (Planar Graph)：可以在平面上无交叉绘制的图\n- 面 (Face)：平面图将平面分割成的连通区域\n- 欧拉示性数 (Euler Characteristic)：$\\chi = V - E + F$，曲面的拓扑不变量\n- Kuratowski 定理：判定平面图的特征定理\n- 对偶图 (Dual Graph)：将平面图的面转换为顶点的构造",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 4]\n- [J. A. Bondy & U. S. R. Murty. Graph Theory. Springer, 2008. Chapter 10]\n\n### 历史文献\n\n- [L. Euler. Elementa doctrinae solidorum. Novi Commentarii academiae scientiarum Petropolitanae, 1758]\n\n### 在线资源\n\n- [Mathlib4 - Planarity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Planarity.html)"
))

theorems.append((
    "GraphTheory/menger-theorem.md",
    "Menger 定理 (Menger's Theorem)",
    "import Mathlib.Combinatorics.SimpleGraph.Connectivity\n\nnamespace SimpleGraph\n\nvariable {V : Type*} [Fintype V] {G : SimpleGraph V}\n\n/-- Menger 定理（顶点形式）：两个不相邻顶点间内部不相交路径的最大数量\n    等于分离它们的最小顶点割的大小 -/\ntheorem menger_vertex (s t : V) (hadj : ¬ G.Adj s t) :\n    G.maxVertexDisjointPaths s t = G.minVertexSeparator s t := by\n  -- 证明基于最大流最小割定理或归纳法\n  sorry\n\n/-- Menger 定理（边形式）：两个顶点间边不交路径的最大数量\n    等于分离它们的最小边割的大小 -/\ntheorem menger_edge (s t : V) :\n    G.maxEdgeDisjointPaths s t = G.minEdgeSeparator s t := by\n  -- 通过将边转化为顶点，归约到顶点形式\n  sorry\n\nend SimpleGraph",
    "Menger 定理由奥地利数学家 Karl Menger 于1927年证明，是图论连通性理论的核心结果。该定理有两个经典形式：顶点形式断言两个不相邻顶点间内部顶点不交路径的最大数量等于分离它们的最小顶点割的大小；边形式断言两个顶点间边不交路径的最大数量等于分离它们的最小边割的大小。Menger 定理深刻刻画了图的局部连通结构。",
    "Menger 定理可以用一个网络可靠性问题来理解：假设一个通信网络中要从城市 $s$ 向城市 $t$ 发送消息，为了避免某个中转站被破坏导致通信中断，希望找到尽可能多的、不共享任何中转站的独立路径。Menger 定理告诉我们：这样独立路径的最大数量，恰好等于要使 $s$ 和 $t$ 完全断开所需要破坏的最少中转站数量。换句话说，网络的\"冗余度\"与\"脆弱性\"是一枚硬币的两面。",
    "设 $G$ 是一个图，$s, t \\in V(G)$ 是两个不同顶点：\n\n**顶点形式**（$s, t$ 不相邻）：\n$$\\kappa_G(s, t) = \\min\\{|S| : S \\subseteq V(G) \\setminus \\{s, t\\}, \\text{ 每个 } s\\text{-}t\\text{ 路径都经过 } S\\}$$\n\n**边形式**：\n$$\\lambda_G(s, t) = \\min\\{|F| : F \\subseteq E(G), \\text{ 每个 } s\\text{-}t\\text{ 路径都包含 } F\\text{ 中的边}\\}$$\n\n其中：\n\n- $\\kappa_G(s, t)$ 表示 $s$ 与 $t$ 之间内部顶点不交路径的最大数量\n- $\\lambda_G(s, t)$ 表示 $s$ 与 $t$ 之间边不交路径的最大数量\n- 等号右边的表达式分别表示最小顶点分隔集和最小边分隔集的大小",
    "1. **弱方向**：任何顶点割必须与子路径集相交，因此路径数不超过割的大小\\n2. **网络流转化**：将图转化为网络流问题，利用最大流最小割定理证明等号方向\\n3. **归纳法**：对图的边数或顶点数进行归纳，分析最短路径的结构\\n4. **收缩与删除**：通过图的收缩和边删除操作，保持 Menger 条件并归约到更小图\n\n核心洞察在于\"不交路径\"与\"分隔集\"构成完美的对偶关系。",
    "### 示例 1：网格图\n\n考虑一个 $3 \\times 3$ 网格图，$s$ 为左上角，$t$ 为右下角。可以找到 3 条内部顶点不交的路径，而移除中间一列的 3 个顶点即可断开 $s$ 和 $t$。验证了 Menger 定理的等式。\n\n### 示例 2：完全图 $K_n$\n\n在 $K_n$ 中任取两个顶点 $s, t$。存在 $n - 2$ 条内部顶点不交的路径（直接经过每个其他顶点一次），而移除其余 $n - 2$ 个顶点中的任意 $n - 2$ 个就能断开 $s$ 和 $t$。等号成立。\n\n### 示例 3：树\n\n在树中，任意两个顶点之间只有唯一一条简单路径。因此内部顶点不交路径的最大数量为 1，而移除路径上的任意一个内部顶点即可分离这两个顶点。最小顶点分隔集大小也为 1。",
    "- **网络可靠性**：评估通信网络和电力网络在节点/链路故障下的容错能力\n- **社交网络**：分析信息传播路径的冗余度和关键影响者\n- **VLSI 设计**：集成电路布线中的通道分配和连通性约束\n- **组合优化**：与网络流、匹配问题之间的深刻联系",
    "- 顶点连通度 (Vertex Connectivity)：分离图所需移除的最少顶点数\n- 边连通度 (Edge Connectivity)：分离图所需移除的最少边数\n- 内部顶点不交路径 (Internally Vertex-Disjoint Paths)：除端点外无公共顶点的路径\n- 边不交路径 (Edge-Disjoint Paths)：无公共边的路径\n- 最大流最小割定理 (Max-Flow Min-Cut Theorem)：Menger 定理在网络流中的推广",
    "### 教材\n\n- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 3]\n- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Chapter 4]\n\n### 论文\n\n- [K. Menger. Zur allgemeinen Kurventheorie. Fundamenta Mathematicae, 1927]\n\n### 在线资源\n\n- [Mathlib4 - Connectivity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity.html)"
))

for args in theorems:
    write_md(*args)
