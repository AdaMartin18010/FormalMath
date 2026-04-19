---
title: "极值组合学 (Extremal Combinatorics)"
msc_primary: 05

  - 05C35
msc_secondary: ['05D05', '05D10', '05D40', '05C65']
processed_at: '2026-04-05'
---

# 极值组合学 (Extremal Combinatorics)

**最后更新**: 2026年4月5日
**MSC分类**: 05C35 (极值图论), 05D05 (极值集合论), 05D10 (Ramsey理论)

---

## 1. 引言

极值组合学研究满足特定性质的离散结构的最大或最小规模。从Turán定理到Szemerédi正则性引理，从Erdős–Ko–Rado定理到Ramsey理论，极值组合学提供了研究离散结构"极限行为"的强大工具，在理论计算机科学、信息论和数论中有深刻应用。

---

## 2. 极值图论

### 2.1 Turán型问题

**问题**: $n$ 顶点图中不含 $H$ 作为子图，最多有多少条边？

**定义 2.1** (Turán数): $\text{ex}(n, H)$ 是 $n$ 顶点 $H$-自由图的最大边数。

**定理 2.1** (Turán定理, 1941): 对完全图 $K_{r+1}$：
$$\text{ex}(n, K_{r+1}) = t_r(n)$$
其中 $t_r(n)$ 是Turán图 $T_r(n)$（完全 $r$-部图，各部分尽可能相等）的边数。

**显式公式**:
$$t_r(n) = \left(1 - \frac{1}{r}\right)\frac{n^2}{2} + O(n)$$

---

### 2.2 Erdős–Stone定理

**定理 2.2** (Erdős–Stone, 1946): 对任意图 $H$ 和整数 $r \geq 2$：
$$\text{ex}(n, H) = \left(1 - \frac{1}{\chi(H) - 1} + o(1)\right)\frac{n^2}{2}$$
其中 $\chi(H)$ 是 $H$ 的色数。

**推论 2.1**: 对非二部图 $H$，$\text{ex}(n, H) = \Theta(n^2)$；对二部图，$\text{ex}(n, H) = o(n^2)$。

---

### 2.3 二部图Turán问题

**定理 2.3** (Kővári–Sós–Turán): 对完全二部图 $K_{s,t}$：
$$\text{ex}(n, K_{s,t}) = O(n^{2-1/s})$$

**开放问题**: 对 $K_{4,4}$，确定 $\text{ex}(n, K_{4,4})$ 的精确渐近行为。

---

## 3. 极值集合论

### 3.1 Sperner定理

**定义 3.1** (反链): 子集族 $\mathcal{F}$ 是反链，若 $A \not\subseteq B$ 对所有 $A, B \in \mathcal{F}$，$A \neq B$。

**定理 3.1** (Sperner, 1928): $[n]$ 的反链最大大小为：
$$\binom{n}{\lfloor n/2 \rfloor}$$
最大反链由所有大小为 $\lfloor n/2 \rfloor$（或 $\lceil n/2 \rceil$）的子集组成。

**证明**: Lubell–Yamamoto–Meshalkin (LYM) 不等式。

---

### 3.2 Erdős–Ko–Rado定理

**定义 3.2** (相交族): 子集族 $\mathcal{F}$ 是相交的，若 $A \cap B \neq \emptyset$ 对所有 $A, B \in \mathcal{F}$。

**定理 3.2** (Erdős–Ko–Rado, 1961): 设 $n \geq 2k$，$[n]$ 的 $k$-子集相交族最大大小为：
$$\binom{n-1}{k-1}$$
最大族是星形（所有含固定元素的 $k$-子集）。

---

### 3.3 Kruskal–Katona定理

**定理 3.3** (Kruskal–Katona): 对 $k$-一致子集族 $\mathcal{F}$，其阴影（$(k-1)$-子集集）的最小大小由初始段达到。

---

## 4. Ramsey理论

### 4.1 图Ramsey数

**定义 4.1** (Ramsey数): $R(s, t)$ 是最小 $n$ 使得任意 $n$ 顶点图或其补图含 $K_s$ 或 $K_t$。

**定理 4.1** (Ramsey定理): $R(s, t)$ 对所有 $s, t$ 有限。

**基本界限**:

- $R(s, t) \leq R(s-1, t) + R(s, t-1)$
- $R(s, s) \leq 4^{s}$

**定理 4.2** (Erdős下界):
$$R(s, s) \geq (1 + o(1))\frac{s}{e\sqrt{2}}2^{s/2}$$

**已知值**: $R(3, 3) = 6$，$R(4, 4) = 18$，$R(5, 5)$ 未知（在43到48之间）。

---

### 4.2 超图Ramsey理论

**定义 4.2** (超图Ramsey数): $R^{(r)}(s, t)$ 是使得任意 $r$-一致超图边染色含单色 $K_s^{(r)}$ 或 $K_t^{(r)}$ 的最小顶点数。

**定理 4.3**:
$$R^{(3)}(s, s) > 2^{cs^2}$$

---

## 5. Szemerédi正则性引理

### 5.1 正则对

**定义 5.1** ($\varepsilon$-正则对): 顶点二部 $(X, Y)$ 是 $\varepsilon$-正则的，若对所有 $A \subseteq X$，$B \subseteq Y$，$|A| \geq \varepsilon|X|$，$|B| \geq \varepsilon|Y|$：
$$|d(A, B) - d(X, Y)| < \varepsilon$$
其中 $d(X, Y) = \frac{e(X, Y)}{|X||Y|}$ 是密度。

---

### 5.2 正则性引理

**定理 5.1** (Szemerédi正则性引理): 对任意 $\varepsilon > 0$ 和整数 $m$，存在 $M = M(\varepsilon, m)$ 使得任意图有顶点划分 $V = V_0 \cup V_1 \cup \cdots \cup V_k$（$m \leq k \leq M$）满足：

1. $|V_0| \leq \varepsilon|V|$，$|V_1| = \cdots = |V_k|$
2. 至多 $\varepsilon k^2$ 对 $(V_i, V_j)$ 不是 $\varepsilon$-正则的

**应用**: 证明图的移除引理、算术级数存在性。

---

## 6. 概率方法

### 6.1 基本方法

**定理 6.1** (概率方法): 若随机结构以正概率满足某性质，则存在满足该性质的结构。

**定理 6.2** (一阶矩方法): 若 $E[X] < 1$，则 $P(X = 0) > 0$。

**定理 6.3** (二阶矩方法): 若 $E[X] > 0$ 且 $\text{Var}(X) = o(E[X]^2)$，则 $P(X > 0) \to 1$。

---

### 6.2 Lovász局部引理

**定理 6.4** (Lovász局部引理): 设 $A_1, \ldots, A_n$ 是概率空间中的事件，每个 $A_i$ 与至多 $d$ 个其他事件不独立，$P(A_i) \leq p$，若 $ep(d+1) \leq 1$，则：
$$P\left(\bigcap_{i=1}^n \overline{A_i}\right) > 0$$

---

## 7. 目录结构

```
docs/09-组合数学与离散数学/01-组合数学/31.05-极值组合学/
├── 00-README.md                    # 本文件
├── 01-Turán定理.md                  # 极值图论基础
├── 02-极值集合论.md                 # Sperner、EKR定理
├── 03-Ramsey理论.md                 # Ramsey数
├── 04-正则性引理.md                 # Szemerédi引理
└── 05-概率方法.md                   # 随机构造
```

---

## 8. 学习路径

### 8.1 基础路径

**极值图论** → **极值集合论** → **Ramsey理论** → **概率方法**

### 8.2 进阶方向

- **加性组合**: Szemerédi定理、Green-Tao定理
- **随机图**: Erdős–Rényi模型、相变现象
- **算法应用**: 性质测试、图同构

---

**最后更新**: 2026年4月5日
**维护者**: FormalMath项目组
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
