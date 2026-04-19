---
msc_primary: 46A22
msc_secondary:
  - 46A20
  - 46B10
processed_at: '2026-04-20'
title: Hahn-Banach定理
---

# Hahn-Banach定理

## 1. 引言

Hahn-Banach定理是泛函分析中最基本、最具普遍性的定理之一。它断言：定义在赋范线性空间子空间上的有界线性泛函可以保范延拓到整个空间。这一看似简单的结论蕴含着深远的后果——它保证了对偶空间 $X^*$ 足够丰富，以至于能区分 $X$ 中的不同点；它为凸集的分离提供了理论基础；它也是凸分析、优化理论以及对偶理论的基石。本文将系统阐述Hahn-Banach定理的各种形式：延拓形式、几何形式以及分离定理，并展示它们在数学各分支中的威力。

## 2. Hahn-Banach延拓定理

### 2.1 实情形

**定理 2.1**（Hahn-Banach，实情形）。设 $X$ 为实线性空间，$p: X \to \mathbb{R}$ 满足
1. **正齐次性**：$p(\alpha x) = \alpha p(x)$，$\alpha \geq 0$；
2. **次可加性**：$p(x + y) \leq p(x) + p(y)$。

设 $M \subseteq X$ 为线性子空间，$f: M \to \mathbb{R}$ 为线性泛函且 $f(x) \leq p(x)$ 对 $x \in M$ 成立。则存在线性泛函 $F: X \to \mathbb{R}$ 使得 $F|_M = f$ 且 $F(x) \leq p(x)$ 对所有 $x \in X$ 成立。

*证明*。这是Zorn引理的经典应用。考虑全体延拓 $(N, g)$ 的集合，其中 $M \subseteq N$ 为子空间，$g: N \to \mathbb{R}$ 线性，$g|_M = f$，$g \leq p$。按 $(N_1, g_1) \leq (N_2, g_2)$（当 $N_1 \subseteq N_2$ 且 $g_2|_{N_1} = g_1$）构成偏序。任何全序子集有上界（取并），故存在极大元 $(N_{\max}, F)$。

关键步骤：证明 $N_{\max} = X$。若不然，取 $x_0 \notin N_{\max}$。对 $y_1, y_2 \in N_{\max}$，
$$F(y_1) + F(y_2) = F(y_1 + y_2) \leq p(y_1 + y_2) \leq p(y_1 - x_0) + p(y_2 + x_0),$$
故
$$F(y_1) - p(y_1 - x_0) \leq p(y_2 + x_0) - F(y_2).$$
令 $\alpha = \sup_{y \in N_{\max}} [F(y) - p(y - x_0)]$，$\beta = \inf_{y \in N_{\max}} [p(y + x_0) - F(y)]$，则 $\alpha \leq \beta$。取 $\gamma \in [\alpha, \beta]$，在 $N_{\max} \oplus \mathbb{R} x_0$ 上定义
$$F'(y + tx_0) = F(y) + t\gamma.$$
验证 $F' \leq p$：对 $t > 0$，$F'(y + tx_0) = t[F(y/t) + \gamma] \leq t[F(y/t) + p(y/t + x_0) - F(y/t)] = p(y + tx_0)$。对 $t < 0$ 类似。这与极大性矛盾。$\square$

### 2.2 赋范空间情形

**推论 2.2**。设 $X$ 为赋范线性空间，$M \subseteq X$ 子空间，$f \in M^*$。则存在 $F \in X^*$ 使得 $F|_M = f$ 且 $\|F\| = \|f\|$。

*证明*。在实情形取 $p(x) = \|f\| \|x\|$。在复情形，先延拓实部 $\operatorname{Re} f$，再复线性延拓。$\square$

**推论 2.3**（范数可达性）。对任意 $x_0 \in X$，$x_0 \neq 0$，存在 $F \in X^*$ 使得 $\|F\| = 1$ 且 $F(x_0) = \|x_0\|$。

*证明*。在 $M = \operatorname{span}\{x_0\}$ 上定义 $f(\alpha x_0) = \alpha \|x_0\|$，$\|f\| = 1$，再延拓。$\square$

**推论 2.4**（点的分离）。$X^*$ 分离 $X$ 的点：若 $x_1 \neq x_2$，则存在 $F \in X^*$ 使 $F(x_1) \neq F(x_2)$。

*证明*。对 $x_0 = x_1 - x_2 \neq 0$ 应用推论2.3。$\square$

## 3. Hahn-Banach的几何形式

### 3.1 Minkowski泛函

**定义 3.1**。设 $C \subseteq X$ 为凸集，$0 \in C$ 的内点。$C$ 的**Minkowski泛函**（规范函数）定义为
$$p_C(x) = \inf\{ t > 0 : x/t \in C \}.$$

**命题 3.2**。$p_C$ 满足正齐次性和次可加性。若 $C$ 对称（$C = -C$），则 $p_C$ 为半范数。

### 3.2 分离定理

**定理 3.3**（超平面分离）。设 $X$ 为实赋范空间，$A, B \subseteq X$ 为非空凸集：

1. **弱分离**：若 $A$ 开且 $A \cap B = \emptyset$，则存在非零 $f \in X^*$ 和 $\alpha \in \mathbb{R}$ 使
   $$f(a) \leq \alpha \leq f(b), \quad \forall a \in A, b \in B.$$

2. **严格分离**：若 $A$ 紧、$B$ 闭且凸，$A \cap B = \emptyset$，则存在 $f \in X^*$ 和 $\alpha \in \mathbb{R}$ 使
   $$\sup_{a \in A} f(a) < \alpha < \inf_{b \in B} f(b).$$

*证明*。(1) 取 $x_0 \in B - A$（凸集，开，不含0）。由Minkowski泛函和Hahn-Banach，存在 $f$ 使 $f(x_0) = p(x_0) \geq 1$ 且 $f \leq p$。对 $a \in A$，$b \in B$，$f(b) - f(a) = f(b - a) \geq 1$（因 $b - a - x_0$ 的调整）。适当缩放得分离。

(2) 由 $A$ 紧、$B$ 闭，$\operatorname{dist}(A, B) > 0$。取 $\varepsilon$-邻域 $A_\varepsilon$ 为开凸集，应用(1)再取极限。$\square$

## 4. 对偶理论中的应用

### 4.1 对偶范数

由Hahn-Banach定理，对 $x \in X$：
$$\|x\| = \sup\{ |f(x)| : f \in X^*, \|f\| \leq 1 \} = \sup\{ |f(x)| : f \in X^*, \|f\| = 1 \}.$$
这说明范数可通过其对偶空间的对偶范数恢复。

### 4.2 自反空间的刻画

**定理 4.1**（Goldstine）。设 $X$ 为Banach空间，$J: X \to X^{**}$ 为自然嵌入。则 $J(B_X)$ 在 $X^{**}$ 的单位球 $B_{X^{**}}$ 中弱*稠密。

*证明*。若不然，由分离定理存在 $\Phi \in X^{***}$ 分离 $J(B_X)$ 的闭包与某 $x^{**} \in B_{X^{**}}$。但 $X^*$ 上的泛函可由 $X^{**}$ 中元表示，导出矛盾。$\square$

**推论 4.2**（James定理）。Banach空间 $X$ 自反当且仅当对每个 $f \in X^*$，存在 $x \in X$，$\|x\| = 1$ 使 $f(x) = \|f\|$。

## 5. 向量值 Hahn-Banach

**定理 5.1**（Bohnenblust-Sobczyk）。设 $X$ 为复Banach空间，$Y$ 复赋范空间，$M \subseteq X$ 子空间。若 $T: M \to Y$ 为有界线性算子且 $Y$ 为有限维，则 $T$ 可保范延拓到 $X$。

*注记*。对无穷维值域，保范延拓一般不成立。但对Hilbert空间值域，由正交投影可延拓（且范数可能增大）。

## 6. 次线性泛函的推广

**定理 6.1**。设 $X$ 实线性空间，$p: X \to \mathbb{R}$ 为**次线性泛函**（sublinear functional）：满足正齐次性和次可加性。设 $G$ 为 $X$ 上交换半群（如 $\mathbb{R}_+$ 或凸锥），作用在 $X$ 上。若 $p(g \cdot x) = p(x)$ 对 $g \in G$，且 $f: M \to \mathbb{R}$ 为 $G$-不变线性泛函，$f \leq p$。则存在 $G$-不变延拓 $F: X \to \mathbb{R}$，$F \leq p$。

这一定理在不变测度存在性证明中有应用。

## 7. 与项目其他部分的关联

Hahn-Banach定理是泛函分析中少数几个不依赖完备性的基本定理之一，但其最深刻的结果（如分离定理的严格形式）需要空间的完备性或至少一个集合的紧性。它与开映射定理（见[08-开映射与闭图像定理](08-开映射与闭图像定理.md)）和对偶理论共同构成了泛函分析的理论核心。在凸分析和优化中，Hahn-Banach分离定理是KKT条件、Farkas引理等结果的抽象来源。在分布论（见[09-分布论入门](09-分布论入门.md)）中，分布的延拓本质上也依赖于类似的延拓原理。

## 8. 参考文献

1. H. Hahn, "Über lineare Gleichungssysteme in linearen Räumen", *J. Reine Angew. Math.* 157 (1927), 214–229.
2. S. Banach, "Sur les fonctionnelles linéaires", *Studia Math.* 1 (1929), 211–216.
3. M.M. Day, *Normed Linear Spaces*, 3rd ed., Springer, 1973.
4. W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991.
5. 定光桂，《巴拿赫空间引论》，科学出版社，1984。
