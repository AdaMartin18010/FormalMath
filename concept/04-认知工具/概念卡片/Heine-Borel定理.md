---
msc_primary: "54D30"
msc_secondary:
  - 26A42
  - 46B50
---

# 概念卡片：Heine-Borel定理

## 严格定义

设 $(X, d)$ 为度量空间（或更一般地，拓扑空间）。子集 $K \subseteq X$ 称为**紧致的（compact）**，若 $K$ 的每个开覆盖都有有限子覆盖：即对任意开集族 $\{U_\alpha\}_{\alpha \in A}$ 满足 $K \subseteq \bigcup_\alpha U_\alpha$，存在有限子集 $A_0 \subseteq A$ 使得 $K \subseteq \bigcup_{\alpha \in A_0} U_\alpha$。

在度量空间中，紧致性等价于**序列紧致**（每个序列都有收敛子列，且极限在集合中）和**完全有界且完备**。

**Heine-Borel 定理**：在欧氏空间 $\mathbb{R}^n$（装备标准度量）中，子集 $K \subseteq \mathbb{R}^n$ 紧致当且仅当 $K$ 是**闭的**且**有界的**。

**一般化失效**：在一般度量空间中，"闭且有界"不蕴含紧致。例如：

- 在无限维 Banach 空间中，闭单位球不是紧致的（Riesz 引理）；
- 在离散度量空间中，整个空间有界且闭，但非紧致（若无限）。

## 历史背景

Heine-Borel 定理的历史反映了分析学从直观到严格的演进。

**Heine 的贡献（1870）**：Eduard Heine 在 1870 年证明了闭区间 $[a, b]$ 上连续函数的一致连续性。他的证明隐含地使用了覆盖论证，但并未明确提出紧致性概念。这一结果后来被称为"Heine-Cantor 定理"。

**Borel 的覆盖引理（1895）**：Émile Borel 在 1895 年明确证明了：闭区间 $[a, b]$ 的任意可数开覆盖都有有限子覆盖。他对可数覆盖的处理源于当时对实数集结构的理解局限。

**Lebesgue 的推广（1904）**：Henri Lebesgue 将 Borel 的结果从可数覆盖推广到任意覆盖，给出了现代形式的 Heine-Borel 定理。Lebesgue 的证明利用了实数的完备性和闭区间的嵌套性质。

**Hausdorff 的抽象化（1914）**：Felix Hausdorff 在《集合论基础》中引入了一般的紧致性概念，并将 Heine-Borel 定理定位为欧氏空间的特殊性质。他证明了在完备度量空间中，完全有界 + 闭 = 紧致，而欧氏空间的有界性恰好蕴含完全有界性。

## 直观理解

Heine-Borel 定理是有限维欧氏空间的一个"幸福意外"：在这里，紧致性——一个 seemingly 复杂的覆盖条件——可以被极为简单的两个性质（闭 + 有界）完全刻画。

**闭性的直观**：闭集包含其所有极限点。若 $K$ 不闭，则存在 $K$ 中的序列收敛到 $K$ 外的点 $x$。以 $x$ 为中心的开球构造的开覆盖将没有有限子覆盖——因为任何有限个开球都无法同时覆盖 $K$ 中趋近于 $x$ 的无穷序列和远离 $x$ 的部分。

**有界性的直观**：无界集可以"逃逸到无穷远"。若 $K$ 无界，则以原点为中心、半径递增的开球族 $\{B(0, n)\}_{n=1}^\infty$ 覆盖 $K$，但任何有限子族只能覆盖到某个有限半径，无法覆盖 $K$ 中超出该半径的点。

**有限维的关键**：在 $\mathbb{R}^n$ 中，有界性意味着可以被装入某个大球中，而有限维的大球可以被有限个任意小的球覆盖（完全有界）。在无限维中，单位球内有无限多个两两距离为常数的点（Riesz 引理），因此无法被有限个小球覆盖。

## 数学例子

### 闭区间的紧致性

**定理**：$[0, 1] \subseteq \mathbb{R}$ 紧致。

**证明（Lebesgue 方法）**：设 $\mathcal{U}$ 为 $[0, 1]$ 的开覆盖。令
$$S = \{x \in [0, 1] : [0, x] \text{ 可被 } \mathcal{U} \text{ 的有限子族覆盖}\}。$$

$S$ 非空（$0$ 被某个 $U \in \mathcal{U}$ 覆盖）。令 $s = \sup S$。

- 若 $s < 1$：取 $U \in \mathcal{U}$ 含 $s$。因 $U$ 开，存在 $\varepsilon > 0$ 使 $(s - \varepsilon, s + \varepsilon) \subseteq U$。由 $s = \sup S$，存在 $x \in S$ 使得 $x > s - \varepsilon$。$[0, x]$ 有有限覆盖，加上 $U$ 覆盖 $(s - \varepsilon, s + \varepsilon)$，故 $[0, s + \varepsilon/2]$ 有有限覆盖，与 $s = \sup S$ 矛盾。
- 故 $s = 1$。类似论证表明 $1 \in S$。

### 有限维推广

**定理**：$\mathbb{R}^n$ 中的闭有界集紧致。

**证明**：闭区间 $[a, b]$ 紧致（如上）。有限个紧致空间的积紧致（Tychonoff 定理，有限情形可用归纳法初等证明）。故 $[a_1, b_1] \times \cdots \times [a_n, b_n]$ 紧致。

任意闭有界集 $K \subseteq \mathbb{R}^n$ 可含于某个闭方体 $C$ 中。$K$ 作为紧致空间 $C$ 的闭子集，本身紧致。

### 无限维反例：Hilbert 空间的单位球

设 $H = \ell^2$（平方可和序列空间），$B = \{x : \|x\| \leq 1\}$ 为闭单位球。

$B$ 是闭的且有界的，但非紧致。

**证明**：取标准基向量 $e_n = (0, \ldots, 0, 1, 0, \ldots)$（第 $n$ 位为 1）。$\|e_n - e_m\| = \sqrt{2}$ 对 $n \neq m$。故 $\{e_n\}$ 无 Cauchy 子列，更无收敛子列。因此 $B$ 不序列紧致，故不紧致。

### 应用：连续函数的一致连续性

**Heine-Cantor 定理**：设 $K \subseteq \mathbb{R}^n$ 紧致，$f: K \to \mathbb{R}^m$ 连续。则 $f$ 一致连续。

**证明**：给定 $\varepsilon > 0$。由连续性，对每个 $x \in K$，存在 $\delta_x > 0$ 使得 $d(x, y) < \delta_x \Rightarrow d(f(x), f(y)) < \varepsilon/2$。

开覆盖 $\{B(x, \delta_x/2)\}_{x \in K}$ 有有限子覆盖 $B(x_1, \delta_{x_1}/2), \ldots, B(x_n, \delta_{x_n}/2)$。令 $\delta = \min_i \delta_{x_i}/2$。

若 $d(x, y) < \delta$，则 $x \in B(x_i, \delta_{x_i}/2)$ 对某个 $i$。于是
$$d(y, x_i) \leq d(y, x) + d(x, x_i) < \delta + \delta_{x_i}/2 \leq \delta_{x_i}。$$
故 $d(f(x), f(y)) \leq d(f(x), f(x_i)) + d(f(x_i), f(y)) < \varepsilon/2 + \varepsilon/2 = \varepsilon$。

## 与其他概念的联系

### 与完备化的联系

Heine-Borel 定理在度量空间中的自然推广是：子集紧致当且仅当它**完备且完全有界**。在 $\mathbb{R}^n$ 中，Bolzano-Weierstrass 定理保证了有界序列有收敛子列，这等价于完全有界性 + 完备性。

一般度量空间的完备化过程可以视为"填补缺失的极限点"，使得原本不闭的集合在完备化中变得"闭"。但完备化本身不恢复紧致性——关键在于维度的有限性。

### 与泛函分析的联系

在泛函分析中，Riesz 引理说：若 $Y$ 是赋范空间 $X$ 的真闭子空间，则存在单位向量 $x$ 使得 $d(x, Y) \geq 1 - \varepsilon$。这意味着无限维空间中单位球面上存在无限个"几乎正交"的点，从而单位球非紧。

弱拓扑下的紧致性是另一重要方向：Banach-Alaoglu 定理说，对赋范空间 $X$，其对偶空间的闭单位球在弱*拓扑下是紧致的。这是 Heine-Borel 精神在无限维中的"最弱"恢复。

### 与几何测度论的联系

在几何测度论中，等周不等式和 Sobolev 不等式的紧性论证常依赖于区域的"闭 + 有界"性质。Blaschke 选择定理说：$\mathbb{R}^n$ 中一致有界的凸集族在 Hausdorff 度量下有收敛子列——这是 Heine-Borel 定理在集合空间中的类比。

## 参考

- Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.). McGraw-Hill.
- Munkres, J. R. (2000). *Topology* (2nd ed.). Prentice-Hall.
- Conway, J. B. (1990). *A Course in Functional Analysis* (2nd ed.). Springer.
- Borel, É. (1895). Sur quelques points de la théorie des fonctions. *Annales Scientifiques de l'École Normale Supérieure*, 12, 9–55.
