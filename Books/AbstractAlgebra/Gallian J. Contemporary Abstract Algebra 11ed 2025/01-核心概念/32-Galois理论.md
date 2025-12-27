# Galois理论 (Galois Theory)

**创建日期**: 2025年12月11日
**来源**: Gallian J. Contemporary Abstract Algebra 11ed 2025, Chapter 30
**主题编号**: AA.GALLIAN.30.01

---

## 📑 目录

- [Galois理论 (Galois Theory)](#galois理论-galois-theory)
  - [📑 目录](#-目录)
  - [一、引言](#一引言)
  - [二、基本定义](#二基本定义)
    - [2.1 自同构 (Automorphism)](#21-自同构-automorphism)
    - [2.2 Galois群 (Galois Group)](#22-galois群-galois-group)
    - [2.3 固定域 (Fixed Field)](#23-固定域-fixed-field)
  - [三、基本例子](#三基本例子)
    - [3.1 例子1：$Q(\sqrt{2})$ 在 $Q$ 上](#31-例子1qsqrt2-在-q-上)
    - [3.2 例子2：$Q(\sqrt[3]{2})$ 在 $Q$ 上](#32-例子2qsqrt32-在-q-上)
    - [3.3 例子3：$Q(\sqrt[4]{2}, i)$ 在 $Q(i)$ 上](#33-例子3qsqrt42-i-在-qi-上)
    - [3.4 例子4：$Q(\sqrt{3}, \sqrt{5})$ 在 $Q$ 上](#34-例子4qsqrt3-sqrt5-在-q-上)
    - [3.5 例子5：$Q(\omega, \sqrt[3]{2})$ 在 $Q$ 上](#35-例子5qomega-sqrt32-在-q-上)
  - [四、Galois基本定理 (定理 30.1)](#四galois基本定理-定理-301)
    - [4.1 定理内容](#41-定理内容)
    - [4.2 定理的四个部分](#42-定理的四个部分)
    - [4.3 应用例子](#43-应用例子)
  - [五、多项式根式可解性](#五多项式根式可解性)
    - [5.1 根式可解的定义](#51-根式可解的定义)
    - [5.2 可解群 (Solvable Group)](#52-可解群-solvable-group)
    - [5.3 根式可解性与可解群的关系 (定理 30.2)](#53-根式可解性与可解群的关系-定理-302)
  - [六、应用](#六应用)
    - [6.1 确定子域](#61-确定子域)
    - [6.2 五次方程不可根式解](#62-五次方程不可根式解)
    - [6.3 有限域的Galois群](#63-有限域的galois群)
  - [七、数学意义与应用](#七数学意义与应用)
  - [八、学习要点与难点](#八学习要点与难点)

---

## 一、引言

Galois理论是抽象代数中最优雅和重要的理论之一。它建立了域扩张与群之间的深刻对应关系，将域论问题转化为群论问题，从而使得许多原本困难的问题变得可解。

**Galois理论的核心思想**：对于域扩张 $E/F$，如果 $E$ 是某个多项式在 $F$ 上的分裂域，则存在一个一一对应关系：
- 中间域 $K$（$F \subseteq K \subseteq E$） ↔ Galois群的子群
- 包含关系反向对应：$K_1 \subseteq K_2$ ↔ $\operatorname{Gal}(E/K_1) \supseteq \operatorname{Gal}(E/K_2)$

这个对应关系使得我们可以通过研究群的结构来理解域的结构。

---

## 二、基本定义

### 2.1 自同构 (Automorphism)

**定义**: 设 $E$ 是域 $F$ 的扩张域。$E$ 的**自同构**是从 $E$ 到 $E$ 的环同构。

- *Gallian原文*: "Definition Automorphism" (Chapter 30)

自同构是保持域结构的双射：它保持加法和乘法运算，并且是双射。

### 2.2 Galois群 (Galois Group)

**定义**: 设 $E$ 是域 $F$ 的扩张域。$E$ 在 $F$ 上的**Galois群**，记为 $\operatorname{Gal}(E/F)$，是所有将 $F$ 的每个元素映射到自身的 $E$ 的自同构的集合。

- *Gallian原文*: "Definition Galois Group" (Chapter 30)

**性质**:
- $\operatorname{Gal}(E/F)$ 在复合运算下构成群
- $\operatorname{Gal}(E/F)$ 是 $E$ 的所有自同构群的子群

**注意**: $\operatorname{Gal}(E/F)$ 与商环或商群无关，它只是自同构的集合。

### 2.3 固定域 (Fixed Field)

**定义**: 设 $H$ 是 $\operatorname{Gal}(E/F)$ 的子群。$H$ 的**固定域**，记为 $E_H$，是 $E$ 中所有在 $H$ 的每个元素作用下保持不变的元素的集合：
$$
E_H = \{x \in E \mid \phi(x) = x \text{ 对所有 } \phi \in H\}
$$

- *Gallian原文*: "Definition Fixed Field of $H$" (Chapter 30)

**性质**: $E_H$ 是 $E$ 的子域。

---

## 三、基本例子

### 3.1 例子1：$Q(\sqrt{2})$ 在 $Q$ 上

**域**: $Q(\sqrt{2}) = \{a + b\sqrt{2} \mid a, b \in Q\}$

**分析**: 任何包含 $Q$ 的域的自同构必须将 $Q$ 的元素映射到自身（练习1）。因此，$Q(\sqrt{2})$ 的自同构 $\phi$ 完全由 $\phi(\sqrt{2})$ 决定。

由于
$$
2 = \phi(2) = \phi(\sqrt{2} \cdot \sqrt{2}) = (\phi(\sqrt{2}))^2,
$$
我们有 $\phi(\sqrt{2}) = \pm \sqrt{2}$。

**Galois群**: $\operatorname{Gal}(Q(\sqrt{2})/Q)$ 有两个元素：
- 恒等映射：$a + b\sqrt{2} \mapsto a + b\sqrt{2}$
- 共轭映射：$a + b\sqrt{2} \mapsto a - b\sqrt{2}$

因此，$\operatorname{Gal}(Q(\sqrt{2})/Q) \cong Z_2$。

- *Gallian原文*: "EXAMPLE 1" (Chapter 30)

### 3.2 例子2：$Q(\sqrt[3]{2})$ 在 $Q$ 上

**分析**: 类似地，$Q(\sqrt[3]{2})$ 的自同构 $\phi$ 完全由 $\phi(\sqrt[3]{2})$ 决定。$\phi(\sqrt[3]{2})$ 必须是2的立方根。

由于 $Q(\sqrt[3]{2})$ 是实数的子集，而 $\sqrt[3]{2}$ 是唯一的实立方根，我们必须有 $\phi(\sqrt[3]{2}) = \sqrt[3]{2}$。

**Galois群**: $\operatorname{Gal}(Q(\sqrt[3]{2})/Q)$ 只有一个元素（恒等映射）。

**固定域**: $\operatorname{Gal}(Q(\sqrt[3]{2})/Q)$ 的固定域是 $Q(\sqrt[3]{2})$ 本身。

- *Gallian原文*: "EXAMPLE 2" (Chapter 30)

### 3.3 例子3：$Q(\sqrt[4]{2}, i)$ 在 $Q(i)$ 上

**分析**: 任何固定 $Q(i)$ 的 $Q(\sqrt[4]{2}, i)$ 的自同构 $\phi$ 完全由 $\phi(\sqrt[4]{2})$ 决定。由于
$$
2 = \phi(2) = \phi((\sqrt[4]{2})^4) = (\phi(\sqrt[4]{2}))^4,
$$
$\phi(\sqrt[4]{2})$ 必须是2的四次根。

**Galois群**: 定义自同构 $\alpha$ 使得 $\alpha(i) = i$ 且 $\alpha(\sqrt[4]{2}) = i\sqrt[4]{2}$，则 $\alpha \in \operatorname{Gal}(Q(\sqrt[4]{2}, i)/Q(i))$ 且 $\alpha$ 的阶为4。

因此，$\operatorname{Gal}(Q(\sqrt[4]{2}, i)/Q(i))$ 是4阶循环群。

**固定域**: $\{\varepsilon, \alpha^2\}$（其中 $\varepsilon$ 是恒等自同构）的固定域是 $Q(\sqrt{2}, i)$。

- *Gallian原文*: "EXAMPLE 3" (Chapter 30)

### 3.4 例子4：$Q(\sqrt{3}, \sqrt{5})$ 在 $Q$ 上

**域**: $Q(\sqrt{3}, \sqrt{5}) = \{a + b\sqrt{3} + c\sqrt{5} + d\sqrt{3}\sqrt{5} \mid a, b, c, d \in Q\}$

**分析**: 任何 $Q(\sqrt{3}, \sqrt{5})$ 的自同构 $\phi$ 完全由两个值 $\phi(\sqrt{3})$ 和 $\phi(\sqrt{5})$ 决定。

**Galois群**: 有四个自同构：

| 自同构 | $\sqrt{3}$ | $\sqrt{5}$ |
|--------|-----------|-----------|
| $\varepsilon$ | $\sqrt{3}$ | $\sqrt{5}$ |
| $\alpha$ | $-\sqrt{3}$ | $\sqrt{5}$ |
| $\beta$ | $\sqrt{3}$ | $-\sqrt{5}$ |
| $\alpha\beta$ | $-\sqrt{3}$ | $-\sqrt{5}$ |

显然，$\operatorname{Gal}(Q(\sqrt{3}, \sqrt{5})/Q) \cong Z_2 \oplus Z_2$。

**固定域**:
- $\{\varepsilon, \alpha\}$ 的固定域是 $Q(\sqrt{5})$
- $\{\varepsilon, \beta\}$ 的固定域是 $Q(\sqrt{3})$
- $\{\varepsilon, \alpha\beta\}$ 的固定域是 $Q(\sqrt{3}\sqrt{5})$

- *Gallian原文*: "EXAMPLE 4" (Chapter 30)

### 3.5 例子5：$Q(\omega, \sqrt[3]{2})$ 在 $Q$ 上

**设置**: $\omega = -1/2 + i\sqrt{3}/2$ 满足 $\omega^3 = 1$ 和 $\omega^2 + \omega + 1 = 0$。

**分析**: $Q(\omega, \sqrt[3]{2})$ 的自同构可以通过指定它们如何作用于 $\omega$ 和 $\sqrt[3]{2}$ 来描述。

**Galois群**: 有六个自同构，且 $\alpha\beta \neq \beta\alpha$，因此 $\operatorname{Gal}(Q(\omega, \sqrt[3]{2})/Q) \cong S_3$。

- *Gallian原文*: "EXAMPLE 5" (Chapter 30)

---

## 四、Galois基本定理 (定理 30.1)

### 4.1 定理内容

**定理 30.1 (Galois基本定理)**: 设 $F$ 是特征为0的域或有限域。如果 $E$ 是某个 $F[x]$ 中多项式在 $F$ 上的分裂域，则从包含 $F$ 的 $E$ 的子域集合到 $\operatorname{Gal}(E/F)$ 的子群集合的映射 $K \mapsto \operatorname{Gal}(E/K)$ 是一一对应。

- *Gallian原文*: "Theorem 30.1 Fundamental Theorem of Galois Theory" (Chapter 30)

### 4.2 定理的四个部分

对于任何包含 $F$ 的 $E$ 的子域 $K$：

1. **度与阶的关系**:
   $$
   [E:K] = |\operatorname{Gal}(E/K)| \quad \text{且} \quad [K:F] = |\operatorname{Gal}(E/F)| / |\operatorname{Gal}(E/K)|
   $$
   $\operatorname{Gal}(E/K)$ 在 $\operatorname{Gal}(E/F)$ 中的指数等于 $K$ 在 $F$ 上的次数。

2. **正规子群对应**:
   如果 $K$ 是某个 $F[x]$ 中多项式在 $F$ 上的分裂域，则 $\operatorname{Gal}(E/K)$ 是 $\operatorname{Gal}(E/F)$ 的正规子群，且
   $$
   \operatorname{Gal}(K/F) \cong \operatorname{Gal}(E/F) / \operatorname{Gal}(E/K)
   $$

3. **固定域性质**:
   $$
   K = E_{\operatorname{Gal}(E/K)}
   $$
   $\operatorname{Gal}(E/K)$ 的固定域是 $K$。

4. **子群对应**:
   如果 $H$ 是 $\operatorname{Gal}(E/F)$ 的子群，则
   $$
   H = \operatorname{Gal}(E/E_H)
   $$
   固定 $E_H$ 的 $E$ 的自同构群是 $H$。

### 4.3 应用例子

**例子6**: 设 $\omega = \cos(2\pi/7) + i\sin(2\pi/7)$，使得 $\omega^7 = 1$。考虑域 $Q(\omega)$。

**问题**: $Q(\omega)$ 有多少个子域？它们是什么？

**解答**:
- $Q(\omega)$ 是 $x^7 - 1$ 在 $Q$ 上的分裂域，因此可以应用Galois基本定理。
- 简单计算表明，将 $\omega$ 映射到 $\omega^3$ 的自同构 $\phi$ 的阶为6。
- 因此，$[Q(\omega):Q] = |\operatorname{Gal}(Q(\omega)/Q)| \geq 6$。
- 由于 $x^7 - 1 = (x-1)(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)$ 且 $\omega$ 是 $x^7 - 1$ 的零点，我们有 $|\operatorname{Gal}(Q(\omega)/Q)| = [Q(\omega):Q] \leq 6$。
- 因此，$\operatorname{Gal}(Q(\omega)/Q)$ 是6阶循环群。

**子群格**: $\operatorname{Gal}(Q(\omega)/Q)$ 的子群格很简单（见图30.6）。

**结论**: $Q(\omega)$ 恰好包含 $Q$ 的两个真扩张：
- 一个3次扩张，对应 $\langle \phi^3 \rangle$ 的固定域
- 一个2次扩张，对应 $\langle \phi^2 \rangle$ 的固定域

- *Gallian原文*: "EXAMPLE 6" (Chapter 30)

---

## 五、多项式根式可解性

### 5.1 根式可解的定义

**定义**: 设 $F$ 是域，$f(x) \in F[x]$。我们说 $f(x)$ 在 $F$ 上**根式可解**，如果 $f(x)$ 在 $F$ 的某个扩张 $F(a_1, a_2, \ldots, a_n)$ 中分裂，且存在正整数 $k_1, \ldots, k_n$，使得 $a_1^{k_1} \in F$ 且 $a_i^{k_i} \in F(a_1, \ldots, a_{i-1})$ 对于 $i = 2, \ldots, n$。

- *Gallian原文*: "Definition Solvable by Radicals" (Chapter 30)

**解释**: 如果我们可以通过对 $F$ 添加各种 $k$ 次根来获得 $f(x)$ 的所有零点，则多项式在 $F$ 上根式可解。换句话说，$f(x)$ 的每个零点可以写成涉及 $F$ 的元素和加法、减法、乘法、除法、开根运算的表达式（通常很复杂）。

**历史背景**:
- 线性方程和二次方程的解法在数千年前就已知（二次公式）。
- 16世纪，意大利数学家开发了求解任何三次或四次方程的公式。这些公式只涉及加法、减法、乘法、除法、开根运算。
- Abel和Galois都证明了不存在一般五次方程的根式解。特别是，不存在"五次公式"。

### 5.2 可解群 (Solvable Group)

**定义**: 我们说群 $G$ 是**可解的**，如果 $G$ 有一系列子群
$$
\{e\} = H_0 \subset H_1 \subset H_2 \subset \cdots \subset H_k = G,
$$
其中，对于每个 $0 \leq i < k$，$H_i$ 在 $H_{i+1}$ 中正规，且 $H_{i+1}/H_i$ 是阿贝尔群。

- *Gallian原文*: "Definition Solvable Group" (Chapter 30)

**例子**:
- 阿贝尔群是可解的。
- 二面体群是可解的。
- 任何阶为 $p^n$ 的群（其中 $p$ 是素数）是可解的（见练习28和29）。
- Feit-Thompson定理（见第24章）说每个奇数阶群都是可解的。
- 任何非阿贝尔单群都不是可解的。特别是，$A_5$ 不是可解的。从第24章练习21可以得出 $S_5$ 不是可解的。

### 5.3 根式可解性与可解群的关系 (定理 30.2)

**定理 30.2**: 设 $F$ 是特征为0的域，$a \in F$。如果 $E$ 是 $x^n - a$ 在 $F$ 上的分裂域，则Galois群 $\operatorname{Gal}(E/F)$ 是可解的。

- *Gallian原文*: "Theorem 30.2 Condition for $\operatorname{Gal}(E/F)$ to be Solvable" (Chapter 30)

**证明思路**:
1. 如果 $F$ 包含 $n$ 次本原单位根 $\omega$，则 $\operatorname{Gal}(E/F)$ 是阿贝尔群，因此是可解的。
2. 如果 $F$ 不包含 $n$ 次本原单位根，则考虑 $F(\omega)$，其中 $\omega$ 是 $n$ 次本原单位根。我们有正规列：
   $$
   \{e\} \subseteq \operatorname{Gal}(E/F(\omega)) \subseteq \operatorname{Gal}(E/F)
   $$
   其中 $\operatorname{Gal}(E/F(\omega))$ 是阿贝尔群，$\operatorname{Gal}(F(\omega)/F)$ 也是阿贝尔群。因此，$\operatorname{Gal}(E/F)$ 是可解的。

**更一般的结果**: 设 $F$ 是特征为0的域，$f(x) \in F[x]$。假设 $f(x)$ 在 $F(a_1, a_2, \ldots, a_t)$ 中分裂，其中 $a_1^{n_1} \in F$ 且 $a_i^{n_i} \in F(a_1, \ldots, a_{i-1})$ 对于 $i = 2, \ldots, t$。设 $E$ 是 $f(x)$ 在 $F$ 上的分裂域，且 $E \subseteq F(a_1, a_2, \ldots, a_t)$。则Galois群 $\operatorname{Gal}(E/F)$ 是可解的。

- *Gallian原文*: "Theorem 30.3" (Chapter 30)

**逆定理**: 如果 $f(x)$ 在 $F$ 上根式可解，则 $\operatorname{Gal}(E/F)$ 是可解的，其中 $E$ 是 $f(x)$ 在 $F$ 上的分裂域。

**应用**: 五次方程 $x^5 - 4x + 2 = 0$ 在 $Q$ 上不可根式解，因为它的Galois群是 $S_5$，而 $S_5$ 不是可解群。

---

## 六、应用

### 6.1 确定子域

Galois基本定理的主要应用之一是确定域的子域。通常，确定子群比确定子域容易得多。因此，我们可以：
1. 计算Galois群
2. 确定Galois群的所有子群
3. 使用Galois基本定理找到对应的子域

### 6.2 五次方程不可根式解

**定理**: 一般的五次方程在 $Q$ 上不可根式解。

**证明思路**:
- 存在五次多项式 $f(x) \in Q[x]$，使得 $f(x)$ 在 $Q$ 上的分裂域 $E$ 的Galois群是 $S_5$。
- $S_5$ 不是可解群（因为 $A_5$ 是单群且不是阿贝尔群）。
- 因此，根据定理30.3的逆，$f(x)$ 在 $Q$ 上不可根式解。

**例子**: $x^5 - 4x + 2 = 0$ 在 $Q$ 上不可根式解。

### 6.3 有限域的Galois群

**例子7**: 考虑扩张 $E = \mathrm{GF}(p^n)$ 在 $F = \mathrm{GF}(p)$ 上。

**分析**:
- 根据定理21.2的推论2，$E$ 具有形式 $F(b)$，其中 $b$ 是某个 $n$ 次不可约多项式 $p(x)$ 的零点。
- 任何域自同构 $\phi$ 必须将1映射到自身，因此 $\phi$ 在 $F$ 上作用为恒等映射。
- 由于 $p(b) = 0$ 意味着 $p(\phi(b)) = 0$，且 $p(x)$ 最多有 $n$ 个零点，我们知道 $\phi(b)$ 最多有 $n$ 种可能。
- 根据第13章练习49，映射 $\sigma(a) = a^p$ 对所有 $a \in E$ 是 $E$ 的自同构。
- 根据定理21.2，$E^*$ 是循环群，因此 $\langle \sigma \rangle$ 的阶为 $n$（见第21章练习9）。

**结论**: $\operatorname{Gal}(\mathrm{GF}(p^n)/\mathrm{GF}(p)) \cong Z_n$。

- *Gallian原文*: "EXAMPLE 7" (Chapter 30)

---

## 七、数学意义与应用

### 7.1 理论意义

1. **统一性**: Galois理论统一了群论和域论，建立了它们之间的深刻对应关系。
2. **简化问题**: 将域论问题转化为群论问题，使得许多原本困难的问题变得可解。
3. **结构理解**: 通过研究群的结构来理解域的结构，特别是子域的结构。

### 7.2 历史意义

1. **解决经典问题**: Galois理论解决了几个世纪以来困扰数学家的多项式方程根式可解性问题。
2. **开创性工作**: Galois的工作开创了现代抽象代数的发展。
3. **深远影响**: Galois理论的影响远远超出了代数学，影响了数论、几何、拓扑等多个数学分支。

### 7.3 现代应用

1. **代数数论**: Galois理论在代数数论中有重要应用，特别是在研究数域的扩张时。
2. **代数几何**: Galois理论在代数几何中用于研究代数簇的结构。
3. **编码理论**: Galois理论在编码理论中用于构造纠错码。
4. **密码学**: Galois理论在密码学中用于构造安全的加密方案。

---

## 八、学习要点与难点

### 8.1 学习要点

1. **理解对应关系**: Galois基本定理建立了域扩张与群之间的一一对应关系，这是Galois理论的核心。
2. **掌握基本定义**: 理解自同构、Galois群、固定域的定义和性质。
3. **熟悉例子**: 通过具体的例子（如 $Q(\sqrt{2})$、$Q(\sqrt{3}, \sqrt{5})$ 等）来理解Galois理论。
4. **应用定理**: 学会使用Galois基本定理来确定子域和研究域的结构。

### 8.2 难点

1. **抽象性**: Galois理论是高度抽象的，需要深入理解群论和域论。
2. **对应关系的反向性**: Galois对应是反向的：较大的域对应较小的群，较小的域对应较大的群。
3. **分裂域条件**: Galois基本定理要求 $E$ 是某个多项式在 $F$ 上的分裂域，这个条件很重要。
4. **可解群**: 理解可解群的定义和性质，以及它与多项式根式可解性的关系。

### 8.3 学习建议

1. **先掌握基础**: 在学习Galois理论之前，确保已经掌握了群论和域论的基础知识。
2. **多做例子**: 通过大量的例子来理解Galois理论的概念和定理。
3. **理解证明**: 虽然Galois基本定理的证明比较复杂，但理解证明思路有助于深入理解理论。
4. **应用练习**: 通过解决实际问题来应用Galois理论，如确定子域、判断多项式是否根式可解等。

---

**最后更新**: 2025年12月11日
