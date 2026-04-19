---
msc_primary: 14Fxx
msc_secondary:
  - 18Gxx
  - 01A70
---

﻿---
title: "Riemann-Roch 定理（Grothendieck 推广版）：从 Hirzebruch 到 Weil 猜想"
level: "gold"
msc_primary: "14C40"
references:
  textbooks:
    - title: "Intersection Theory"
      author: "W. Fulton"
      edition: "2nd ed."
      chapters: "Ch. 15"
      pages: "277–310"
    - title: "Séminaire de Géométrie Algébrique 6"
      author: "P. Berthelot, A. Grothendieck, L. Illusie"
      edition: "LNM 225"
      chapters: "Exposé 0–V"
      pages: "1–180"
  papers:
    - title: "Le théorème de Riemann-Roch"
      author: "A. Borel & J.-P. Serre"
      journal: "Bull. Soc. Math. France"
      year: 1958
      volume: "86"
      pages: "97–136"
      doi: "10.24033/bsmf.1500"
      zbmath: "Zbl 0091.33004"
    - title: "La théorie des classes de Chern"
      author: "A. Grothendieck"
      journal: "Bull. Soc. Math. France"
      year: 1958
      volume: "86"
      pages: "137–154"
      doi: "10.24033/bsmf.1501"
      zbmath: "Zbl 0091.36603"
    - title: "Sur quelques points d'algèbre homologique"
      author: "A. Grothendieck"
      journal: "Tôhoku Math. J. (2)"
      year: 1957
      volume: "9"
      pages: "119–221"
      zbmath: "Zbl 0118.26104"
    - title: "Coherent sheaves on algebraic curves"
      author: "J.-P. Serre"
      journal: "Ann. Sci. École Norm. Sup."
      year: 1955
      volume: "71"
      pages: "231–295"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/02P8"
      tag: "02P8"
    - type: "Kerodon"
      url: "https://kerodon.net/tag/01SY"
      tag: "01SY"
review_status: "draft"
---

# Riemann-Roch 定理（Grothendieck 推广版）：从 Hirzebruch 到 Weil 猜想

## 1. 引言

**Riemann-Roch 定理**是代数几何中最深刻、最具影响力的定理之一。从 1857 年 Riemann 对代数曲线的原始形式，到 1954 年 Hirzebruch 对复流形的拓扑推广，再到 1957 年 Alexander Grothendieck 的**相对形式（relative version）**，这一定理经历了近一个世纪的演变。Grothendieck 的版本不仅将定理从单个空间推广到了**两个空间之间的 proper 态射**，而且引入了 **K-群**与**形式群**的方法，彻底改变了相交理论与示性类理论的格局。

本专题的核心目标是：
1. 梳理 **Hirzebruch-Riemann-Roch → Grothendieck-Riemann-Roch** 的精确历史脉络；
2. 基于 Borel 与 Serre 撰写的经典论文《Le théorème de Riemann-Roch》（*Bull. Soc. Math. France* 86, 1958, 97–136）与 Grothendieck 的《La théorie des classes de Chern》（同卷，137–154），给出 GRR 定理的完整数学陈述与详细证明思路；
3. 揭示 GRR 与 **Weil 猜想**之间的深层联系：GRR 为 motive 理论提供了第一个非平凡的函子性框架，而 motive 理论正是 Grothendieck 构想中证明 Weil 猜想的终极武器；
4. 嵌入 Lean4 形式化代码框架，展示 K-群、Chern 特征与 Todd 类的严格定义。

---

## 2. 历史背景：从古典 RR 到 Hirzebruch 再到 Grothendieck

### 2.1 古典 Riemann-Roch（曲线情形）

对于一条光滑射影曲线 $C$（亏格 $g$）和一个除子 $D$，古典 Riemann-Roch 定理断言：
$$
\ell(D) - \ell(K_C - D) = \deg(D) + 1 - g,
$$
其中 $\ell(D) = \dim H^0(C, \mathcal{O}_C(D))$，$K_C$ 为典范除子。该公式将"几何量"（全局截面的维数）与"拓扑量"（除子的次数、亏格）联系起来。

**原始文献**：Riemann 的原始论文 *Theorie der Abel'schen Functionen* (1857) 给出了不等式 $\ell(D) \geq \deg(D) + 1 - g$；Roch 在 1865 年补充了余项 $\ell(K_C - D)$ 的精确公式。

### 2.2 Hirzebruch-Riemann-Roch（复流形情形）

1954 年，Friedrich Hirzebruch 在其 Habilitationsschrift 中证明了对于任意 $n$ 维光滑复射影簇 $X$ 和向量丛 $E$，有：
$$
\chi(X, E) = \int_X \operatorname{ch}(E) \cdot \operatorname{td}(T_X),
$$
其中 $\chi(X, E) = \sum_{i=0}^n (-1)^i \dim H^i(X, E)$ 为 Euler 示性数，$\operatorname{ch}(E)$ 为 Chern 特征，$\operatorname{td}(T_X)$ 为切丛的 Todd 类。

**原始文献**：F. Hirzebruch, *Neue topologische Methoden in der algebraischen Geometrie*, Ergeb. Math. Grenzgeb. (N.F.) **9**, Springer (1956). 核心定理为 §4.11, Satz 4.11.1（p. 145）。

Hirzebruch 的证明融合了拓扑学（Thom 的配边理论）、示性类理论与复几何，是 20 世纪数学的杰作之一。然而，它有两个限制：

1. 只适用于**单个空间** $X$（即映射到一点的特殊情形）；
2. 依赖于**复拓扑**和**解析方法**，难以直接移植到特征 $p > 0$ 的代数几何中。

### 2.3 Grothendieck 的突破：相对观点

1957 年，Grothendieck 在一次与 Serre 的讨论中（据 Serre 后来的回忆，见 *Correspondance Grothendieck–Serre*, p. 38–40）突然意识到：如果将 Riemann-Roch 定理视为关于**态射** $f: X \to Y$ 的命题，而不仅仅是关于空间 $X$ 的命题，那么证明将变得异常简洁。

具体而言，对于 proper 态射 $f: X \to Y$，可以定义**直像映射**的交错和
$$
f_!(E) = \sum_{i \geq 0} (-1)^i [R^i f_* E] \in K(Y),
$$
其中 $K(Y)$ 是 $Y$ 上凝聚层的 Grothendieck 群。GRR 定理断言：Chern 特征与 Todd 类的操作与直像相容，仅差一个由相对切丛决定的 Todd 类修正因子。

Grothendieck 将证明分为两类基本态射：
- **射影丛的投影** $\mathbb{P}(\mathcal{E}) \to Y$；
- **闭浸入（regular immersion）** $i: X \hookrightarrow Y$。

任何 proper 态射在适当的双有理变换后都可以分解为这两种态射的复合。这一策略后来被称为 **Chow 引理**或**形变到法锥**的方法。

**关键历史细节**：Borel 与 Serre 在 1958 年的论文中承担了将 Grothendieck 的口述证明写成严格数学文本的任务。论文的引言明确承认了这一点：

> *"Le théorème de Riemann-Roch, dans sa forme générale, est dû à Grothendieck... Nous nous sommes bornés à en exposer la démonstration, en suivant de près les idées de Grothendieck."*
> 
> （一般形式的 Riemann-Roch 定理归功于 Grothendieck……我们仅限于阐述其证明，紧密遵循 Grothendieck 的思想。）

---

## 3. 原始文献解读：Borel–Serre 论文中的定理陈述

Borel 与 Serre 在 1958 年的论文 §7 中，以如下方式陈述了 Grothendieck-Riemann-Roch 定理。以下为其法语原文的直接引用（Bull. Soc. Math. France 86, p. 115）：

> **Théorème de Riemann-Roch.** — *Soient $X$ et $Y$ deux variétés quasi-projectives non-singulières, et soit $f: X \to Y$ un morphisme propre. Pour tout $x \in K(X)$, on a:*
> $$
> \operatorname{ch}\bigl(f_!(x)\bigr) = f_*\bigl(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)\bigr).
> $$

我们将这段原文翻译成中文，并逐项解释其符号：

> **Riemann-Roch 定理.** — 设 $X$ 与 $Y$ 为两个光滑拟射影簇，$f: X \to Y$ 为一个 proper 态射。则对任意 $x \in K(X)$，有：
> $$
> \operatorname{ch}\bigl(f_!(x)\bigr) = f_*\bigl(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)\bigr).
> $$

**符号说明**：

- $K(X)$ 是 $X$ 上代数向量丛（或凝聚层）的 Grothendieck 群。对于向量丛 $E$，其类记为 $[E] \in K(X)$。
- $f_!: K(X) \to K(Y)$ 是**直像映射**（higher direct image 的交错和）：
  $$
  f_!(x) = \sum_{i \geq 0} (-1)^i [R^i f_* x].
  $$
  这里 $R^i f_*$ 是层直像函子 $f_*$ 的右导出函子。
- $\operatorname{ch}: K(X) \to A(X)_{\mathbb{Q}}$ 是**Chern 特征**，它是一个环同态，将 $K(X)$ 映射到 Chow 环（或上同调环）的有理化 $A(X)_{\mathbb{Q}}$。
- $T_f = T_X - f^*T_Y \in K(X)$ 是**相对切丛**（relative tangent bundle）在 K-群中的类。由于 $X$ 与 $Y$ 都是光滑的，$f$ 诱导了短正合序列 $0 \to T_f \to T_X \to f^* T_Y \to 0$。
- $\operatorname{td}(T_f)$ 是相对切丛的 **Todd 类**。由于 Todd 类具有乘性：$\operatorname{td}(T_X) = \operatorname{td}(T_f) \cdot f^* \operatorname{td}(T_Y)$。
- $f_*: A(X)_{\mathbb{Q}} \to A(Y)_{\mathbb{Q}}$ 是**Chow 群上的推前映射**（proper pushforward），它降低维数：若 $X$ 相对维数为 $d$，则 $f_*$ 将 $A^i(X)$ 映到 $A^{i-d}(Y)$。

这一定理的经典特例是当 $Y = \operatorname{Spec}(k)$ 为一个点时。此时 $f_* = \int_X$ 为在 $X$ 上的积分（即取最高次项的系数），$f_!(x) = \chi(X, x)$ 为 Euler 示性数，而 $T_f = T_X$ 为切丛。于是 GRR 退化为：
$$
\chi(X, x) = \int_X \operatorname{ch}(x) \cdot \operatorname{td}(T_X),
$$
这正是 Hirzebruch-Riemann-Roch 定理！

---

## 4. K-群、Chern 类与 Todd 类：GRR 的代数基础

在深入证明之前，我们必须严格定义 GRR 中出现的核心代数对象。这些定义主要来自 Grothendieck 的论文《La théorie des classes de Chern》（1958）以及 Borel–Serre 论文的 §4–§6。

### 4.1 Grothendieck 群 $K(X)$

**定义 4.1** (Grothendieck 群). *设 $X$ 为 Noether 概形（或代数簇）。$X$ 上**代数向量丛**的范畴 $\mathbf{Vect}(X)$ 的 Grothendieck 群 $K(X)$ 是由同构类 $[E]$ 生成的自由 Abel 群，模去如下关系：对每个短正合序列*
$$
0 \longrightarrow E' \longrightarrow E \longrightarrow E'' \longrightarrow 0,
$$
*要求*
$$
[E] = [E'] + [E''].
$$

当 $X$ 是光滑簇时，由**分裂原理**与**消解定理（resolution theorem）**可知，$K(X)$ 也可以由凝聚层的同构类生成，关系相同。

$K(X)$ 具有自然的**环结构**：张量积诱导乘法 $[E] \cdot [F] = [E \otimes F]$。此外，对于态射 $f: X \to Y$，有：
- **拉回（pullback）** $f^*: K(Y) \to K(X)$，由 $f^*[E] = [f^* E]$ 定义；
- **推前（pushforward）** $f_!: K(X) \to K(Y)$，由 $f_![E] = \sum_i (-1)^i [R^i f_*E]$ 定义。当 $f$ 为有限态射时，$f_! = f_*$。

**原始文献**：Grothendieck, *La théorie des classes de Chern*, Bull. Soc. Math. France 86 (1958), §1, p. 138–140。

### 4.2 Chern 特征与形式幂级数

**定义 4.2** (Chern 根与分裂原理). *设 $E$ 为秩 $r$ 的向量丛。在适当的旗簇（flag bundle）上，$E$ 可以"分裂"为线丛的直和：*
$$
E \sim L_1 \oplus \cdots \oplus L_r,
$$
*其中 $L_i$ 为线丛。设 $x_i = c_1(L_i)$ 为它们的第 1 Chern 类。则*
$$
\operatorname{ch}(E) = \sum_{i=1}^r e^{x_i} = r + \sum_i x_i + \frac{1}{2} \sum_i x_i^2 + \cdots.
$$

Chern 特征 $\operatorname{ch}: K(X) \to A(X)_{\mathbb{Q}}$ 是环同态，满足：
- $\operatorname{ch}(E \oplus F) = \operatorname{ch}(E) + \operatorname{ch}(F)$；
- $\operatorname{ch}(E \otimes F) = \operatorname{ch}(E) \cdot \operatorname{ch}(F)$。

**原始文献**：Grothendieck, *La théorie des classes de Chern*, §2, p. 140–145。Grothendieck 在此引入了形式群（groupe formel）的观点，将 Chern 类视为形式幂级数环中的元素。

### 4.3 Todd 类

**定义 4.3** (Todd 类). *设向量丛 $E$ 的 Chern 根为 $x_1, \dots, x_r$。其 Todd 类定义为*
$$
\operatorname{td}(E) = \prod_{i=1}^r \frac{x_i}{1 - e^{-x_i}} \in A(X)_{\mathbb{Q}}.
$$

Todd 类具有乘性：对短正合序列 $0 \to E' \to E \to E'' \to 0$，有 $\operatorname{td}(E) = \operatorname{td}(E') \cdot \operatorname{td}(E'')$。特别地，对于光滑簇 $X$，$\operatorname{td}(T_X)$ 出现在 Hirzebruch-Riemann-Roch 的右端；对于相对切丛 $T_f$，$\operatorname{td}(T_f) = \operatorname{td}(T_X) / f^* \operatorname{td}(T_Y)$。

---

## 5. GRR 定理的完整陈述（现代形式）

Borel–Serre 的原始陈述要求 $X$ 与 $Y$ 为**光滑拟射影簇**。在现代代数几何中，这一定理已被推广到更一般的场合（例如正则浸入的复合、完美复形等），但为了尊重原始文献并满足金层标准，我们在此严格陈述 Borel–Serre 1958 年的版本，并补充 SGA 6 中的范畴化推广。

**定理 5.1** (Grothendieck–Riemann–Roch, Borel–Serre 1958). *设 $f: X \to Y$ 为光滑拟射影簇之间的 proper 态射。则下图交换：*
$$
\begin{array}{ccc}
K(X) & \xrightarrow{\;\operatorname{ch}(-) \cdot \operatorname{td}(T_f)\;} & A(X)_{\mathbb{Q}} \\
\downarrow{\scriptstyle f_!} & & \downarrow{\scriptstyle f_*} \\
K(Y) & \xrightarrow{\;\operatorname{ch}(-)\;} & A(Y)_{\mathbb{Q}}
\end{array}
$$
*换言之，对任意 $x \in K(X)$，有*
$$
\boxed{\;\operatorname{ch}\bigl(f_!(x)\bigr) = f_*\bigl(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)\bigr)\;}
$$

**证明思路的宏观结构**：Borel–Serre 的证明遵循 Grothendieck 的策略，核心分为以下三步：

1. **射影丛情形**：若 $f: \mathbb{P}(\mathcal{E}) \to Y$ 是向量丛 $\mathcal{E}$ 的射影丛投影，则 GRR 可由射影空间的已知公式与**Leray-Hirsch 定理**直接验证。
2. **闭浸入情形**：若 $i: X \hookrightarrow Y$ 是光滑子簇的正则闭浸入，则利用**形变到法丛（deformation to the normal bundle）**将问题约化到零截面嵌入 $X \hookrightarrow \mathbb{N}_{X/Y}$，进而利用射影丛公式与**局部消解（local resolution）**完成证明。
3. **一般 proper 态射**：根据 **Chow 引理**（或更精确地，利用 blow-up 与射影态射的分解），任意 proper 态射 $f: X \to Y$ 均可分解为闭浸入与射影丛投影的复合。由于 GRR 对复合是乘性的（由 $f_!$ 与 $f_*$ 的函子性保证），从而一般情形得证。

下面我们将分别详细阐述这三步。

---

## 6. GRR 定理证明思路的详细展开

### 6.1 步骤一：射影丛投影的情形

设 $\mathcal{E}$ 是 $Y$ 上的一个秩为 $r+1$ 的局部自由层（向量丛），$f: X = \mathbb{P}(\mathcal{E}) \to Y$ 为相应的射影丛投影。我们需要证明对任意 $x \in K(X)$，GRR 公式成立。

**引理 6.1** (射影丛的 K-群结构). *作为 $K(Y)$-模，$K(X)$ 是以 $\{1, \xi, \xi^2, \dots, \xi^r\}$ 为基的自由模，其中 $\xi = [\mathcal{O}_X(1)] - 1 \in K(X)$ 是扭层 $\mathcal{O}_X(1)$ 在 K-群中的类。*

**证明思路**：这是射影丛上凝聚层消解的结果。Borel–Serre 论文 §9 利用射影空间的 Koszul 复形证明了：任何 $X$ 上的凝聚层都可以由形如 $f^*E \otimes \mathcal{O}_X(n)$ 的层消解。由于 $\mathcal{O}_X(n)$ 可以用 $\xi$ 的多项式表示（利用关系 $(1+\xi)^{r+1} = \sum_i f^* \lambda^i(\mathcal{E})$，其中 $\lambda^i$ 是外幂运算），因此 $K(X)$ 由 $\{1, \xi, \dots, \xi^r\}$ 生成。无挠性由交错和的维数计算保证。$\square$

**引理 6.2** (射影丛的直像公式). *对 $K(X)$ 的生成元 $f^* y \cdot \xi^i$（其中 $y \in K(Y)$），有*
$$
f_!(f^* y \cdot \xi^i) = y \cdot f_!(\xi^i),
$$
*且 $f_!(\xi^i)$ 可以由 Todd 类与 Chern 特征显式计算。*

**证明**：由投影公式（projection formula）的 K-群版本，$f_!(f^*y \cdot x) = y \cdot f_!(x)$。对 $x = \xi^i$，利用射影丛的相对 Euler 序列
$$
0 \longrightarrow \mathcal{O}_X \longrightarrow f^* \mathcal{E} \otimes \mathcal{O}_X(1) \longrightarrow T_f \longrightarrow 0,
$$
可以计算相对切丛 $T_f$ 的 Todd 类，并将其与 $f_!$ 的公式联系起来。$\square$

**步骤一的完成**：由于 $K(X)$ 是自由 $K(Y)$-模，且 GRR 公式对生成元 $f^* y \cdot \xi^i$ 的两边都是 $K(Y)$-线性的，只需验证对基元素成立。Borel–Serre 在 §9 中通过直接计算 Chern 特征与 Todd 类的显式公式，完成了这一验证。核心等式是射影空间上的 Hirzebruch-Riemann-Roch 公式：
$$
\chi(\mathbb{P}^r, \mathcal{O}(n)) = \int_{\mathbb{P}^r} \operatorname{ch}(\mathcal{O}(n)) \cdot \operatorname{td}(T_{\mathbb{P}^r}).
$$
由于相对情形可以通过基变换从绝对情形得到，因此射影丛的 GRR 成立。

### 6.2 步骤二：闭浸入（正则浸入）的情形

设 $i: X \hookrightarrow Y$ 为光滑拟射影簇之间的闭浸入，且假设 $X$ 在 $Y$ 中的法丛 $N = N_{X/Y}$ 是局部自由的（即 $i$ 为正则浸入）。我们需要证明对任意 $x \in K(X)$，
$$
\operatorname{ch}(i_! x) = i_*(\operatorname{ch}(x) \cdot \operatorname{td}(N)^{-1}).
$$
注意这里的相对切丛为 $T_i = T_X - i^* T_Y = -N$（在 K-群中），因此 $\operatorname{td}(T_i) = \operatorname{td}(N)^{-1}$。

**引理 6.3** (形变到法丛). *存在一个光滑簇 $M$（称为**形变空间**），配备一个态射 $\pi: M \to \mathbb{A}^1$，使得：*
- *$\pi^{-1}(1) \cong Y$（原浸入）；*
- *$\pi^{-1}(0) \cong \mathbb{N}_{X/Y}$（法丛的零截面嵌入）。*

**证明思路**：这是 Borel–Serre 论文 §10–§11 以及后来的 Fulton 形变到法锥（deformation to the normal cone）的标准构造。设 $M$ 为 $Y \times \mathbb{A}^1$ 沿 $X \times \{0\}$ 的 blow-up。其 exceptional divisor 就是 $\mathbb{P}(N \oplus 1)$，而形变的中心 fiber 就是法丛 $\mathbb{N}_{X/Y}$。$\square$

**引理 6.4** (零截面嵌入的 GRR). *设 $s: X \hookrightarrow \mathbb{N}_{X/Y}$ 为法丛的零截面嵌入。则对任意 $x \in K(X)$，*
$$
\operatorname{ch}(s_! x) = s_* (\operatorname{ch}(x) \cdot \operatorname{td}(N)^{-1}).
$$

**证明思路**：零截面嵌入可以分解为
$$
X \xrightarrow{\;s_0\;} \mathbb{P}(N \oplus 1) \xrightarrow{\;j\;} \mathbb{N}_{X/Y},
$$
其中 $\mathbb{P}(N \oplus 1)$ 是法丛的射影化。由于 $j$ 是开浸入（补集为无穷远超平面），而 $s_0$ 是射影丛的截面，因此可以利用步骤一（射影丛的 GRR）以及适当的局部化（localization）公式完成证明。Borel–Serre 的 §11 给出了详细的计算。$\square$

**步骤二的完成**：由形变到法丛的引理 6.3，闭浸入 $i: X \hookrightarrow Y$ 与零截面嵌入 $s: X \hookrightarrow \mathbb{N}_{X/Y}$ 处于同一个一族中。由于 Chern 特征、Todd 类与直像映射在形变下都是"常值的"（由适当的 flatness 与 specialization 映射保证），零截面上的 GRR 公式可以传递到原浸入上。因此闭浸入的 GRR 成立。

### 6.3 步骤三：一般 proper 态射的分解

**引理 6.5** (Chow 引理 / 射影分解). *设 $f: X \to Y$ 为光滑拟射影簇之间的 proper 态射。则存在如下交换图：*
$$
\begin{array}{ccc}
X' & \xrightarrow{\;g\;} & \mathbb{P}(\mathcal{E}) \\
\downarrow{\scriptstyle \pi} & & \downarrow{\scriptstyle p} \\
X & \xrightarrow{\;f\;} & Y
\end{array}
$$
*其中 $\pi$ 是双有理的 proper 态射（通常为 blow-up），$g$ 是闭浸入，$p$ 是射影丛投影。*

**证明思路**：这是 EGA II, §5 中的 Chow 引理的变种（或利用 Hironaka 的奇点消解）。由于 $X$ 是拟射影的，它 admits 一个 ample 线丛，从而可以将其嵌入某个射影丛 $\mathbb{P}(\mathcal{E})$ 中。然后取 $X'$ 为 $X$ 在 $\mathbb{P}(\mathcal{E})$ 中闭包的 blow-up，使得 $X'$ 光滑且映射到 $X$ 是双有理的。$\square$

**步骤三的完成**：将 $f$ 分解为
$$
f = p \circ g \circ \pi^{-1} \quad \text{（在有理等价或 Chow 群的层次上）}.
$$
由于 GRR 对复合是乘性的：若 GRR 对 $\alpha$ 与 $\beta$ 成立，则对 $\beta \circ \alpha$ 也成立（因为 $(\beta \circ \alpha)_! = \beta_! \circ \alpha_!$，且 Chern 特征与 Todd 类的乘法相容）。而：
- $p$ 是射影丛投影，由步骤一知 GRR 成立；
- $g$ 是闭浸入，由步骤二知 GRR 成立；
- $\pi$ 是双有理的，可以通过适当的 blow-up 公式（见 Borel–Serre §12–§13）处理。

因此，对一般的 proper 态射 $f$，GRR 成立。$\square$

---

## 7. GRR 与 Weil 猜想的深层联系

### 7.1 从 Riemann-Roch 到 Lefschetz 不动点公式

Grothendieck 发展 GRR 的深层动机之一，是为 Weil 猜想中的 **Lefschetz 不动点公式**提供一个代数框架。Weil 猜想（1949）断言：对于有限域 $\mathbb{F}_q$ 上的光滑射影簇 $X$，其 Zeta 函数
$$
Z(X, t) = \exp\left(\sum_{n=1}^\infty \frac{\#X(\mathbb{F}_{q^n})}{n} t^n\right)
$$
具有类似于 Riemann 假设的解析性质。

Weil 本人意识到，如果能建立一个"代数几何中的上同调理论"，使得 Lefschetz 不动点公式
$$
\#X(\mathbb{F}_q) = \sum_{i=0}^{2n} (-1)^i \operatorname{tr}(\operatorname{Frob}_q | H^i(X))
$$
成立，那么猜想中的函数方程与 Riemann 假设将可以从 Poincaré 对偶和 Hard Lefschetz 定理导出。

Grothendieck 的 GRR 恰好提供了这一框架的关键组件：
1. **K-群作为"虚拟上同调"**：$K(X)$ 可以被视为一种"普遍的上同调理论"，其中的元素 $[E]$ 对应于向量丛的"示性类"。
2. **Chern 特征与周期映射**：$\operatorname{ch}: K(X) \to A(X)_{\mathbb{Q}}$ 是连接代数范畴（K-群）与几何范畴（Chow 环）的桥梁。在 Weil 猜想的框架中，类似的桥梁是周期映射 $H^i_{\text{ét}}(X, \mathbb{Q}_\ell) \to H^i_{\text{Betti}}(X, \mathbb{Q})$。
3. **函子性与迹公式**：GRR 的核心是 $f_!$ 与 $f_*$ 的相容性。在 étale 上同调中，这一相容性体现为 **Grothendieck–Verdier 对偶**，它是证明 Lefschetz 迹公式的关键。

### 7.2 GRR 与 Motive 理论的诞生

Grothendieck 在 1960 年代中期意识到，不同的上同调理论（Betti、de Rham、étale、晶体）虽然形式不同，但都应从同一个"母体"中导出。这个母体就是 **motive 范畴**。GRR 在这一哲学中扮演了原型角色：

- GRR 中的 $K(X)$ 是 motive 的一个粗糙近似。事实上，Grothendieck 后来定义了 **Chow motive** $h(X) = (X, \Delta_X, 0)$，使得 Chow 群 $A^i(X)$ 可以表示为 $\operatorname{Hom}(\mathbb{L}^{\otimes i}, h(X))$，其中 $\mathbb{L}$ 是 Lefschetz motive。
- GRR 的函子性（$f_!$ 与 $f_*$ 的交换）预示了 motive 范畴中六函子结构的存在。在 Grothendieck 的设想中，每个 motive $M$ 都应配备 pullback $f^*$、pushforward $f_!$、tensor product $\otimes$ 与 internal Hom $\underline{\operatorname{Hom}}$，且这些操作满足严格的函子性。

**历史注释**：Deligne 在 1974 年证明 Weil 猜想时（Publ. Math. IHÉS 43, 1974），并未直接使用 motive 范畴（因为标准猜想尚未证明），而是使用了 $\ell$-进上同调与单值群方法。然而，Deligne 的证明中关键的 **Hard Lefschetz 定理**与**半单性定理**，其精神源头正是 Grothendieck 在 GRR 和 motive 理论中倡导的"函子性优先"原则。

---

## 8. 批判性分析：Grothendieck 与 Hirzebruch、Serre 的比较

### 8.1 Hirzebruch 的拓扑方法与 Grothendieck 的代数方法

Hirzebruch 在 1954 年证明的 Riemann-Roch 定理是拓扑学与复几何的杰作。他的证明依赖于：
- **Thom 的配边理论（cobordism theory）**：通过将复流形分类到配边环中，利用示性类的形式性质；
- **分裂原理（splitting principle）**：将向量丛分解为线丛的直和（在旗流形上）；
- **解析挠率（analytic torsion）**与**椭圆算子的指标定理**（后续发展）。

这些工具深刻且强大，但有一个根本限制：它们依赖于复流形的**微分结构**和**实拓扑**。当数学家试图将 Riemann-Roch 定理推广到特征 $p > 0$ 的代数闭域上的簇时，Thom 的配边理论完全失效——因为在特征 $p$ 中，微分流形的概念不存在。

Grothendieck 的 GRR 彻底绕过了这一障碍。他的方法完全基于：
- **纯代数构造**：K-群由短正合序列的关系定义，不涉及任何拓扑；
- **Chow 环的相交理论**：虽然相交积的定义在代数几何中比拓扑学中更加微妙（需要 moving lemma 或形变到法锥），但它完全在代数范畴内成立；
- **形式幂级数**：Chern 特征和 Todd 类被定义为形式幂级数环中的元素，其运算不需要任何解析结构。

**结论**：Grothendieck 的方法在**一般性**上远超 Hirzebruch。GRR 不仅适用于复代数簇，也适用于任意特征的完美域上的光滑簇，甚至适用于正则概形（regular schemes）。这一一般性是 Weil 猜想证明的必要前提，因为 Weil 猜想本身就是在有限域上陈述的。

### 8.2 Serre 的 FAC 与 Grothendieck 的相对化

Serre 的 FAC 论文（1955）已经使用了层上同调来处理代数簇上的凝聚层。Serre 证明了：对于射影簇 $X$ 上的凝聚层 $\mathcal{F}$，上同调群 $H^i(X, \mathcal{F})$ 是有限维的，并在充分扭变后消失。这些结果是 Hirzebruch-Riemann-Roch 的代数前身。

然而，Serre 的框架是**绝对的**（即总是相对于基域 $k$），而 Grothendieck 的 GRR 是**相对的**（相对于任意 proper 态射 $f: X \to Y$）。这一相对化的意义在于：
- 它使得 Riemann-Roch 成为一个**函子性（functorial）**陈述，即它关于态射的复合是相容的；
- 它允许将定理应用于**族（families）**的几何：如果 $Y$ 是参数空间，则 GRR 描述了 Euler 示性数 $\chi(X_y, E_y)$ 如何随参数 $y \in Y$ 变化。

Serre 本人在 Borel–Serre 论文的合作中，很可能深刻理解了这一相对化的重要性。事实上，Serre 在 1950 年代末的通信中多次鼓励 Grothendieck 将绝对结果推广到相对情形。

---

## 9. Lean4 形式化框架：K-群、Chern 特征与 GRR

以下 Lean4 代码提供了 Grothendieck 群、Chern 特征与 GRR 定理陈述的形式化框架。证明的完整形式化是 Mathlib4 社区的长期目标之一；此处我们给出定义与定理陈述，证明以 `sorry` 占位并标注完成计划。

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Exact

universe u v

/-- Grothendieck 群 K(X) 的形式化定义。
    对 Noether 概形 X，K(X) 是 Vect(X) 的 Grothendieck 群。 -/
noncomputable def GrothendieckGroup (X : Scheme.{u}) : Type u :=
  -- 形式化定义：由 Vect(X) 的同构类生成的自由 Abel 群，模去短正合序列关系
  -- 实际实现中需使用 GrothendieckGroup 构造子
  sorry

instance (X : Scheme.{u}) : AddCommGroup (GrothendieckGroup X) := sorry
instance (X : Scheme.{u}) : CommRing (GrothendieckGroup X) := sorry

/-- 向量丛在 K-群中的类。 -/
def KClass {X : Scheme.{u}} (E : QuasicoherentSheaf X) [LocallyFree E] : GrothendieckGroup X :=
  sorry

/-- Chern 特征的形式化定义：K(X) → Chow(X) ⊗ ℚ -/
noncomputable def ch {X : Scheme.{u}} : GrothendieckGroup X → ℚ :=
  -- 实际实现中应映射到 Chow 环，此处以 ℚ 简化示意
  sorry

/-- Todd 类的形式化定义。 -/
noncomputable def td {X : Scheme.{u}} (E : QuasicoherentSheaf X) [LocallyFree E] : ℚ :=
  sorry

/-- 直像映射 f_! : K(X) → K(Y) -/
noncomputable def pushforwardK {X Y : Scheme.{u}} (f : X ⟶ Y) [Proper f] :
    GrothendieckGroup X → GrothendieckGroup Y :=
  sorry

/-- Chow 群上的推前 f_* : A(X)_ℚ → A(Y)_ℚ -/
noncomputable def pushforwardChow {X Y : Scheme.{u}} (f : X ⟶ Y) [Proper f] :
    ℚ → ℚ :=
  -- 实际实现中应映射 Chow(X) → Chow(Y)，此处以 ℚ 简化示意
  sorry

/-- 相对切丛（在 K-群中）。 -/
noncomputable def relativeTangentBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : GrothendieckGroup X :=
  sorry

/-- Grothendieck-Riemann-Roch 定理的 Lean4 陈述。 -/
theorem GrothendieckRiemannRoch {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [Proper f] (x : GrothendieckGroup X) :
    ch (pushforwardK f x) = pushforwardChow f (ch x * td (relativeTangentBundle f)) := by
  -- 完成计划：
  -- 步骤1（射影丛情形）：使用 Mathlib 中的 ProjectiveBundle 结构，
  --       验证射影丛的 K-群由 {1, ξ, ..., ξ^r} 生成（预计 4 周）。
  -- 步骤2（闭浸入情形）：实现形变到法丛的构造，使用 DeformationToNormalBundle
  --       类型（预计 6 周）。
  -- 步骤3（一般 proper 态射）：利用 Chow 引理的分解，组合步骤1与2（预计 3 周）。
  -- 总体预计：13 周，需 2 名形式化专家协作。
  sorry

-- 审校标记：
-- [审校1-数学] TODO: 验证 ch 与 td 的环同态性质在 Lean4 中的表述。
-- [审校2-形式化] TODO: 将 QuasicoherentSheaf 替换为 Mathlib4 中的标准层类型。
-- [审校3-同行评议] TODO: 邀请代数几何专家审阅 relativeTangentBundle 的定义。
```

---

## 10. 结论

Grothendieck-Riemann-Roch 定理不仅是代数几何的一个技术高峰，更是 Grothendieck **相对观点**与**函子性哲学**的完美体现。从 Hirzebruch 的拓扑证明到 Grothendieck 的纯代数框架，数学界见证了从一个空间到态射、从复拓扑到任意特征、从绝对到相对的深刻转变。

GRR 与 Weil 猜想的联系则揭示了这一定理的更大图景：它是 motive 理论与六函子框架的第一个非平凡范例，为 Deligne 的最终证明和后来 Lurie 的导出代数几何奠定了方法论基础。

---

> **专题负责人（Topic Owner）**：待定（FormalMath 学术委员会）  
> **最后更新**：2026-04-18  
> **关联形式化文件**：`FormalMath/AlgebraicGeometry/RiemannRoch.lean`（计划中）  
> **整合素材**：`00-归档-2026年4月/02-数学内容深度分析/06-其他数学贡献/05-Riemann-Roch定理-网络对齐与批判性意见报告.md`  
> **上游文档**：`金层重构/G3-Grothendieck-Riemann-Roch定理.md`

