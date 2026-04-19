---
title: Lie代数上同调
description: 介绍Lie代数上同调的Chevalley-Eilenberg复形、低维解释，以及它与Lie代数表示理论和形变理论的联系。
msc_primary:
  - 17B56
msc_secondary:
  - 17B10
  - 18G60
processed_at: '2026-04-20'
references:
  textbooks:
    - id: weibel_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Charles A. Weibel
      publisher: Cambridge University Press
      year: 1994
      msc: 18-01
    - id: knapp_lie
      type: textbook
      title: Lie Groups, Lie Algebras, and Cohomology
      authors:
        - Anthony W. Knapp
      publisher: Princeton University Press
      year: 1988
      msc: 22-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Lie代数上同调

## 引言

Lie代数上同调（Lie algebra cohomology）由Chevalley和Eilenberg于1948年系统建立，是群上同调到Lie代数范畴的自然推广。它通过外代数构造上链复形，将Lie代数的表示论、形变理论和结构问题转化为同调代数语言。低维上同调群具有深刻的代数意义：$H^0$ 给出不变量，$H^1$ 刻画外导子，$H^2$ 分类Lie代数扩张，$H^3$ 包含Jacobi恒等式的上同调障碍。

本教程从Chevalley-Eilenberg复形的严格定义出发，证明Whitehead引理，并通过具体例子展示计算技巧。

---

## 1. Chevalley-Eilenberg复形

### 1.1 基本定义

设 $\mathfrak{g}$ 为域 $k$ 上的Lie代数，$M$ 为 $\mathfrak{g}$-模（即 $k$-向量空间带有Lie代数表示 $\rho: \mathfrak{g} \to \mathfrak{gl}(M)$，常简记 $x \cdot m = \rho(x)m$）。

**定义 1.1（Chevalley-Eilenberg上链）**。对 $n \geq 0$，定义 $n$-上链空间
$$C^n(\mathfrak{g}, M) := \operatorname{Hom}_k(\Lambda^n \mathfrak{g}, M).$$
即反对称 $n$-重线性映射 $f: \mathfrak{g}^{\times n} \to M$ 的全体。

**定义 1.2（上边缘算子）**。上边缘 $d: C^n(\mathfrak{g}, M) \to C^{n+1}(\mathfrak{g}, M)$ 定义为
$$\begin{aligned}
df(x_0, \dots, x_n) := &\sum_{i=0}^n (-1)^i x_i \cdot f(x_0, \dots, \widehat{x_i}, \dots, x_n) \\
&+ \sum_{0 \leq i < j \leq n} (-1)^{i+j} f([x_i, x_j], x_0, \dots, \widehat{x_i}, \dots, \widehat{x_j}, \dots, x_n).
\end{aligned}$$

**定理 1.1**。$d^2 = 0$，即 $(C^\bullet(\mathfrak{g}, M), d)$ 构成上链复形。

**证明概要**：需验证对任意 $f \in C^n(\mathfrak{g}, M)$，$d(df) = 0$。将 $d(df)(x_0, \dots, x_{n+1})$ 按三项展开：
1. 第一项中 $x_i$ 作用在 $df$ 上产生双重作用；
2. 第二项中 $[x_i, x_j]$ 代入 $df$ 的第一项产生Lie括号的作用；
3. 第二项中 $[x_i, x_j]$ 代入 $df$ 的第二项产生双重Lie括号。

由Jacobi恒等式和模作用条件 $\rho([x,y]) = [\rho(x), \rho(y)]$，这三类项精确抵消。具体验证对 $n=0,1$ 直接计算即可，一般情形通过对称群 $S_{n+2}$ 的作用归纳完成。∎

**定义 1.3（Lie代数上同调）**。第 $n$ 个Lie代数上同调群定义为
$$H^n(\mathfrak{g}, M) := H^n(C^\bullet(\mathfrak{g}, M), d) = \frac{\ker(d: C^n \to C^{n+1})}{\operatorname{im}(d: C^{n-1} \to C^n)}.$$

当 $M = k$ 为平凡模（$x \cdot \lambda = 0$）时，记 $H^n(\mathfrak{g}) := H^n(\mathfrak{g}, k)$。

---

## 2. 低维上同调的解释

### 2.1 $H^0$：不变量

**命题 2.1**。$H^0(\mathfrak{g}, M) = M^{\mathfrak{g}} := \{m \in M : x \cdot m = 0 \text{ 对所有 } x \in \mathfrak{g}\}$。

**证明**：$C^0(\mathfrak{g}, M) = M$，$df(x) = x \cdot f$（因 $f \in M$ 无变量，第二项消失）。故 $\ker d = \{m : xm = 0 \, \forall x\} = M^{\mathfrak{g}}$，$\operatorname{im} d = 0$（因 $C^{-1}=0$）。∎

### 2.2 $H^1$：导子与内导子

**定义 2.1（导子）**。线性映射 $D: \mathfrak{g} \to M$ 称为 **导子**（derivation），若
$$D([x,y]) = x \cdot D(y) - y \cdot D(x) \quad \forall x,y \in \mathfrak{g}.$$
全体导子记为 $\operatorname{Der}(\mathfrak{g}, M)$。

**定义 2.2（内导子）**。对 $m \in M$，定义 **内导子** $D_m(x) = x \cdot m$。由模作用条件，$D_m$ 确为导子。全体内导子记为 $\operatorname{IDer}(\mathfrak{g}, M)$。

**命题 2.2**。$H^1(\mathfrak{g}, M) \cong \operatorname{Der}(\mathfrak{g}, M) / \operatorname{IDer}(\mathfrak{g}, M)$。

**证明**：$C^1(\mathfrak{g}, M) = \operatorname{Hom}(\mathfrak{g}, M)$。对 $f \in C^1$，
$$df(x,y) = x \cdot f(y) - y \cdot f(x) - f([x,y]).$$
故 $f \in \ker d$ 当且仅当 $f$ 为导子。$f \in \operatorname{im} d$ 当且仅当存在 $m \in M$ 使 $f(x) = x \cdot m$，即 $f$ 为内导子。∎

### 2.3 $H^2$：Lie代数扩张的分类

**定义 2.3（Lie代数扩张）**。一个 $M$ 由 $\mathfrak{g}$ 的 **Lie代数扩张** 是短正合列
$$0 \longrightarrow M \longrightarrow \widetilde{\mathfrak{g}} \longrightarrow \mathfrak{g} \longrightarrow 0,$$
其中 $M$ 为Abel Lie代数（$[M,M]=0$），且 $M$ 的 $\widetilde{\mathfrak{g}}$-伴随作用与给定的 $\mathfrak{g}$-模结构一致。

**定理 2.1**。$H^2(\mathfrak{g}, M)$ 与上述扩张的等价类之间存在自然双射。

**证明概要**：给定扩张，选取截面 $s: \mathfrak{g} \to \widetilde{\mathfrak{g}}$。定义因子集
$$f(x,y) = [s(x), s(y)] - s([x,y]) \in M.$$
由Jacobi恒等式，$f$ 满足上闭链条件 $df = 0$。不同截面的选择导致相差上边缘，故 $[f] \in H^2(\mathfrak{g}, M)$ 良定。

反之，给定上闭链 $f$，在向量空间 $\widetilde{\mathfrak{g}} = \mathfrak{g} \oplus M$ 上定义
$$[(x,m), (y,n)] = ([x,y], x\cdot n - y\cdot m + f(x,y)).$$
上闭链条件保证Jacobi恒等式成立；上边缘的变化对应于截面的重新选择，不改变等价类。∎

---

## 3. Whitehead引理与Weyl定理

### 3.1 Whitehead引理

**定理 3.1（Whitehead引理）**。设 $\mathfrak{g}$ 为特征零域上的半单Lie代数，$M$ 为有限维 $\mathfrak{g}$-模。则
$$H^1(\mathfrak{g}, M) = 0, \quad H^2(\mathfrak{g}, M) = 0.$$

**证明概要**（$H^1=0$）：利用Casimir元素。半单Lie代数的Killing型非退化，可选取基 $\{x_i\}$ 和对偶基 $\{x^i\}$，定义Casimir算子
$$C = \sum_i \rho(x_i)\rho(x^i) \in \operatorname{End}(M).$$
由Schur引理，$C$ 在每个不可约分支上为标量。利用 $C$ 可构造投影算子到不变子空间。

对 $f \in \operatorname{Der}(\mathfrak{g}, M)$，定义
$$m = -\sum_i x^i \cdot f(x_i) \in M.$$
直接计算（利用 $f$ 的导子性质和Casimir的性质）可得 $f(x) = x \cdot m$ 对所有 $x$，即 $f$ 为内导子。故 $H^1 = 0$。

$H^2=0$ 的证明类似但更复杂，需构造对任意2-上闭链 $f$ 的 primitives。核心仍是利用Casimir算子实现"平均化"，这是半单Lie代数表示论中的标准技巧。∎

### 3.2 Weyl完全可约定理

**定理 3.2（Weyl）**。半单Lie代数的有限维表示完全可约（即每个不变子空间有不变补空间）。

**证明**：设 $M$ 为有限维 $\mathfrak{g}$-模，$N \subseteq M$ 为子模。需找补子模 $N'$ 使 $M = N \oplus N'$。

考虑 $\mathfrak{g}$-模同态空间 $\operatorname{Hom}_k(M, N)$。子空间
$$W = \{f \in \operatorname{Hom}(M,N) : f|_N = \lambda \cdot \mathrm{id}_N \text{ 对某 } \lambda \in k\}$$
是 $\mathfrak{g}$-子模。由 $H^1(\mathfrak{g}, \operatorname{Hom}(M/N, N)) = 0$（Whitehead引理）和正合序列论证，存在 $\mathfrak{g}$-模同态 $p: M \to N$ 使 $p|_N = \mathrm{id}_N$。则 $N' = \ker p$ 为所求补子模。∎

---

## 4. 具体计算例子

### 例子 4.1：Abel Lie代数的上同调

设 $\mathfrak{a}$ 为 $n$ 维Abel Lie代数（$[x,y]=0$ 对所有 $x,y$），$M = k$ 为平凡模。

**计算**：上边缘算子简化为
$$df(x_0, \dots, x_n) = \sum_{i<j} (-1)^{i+j} f([x_i,x_j], \dots) = 0.$$
故 $d = 0$，$H^n(\mathfrak{a}) = C^n(\mathfrak{a}, k) = \operatorname{Hom}(\Lambda^n \mathfrak{a}, k) \cong \Lambda^n \mathfrak{a}^*$。

**结论**：
$$H^n(\mathfrak{a}) \cong \Lambda^n \mathfrak{a}^* \cong \binom{n}{n} k = k^{\binom{n}{n}}.$$
特别地，$\dim H^n(\mathfrak{a}) = \binom{n}{n}$。对 $n=2$：$H^0=k$，$H^1=k^2$，$H^2=k$。

这与de Rham上同调一致：Abel Lie代数对应环面 $T^n$，其de Rham上同调恰为外代数。

### 例子 4.2：$\mathfrak{sl}(2, \mathbb{C})$ 的上同调

$\mathfrak{sl}(2, \mathbb{C})$ 的标准基为
$$H = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \quad E = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \quad F = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix},$$
满足 $[H,E]=2E$，$[H,F]=-2F$，$[E,F]=H$。

**计算 $H^*(\mathfrak{sl}(2), \mathbb{C})$（平凡模）**：

由Whitehead引理，$H^1 = H^2 = 0$。

对 $H^3$：考虑Killing型给出的3-形式
$$\omega(x,y,z) = \kappa([x,y], z) = \operatorname{tr}(\operatorname{ad}[x,y] \circ \operatorname{ad} z).$$
可验证 $d\omega = 0$（由Jacobi恒等式），且 $\omega \neq 0$（如 $\omega(H,E,F) = \kappa(H,H) = 8$）。

**定理 4.1**。$H^n(\mathfrak{sl}(2, \mathbb{C}), \mathbb{C}) = \begin{cases} \mathbb{C} & n = 0, 3, \\ 0 & n = 1, 2. \end{cases}$

更高维的上同调由 $H^3$ 生成：$H^*(\mathfrak{sl}(2)) \cong \Lambda^*(u)$，其中 $u$ 为3次生成元。这与 $S^3 \cong SU(2)$ 的上同调一致，反映了Whitehead定理：紧Lie群 $G$ 的实上同调与其Lie代数的上同调同构（$H^*(\mathfrak{g}, \mathbb{R}) \cong H^*(G, \mathbb{R})$）。

---

## 5. 与已有文档的关联

- [17-群上同调](17-群上同调.md)：Lie代数上同调是群上同调的Lie类比，通过包络代数和指数映射建立联系。
- [19-Hochschild上同调](19-Hochschild上同调.md)：包络代数 $U(\mathfrak{g})$ 的Hochschild上同调与Lie代数上同调通过Hochschild-Kostant-Rosenberg定理相关。
- [李群李代数基础](../../11-高级数学/李群李代数-基础.md)：李群与李代数的基本理论。
- [18-Lie代数上同调](18-Lie代数上同调.md)：Lie代数上同调与同调维数。

---

## 参考文献

1. C. Chevalley, S. Eilenberg, "Cohomology theory of Lie groups and Lie algebras", *Trans. Amer. Math. Soc.*, 63:85–124, 1948.
2. A. W. Knapp, *Lie Groups, Lie Algebras, and Cohomology*, Princeton Univ. Press, 1988.
3. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 7)
4. J. L. Koszul, "Homologie et cohomologie des algèbres de Lie", *Bull. Soc. Math. France*, 78:65–127, 1950.

---

**适用**：docs/15-同调代数/
