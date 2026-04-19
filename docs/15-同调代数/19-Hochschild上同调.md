---
title: Hochschild上同调
description: 介绍Hochschild上同调的定义、与代数形变的关系、Gerstenhaber代数结构，以及在非交换几何中的应用。
msc_primary:
  - 16E40
msc_secondary:
  - 16S80
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
    - id: gerstenhaber
      type: textbook
      title: Deformation Theory
      authors:
        - Robin Hartshorne
      publisher: Springer
      year: 2010
      msc: 14-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Hochschild上同调

## 引言

Hochschild上同调是研究结合代数及其双模的标准同调工具，由Gerhard Hochschild于1945年引入。它统一了群上同调与Lie代数上同调的思想，将其推广到结合代数范畴。Hochschild上同调最引人注目的应用是在代数形变理论中：$HH^2(A,A)$ 分类代数的无穷小形变，$HH^3(A,A)$ 则包含形变结合的障碍。此外，Hochschild上同调 $HH^*(A,A)$ 具有Gerstenhaber代数结构——一种兼有分次交换积和Poisson型括号的丰富代数结构——这一结构在弦论、镜像对称和非交换几何中扮演着核心角色。

本教程从Hochschild复形的严格定义出发，证明 $d^2=0$，建立低维解释与形变理论的精确联系，并计算多项式代数和对角代数的Hochschild上同调。

---

## 1. Hochschild复形

### 1.1 定义

设 $k$ 为域，$A$ 为 $k$-代数，$M$ 为 $A$-$A$-双模（即左 $A$ 模且右 $A$ 模，满足相容性 $(am)a' = a(ma')$）。

**定义 1.1（Hochschild上链）**。对 $n \geq 0$，$n$-上链空间定义为
$$C^n(A, M) := \operatorname{Hom}_k(A^{\otimes n}, M).$$
特别地，$C^0(A,M) = M$，$C^1(A,M) = \operatorname{Hom}_k(A, M)$，$C^2(A,M) = \operatorname{Hom}_k(A \otimes A, M)$。

**定义 1.2（Hochschild上边缘）**。上边缘 $d: C^n(A,M) \to C^{n+1}(A,M)$ 定义为
$$\begin{aligned}
df(a_1, \dots, a_{n+1}) := &\, a_1 f(a_2, \dots, a_{n+1}) \\
&+ \sum_{i=1}^n (-1)^i f(a_1, \dots, a_i a_{i+1}, \dots, a_{n+1}) \\
&+ (-1)^{n+1} f(a_1, \dots, a_n) a_{n+1}.
\end{aligned}$$

**定理 1.1**。$d^2 = 0$。

**证明**：对 $f \in C^n(A,M)$，$d(df)(a_1,\dots,a_{n+2})$ 按定义展开为三组项：
1. **首项作用**：$a_1 \cdot df(a_2,\dots,a_{n+2})$ 展开后产生 $a_1a_2f(\dots)$ 与 $a_1f(a_2a_3,\dots)$ 等；
2. **中间折叠**：$\sum (-1)^i df(\dots, a_ia_{i+1}, \dots)$ 展开后产生折叠位置的乘积作用与二次折叠；
3. **末项作用**：$(-1)^{n+2} df(\dots) a_{n+2}$ 展开后产生末项的右作用。

具体对 $n=1$ 验证：$f \in C^1(A,M)$，
$$df(a,b) = af(b) - f(ab) + f(a)b,$$
$$d(df)(a,b,c) = a(df)(b,c) - (df)(ab,c) + (df)(a,bc) - (df)(a,b)c$$
$$= a[bf(c)-f(bc)+f(b)c] - [(ab)f(c)-f(abc)+f(ab)c]$$
$$+ [af(bc)-f(abc)+f(a)bc] - [af(b)-f(ab)+f(a)b]c$$
$$= abf(c) - af(bc) + af(b)c - abf(c) + f(abc) - f(ab)c$$
$$+ af(bc) - f(abc) + f(a)bc - af(b)c + f(ab)c - f(a)bc = 0.$$
一般情形由三项各自的抵消模式保证：首项与中间折叠的相邻项抵消，中间折叠的二次折叠自身成对抵消，末项与中间折叠的另一相邻项抵消。∎

**定义 1.3（Hochschild上同调）**。第 $n$ 个Hochschild上同调群为
$$HH^n(A, M) := H^n(C^\bullet(A,M), d) = \frac{Z^n(A,M)}{B^n(A,M)},$$
其中 $Z^n = \ker d$，$B^n = \operatorname{im} d$。

---

## 2. 低维上同调的解释

### 2.1 $HH^0$：中心

**命题 2.1**。$HH^0(A, M) = M^A := \{m \in M : am = ma \text{ 对所有 } a \in A\}$。

**证明**：$C^0 = M$，$dm(a) = am - ma$。故 $\ker d = \{m : am = ma \, \forall a\}$。∎

当 $M = A$ 时，$HH^0(A,A) = Z(A)$ 为 $A$ 的中心。

### 2.2 $HH^1$：导子

**定义 2.1**。线性映射 $D: A \to M$ 称为 **导子**，若
$$D(ab) = aD(b) + D(a)b \quad \forall a,b \in A.$$
若存在 $m \in M$ 使 $D(a) = am - ma$，则称 $D$ 为 **内导子**。

**命题 2.2**。$HH^1(A, M) = \operatorname{Der}(A, M) / \operatorname{InnDer}(A, M)$。

**证明**：$f \in C^1$ 满足 $df = 0$ 当且仅当 $af(b) - f(ab) + f(a)b = 0$，即 $f$ 为导子。$f = dg$ 对 $g \in C^0 = M$ 当且仅当 $f(a) = ag - ga$，即 $f$ 为内导子。∎

### 2.3 $HH^2$：代数扩张与形变

**定义 2.2（奇异扩张）**。$A$ 由 $M$ 的 **奇异扩张**（singular extension）是短正合列
$$0 \longrightarrow M \longrightarrow B \longrightarrow A \longrightarrow 0,$$
其中 $B$ 为 $k$-代数，$M$ 为 $B$ 的双边理想且 $M^2 = 0$。

**定理 2.1**。$HH^2(A, M)$ 与 $A$ 由 $M$ 的奇异扩张的等价类之间存在自然双射。

**证明概要**：给定扩张，选取 $k$-线性截面 $s: A \to B$。定义 $f(a,b) = s(a)s(b) - s(ab) \in M$（因 $\pi(f(a,b)) = ab - ab = 0$）。由 $B$ 的结合性，
$$s(a)(s(b)s(c)) = (s(a)s(b))s(c)$$
展开并利用 $M^2 = 0$（故 $s(a)f(b,c) = as(b,c)$ 在 $M$ 中的左作用由 $A$-模结构给出），得 $df = 0$。不同截面的选择导致相差上边缘。反之，给定2-上闭链 $f$，在 $B = A \oplus M$ 上定义乘法
$$(a,m)(b,n) = (ab, an + mb + f(a,b)),$$
则 $f$ 的上闭链条件保证结合律，上边缘的变化对应截面重选。∎

### 2.4 $HH^2$ 与无穷小形变

**定义 2.3（一阶形变）**。$A$ 的 **一阶形变** 是 $k[\varepsilon]/\varepsilon^2$-代数结构 $A_\varepsilon = A \oplus \varepsilon A$，其乘法为
$$(a + \varepsilon b)(c + \varepsilon d) = ac + \varepsilon(ad + bc + f(a,c)),$$
其中 $f \in C^2(A,A)$。结合律要求 $f$ 为2-上闭链；等价的形变（通过 $k[\varepsilon]$-代数同构）相差上边缘。

**定理 2.2**。$HH^2(A,A)$ 分类 $A$ 的一阶形变的等价类。

---

## 3. Gerstenhaber代数结构

### 3.1 杯积

**定义 3.1**。对 $f \in C^m(A,A)$，$g \in C^n(A,A)$，定义 **杯积** $f \smile g \in C^{m+n}(A,A)$ 为
$$(f \smile g)(a_1, \dots, a_{m+n}) = f(a_1, \dots, a_m) g(a_{m+1}, \dots, a_{m+n}).$$

**定理 3.1**。杯积在上同调上诱导分次交换积：对 $[f] \in HH^m$，$[g] \in HH^n$，
$$[f] \smile [g] = (-1)^{mn} [g] \smile [f].$$

### 3.2 Gerstenhaber括号

**定义 3.2**。对 $f \in C^m$，$g \in C^n$，定义 **Gerstenhaber括号** $[f,g] \in C^{m+n-1}$ 为
$$[f,g] = \sum_{i=1}^m (-1)^{(n-1)(i-1)} f \circ_i g - (-1)^{(m-1)(n-1)} \sum_{j=1}^n (-1)^{(m-1)(j-1)} g \circ_j f,$$
其中 $(f \circ_i g)(a_1,\dots,a_{m+n-1}) = f(a_1,\dots,a_{i-1}, g(a_i,\dots,a_{i+n-1}), a_{i+n},\dots)$。

**定理 3.2**。Gerstenhaber括号在上同调上满足：
1. **分次反对称**：$[f,g] = -(-1)^{(|f|-1)(|g|-1)}[g,f]$；
2. **分次Jacobi恒等式**；
3. **Poisson恒等式**：$[f \smile g, h] = [f,h] \smile g + (-1)^{(|f|-1)|h|} f \smile [g,h]$。

因此 $(HH^*(A,A), \smile, [-,-])$ 构成 **Gerstenhaber代数**。

---

## 4. 具体计算例子

### 例子 4.1：多项式代数 $k[x]$

**定理 4.1**。$HH^*(k[x], k[x]) \cong k[x] \otimes \Lambda^*(\xi)$，其中 $\xi$ 为1次生成元。具体地，$HH^n(k[x]) \cong k[x]$ 对所有 $n \geq 0$。

**证明概要**：利用Hochschild-Kostant-Rosenberg（HKR）定理。对光滑交换代数 $A$，
$$HH_n(A,A) \cong \Omega^n_{A/k}, \quad HH^n(A,A) \cong \Lambda^n \operatorname{Der}(A).$$
对 $A = k[x]$，$\Omega^1_{k[x]} \cong k[x]dx$，$\operatorname{Der}(k[x]) \cong k[x]\frac{d}{dx}$。故 $HH^n \cong k[x]$ 对所有 $n$。∎

### 例子 4.2：$k[x]/(x^2)$（外代数）

设 $A = k[\varepsilon]/\varepsilon^2$，$\varepsilon^2 = 0$。这是1维外代数。

取 $M = A$。$HH^0 = Z(A) = A$（因 $A$ 交换）。$HH^1 = \operatorname{Der}(A)/\operatorname{InnDer}(A)$。因 $A$ 交换，内导子为0。导子由 $D(\varepsilon)$ 决定：$D(1)=0$，$D(\varepsilon) = a + b\varepsilon$。由 $D(\varepsilon^2) = 2\varepsilon D(\varepsilon) = 0$，无额外约束。故 $\operatorname{Der}(A) \cong A$，$HH^1 = A \cong k^2$。

$HH^2$ 分类奇异扩张。$\dim HH^2(A,A)$ 可通过Bar复形计算。对有限维代数，可用quiver表示。$A$ 的quiver为一点带一圈（自环 $\varepsilon$ 满足 $\varepsilon^2=0$）。由一般理论，$\dim HH^2(A,A) = 1$（对应关系 $\varepsilon^2 = 0$ 的形变 $ \varepsilon^2 = t\varepsilon$）。

### 例子 4.3：矩阵代数 $M_n(k)$

**定理 4.2**。$HH^i(M_n(k), M_n(k)) = 0$ 对 $i > 0$，$HH^0 = Z(M_n(k)) = k \cdot I$。

**证明**：由Morita不变性，$HH^*(M_n(k)) \cong HH^*(k)$。而 $HH^0(k) = k$，$HH^i(k) = 0$ 对 $i > 0$（因 $k$ 的单位元使所有上边缘平凡）。∎

这反映了半单代数是"刚性"的：它没有非平凡的一阶形变（$HH^2 = 0$），也没有非平凡的外导子（$HH^1 = 0$）。

---

## 5. 与已有文档的关联

- [17-群上同调](17-群上同调.md)：群代数 $kG$ 的Hochschild上同调与群上同调的关系。
- [18-Lie代数上同调](18-Lie代数上同调.md)：包络代数 $U(\mathfrak{g})$ 的Hochschild上同调与Lie代数上同调。
- [07-左导出函子Ext](07-左导出函子Ext.md)：$HH^n(A,M) = \operatorname{Ext}^n_{A^e}(A,M)$，其中 $A^e = A \otimes A^{\mathrm{op}}$。
- [同调代数-具体计算例子](同调代数-具体计算例子.md)：同调代数中的显式计算方法。

---

## 参考文献

1. G. Hochschild, "On the cohomology groups of an associative algebra", *Ann. of Math.*, 46:58–67, 1945.
2. M. Gerstenhaber, "The cohomology structure of an associative ring", *Ann. of Math.*, 78:267–288, 1963.
3. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 9)
4. J.-L. Loday, *Cyclic Homology*, 2nd ed., Springer, 1998. (Appendix)

---

**适用**：docs/15-同调代数/
