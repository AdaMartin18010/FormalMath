---
msc_primary: 18E10
msc_secondary:
  - 18Gxx
  - 18E20
processed_at: '2026-04-20'
title: Abel范畴
---

# Abel范畴

## 1. 引言

Abel范畴（abelian category）是Grothendieck在1950年代为统一同调代数而引入的概念。它精确刻画了那些在类似交换群（或模范畴）的环境中进行"线性代数"操作所需的范畴性质：存在核与余核、每个单射是某个态射的核、每个满射是某个态射的余核、以及态射可分解为满射接单的合成。Abel范畴为同调代数提供了最一般的框架——在这个框架中，正合序列、五引理、蛇引理、同调长正合序列等工具都可以建立。本文从加性范畴出发，逐步引入Abel范畴的公理，建立核心同调工具。

## 2. 加性范畴

### 2.1 定义

**定义 2.1**。范畴 $\mathcal{A}$ 称为**预加性的**（preadditive），若每个 $\operatorname{Hom}(A, B)$ 为交换群，且复合运算为双线性。

**定义 2.2**。预加性范畴 $\mathcal{A}$ 称为**加性的**（additive），若它有余积（等价地，有限积存在且与余积重合）。此时零对象（既是始对象又是终对象）存在，记作 $0$。

**例 2.3**。$\mathbf{Ab}$、$R\text{-}\mathbf{Mod}$、有限生成自由 $R$-模范畴皆为加性范畴。

### 2.2 核与余核

**定义 2.4**。在加性范畴中，态射 $f: A \to B$ 的**核**（kernel）是满足 $f \circ k = 0$ 的泛映射 $k: K \to A$。对偶地，**余核**（cokernel）是满足 $q \circ f = 0$ 的泛映射 $q: B \to Q$。

**命题 2.5**。核是monomorphism，余核是epimorphism。

## 3. Abel范畴的公理

**定义 3.1**。加性范畴 $\mathcal{A}$ 称为**Abel范畴**，若满足：

1. 每个态射有核和余核；
2. 每个monomorphism是某个态射的核；
3. 每个epimorphism是某个态射的余核。

等价地，可替换(2)(3)为：
- 对任意 $f: A \to B$，自然映射 $\operatorname{coker}(\ker f) \to \ker(\operatorname{coker} f)$ 是同构。

这意味着每个态射 $f$ 可唯一分解为
$$A \xrightarrow{p} \operatorname{coim} f \xrightarrow{\bar{f}} \operatorname{im} f \xrightarrow{i} B,$$
其中 $p$ 为epimorphism（实际上是余核），$i$ 为monomorphism（实际上是核），$\bar{f}$ 为同构当且仅当 $f$ 既monic又epic。

**例 3.2**。以下为Abel范畴：
- $\mathbf{Ab}$（交换群）；
- $R\text{-}\mathbf{Mod}$（环 $R$ 上的左模范畴）；
- 凝聚 $\"mathcal{O}_X$-模范畴（$X$ 为Noetherian概形）；
- 拓扑空间上的 Abel 群层范畴（见[06-层作为范畴](06-层作为范畴.md)）。

**非例 3.3**。$\mathbf{Grp}$ 非Abel范畴（monomorphism不必为核）。有限生成Abel群范畴非Abel（核可能非有限生成）。

## 4. 正合序列

### 4.1 定义

**定义 4.1**。在Abel范畴中，序列 $A \xrightarrow{f} B \xrightarrow{g} C$ 称为**正合的**（exact），若 $\operatorname{im} f = \ker g$（作为 $B$ 的子对象）。

**定义 4.2**。短正合序列 $0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0$ 表示 $f$ monic，$g$ epic，$\operatorname{im} f = \ker g$。

### 4.2 五引理

**定理 4.3**（五引理）。设Abel范畴中有交换图
$$\begin{array}{ccccccccc}
A_1 & \to & A_2 & \to & A_3 & \to & A_4 & \to & A_5 \\
\downarrow{f_1} & & \downarrow{f_2} & & \downarrow{f_3} & & \downarrow{f_4} & & \downarrow{f_5} \\
B_1 & \to & B_2 & \to & B_3 & \to & B_4 & \to & B_5
\end{array}$$
两行皆正合。若 $f_1$ epic，$f_5$ monic，$f_2$ 和 $f_4$ 同构，则 $f_3$ 同构。

*证明*。经典追图法（diagram chase），在模范畴中直观。在一般Abel范畴中，可用Mitchell嵌入定理将其化为模范畴中的问题。$\square$

### 4.3 蛇引理

**定理 4.4**（蛇引理）。在Abel范畴中，给定交换图
$$\begin{array}{ccccccccc}
& & A & \xrightarrow{f} & B & \xrightarrow{g} & C & \to & 0 \\
& & \downarrow{a} & & \downarrow{b} & & \downarrow{c} & & \\
0 & \to & A' & \xrightarrow{f'} & B' & \xrightarrow{g'} & C' & &
\end{array}$$
两行正合。则存在连接同态 $\delta: \ker c \to \operatorname{coker} a$ 使
$$\ker a \to \ker b \to \ker c \xrightarrow{\delta} \operatorname{coker} a \to \operatorname{coker} b \to \operatorname{coker} c$$
正合。

## 5. 链复形与同调

### 5.1 链复形范畴

**定义 5.1**。Abel范畴 $\mathcal{A}$ 中的**链复形** $C_\bullet$ 是一列对象和态射
$$\cdots \to C_{n+1} \xrightarrow{d_{n+1}} C_n \xrightarrow{d_n} C_{n-1} \to \cdots$$
满足 $d_n \circ d_{n+1} = 0$。链复形全体构成范畴 $\operatorname{Ch}(\mathcal{A})$。

**定理 5.2**。若 $\mathcal{A}$ 为Abel范畴，则 $\operatorname{Ch}(\mathcal{A})$ 也是Abel范畴。

### 5.2 同调对象

**定义 5.3**。链复形 $C_\bullet$ 的**$n$-维同调**为
$$H_n(C_\bullet) = \operatorname{coker}(C_{n+1} \to \ker d_n) = \ker(\operatorname{coker} d_{n+1} \to C_{n-1}).$$

在 $R\text{-}\mathbf{Mod}$ 中，这还原为通常的 $H_n = Z_n / B_n$。

### 5.3 同调长正合序列

**定理 5.4**。在Abel范畴中，链复形的短正合序列 $0 \to A_\bullet \to B_\bullet \to C_\bullet \to 0$ 诱导同调的长正合序列
$$\cdots \to H_n(A) \to H_n(B) \to H_n(C) \xrightarrow{\partial} H_{n-1}(A) \to \cdots.$$

## 6. 内射对象与投射对象

**定义 6.1**。对象 $I \in \mathcal{A}$ 称为**内射的**（injective），若函子 $\operatorname{Hom}(-, I): \mathcal{A}^{\mathrm{op}} \to \mathbf{Ab}$ 正合。等价地，对任意monomorphism $A \hookrightarrow B$，任意 $A \to I$ 可延拓到 $B \to I$。

**定义 6.2**。对象 $P \in \mathcal{A}$ 称为**投射的**（projective），若 $\operatorname{Hom}(P, -)$ 正合。等价地，对任意epimorphism $B \twoheadrightarrow C$，任意 $P \to C$ 可提升为 $P \to B$。

**例 6.3**。在 $R\text{-}\mathbf{Mod}$ 中，自由模是投射的。$\mathbb{Q}$ 在 $\mathbf{Ab}$ 中是内射的（ divisible 群皆内射）。Baer判别法：$I$ 内射当且仅当对任意理想 $J \subseteq R$，$J \to I$ 可延拓到 $R \to I$。

## 7. 与项目其他部分的关联

Abel范畴是同调代数的通用语言。在代数拓扑（见`docs/12-代数拓扑/`）中，奇异链复形、单纯链复形皆为Abel群范畴中的对象，同调长正合序列、蛇引理是基本工具。在交换代数（见`docs/02-代数结构/交换代数/`）中，模的Ext和Tor函子通过投射/内射分解定义，这是Abel范畴中导出函子的特例。层范畴是Abel范畴的重要例子（见[06-层作为范畴](06-层作为范畴.md)），层上同调由此建立。在代数几何中，凝聚层范畴的Abel性质是理论基石（见[08-范畴论在代数几何中的应用](08-范畴论在代数几何中的应用.md)）。

## 8. 参考文献

1. A. Grothendieck, "Sur quelques points d'algèbre homologique", *Tôhoku Math. J.* 9 (1957), 119–221.
2. S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998.
3. P. Freyd, *Abelian Categories*, Harper & Row, 1964.
4. C. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994.
5. 陈志杰，《同调代数》，高等教育出版社，2009。
