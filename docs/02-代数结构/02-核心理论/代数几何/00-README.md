---
title: 代数几何
msc_primary: 00

  - 00A99
  - 16A99
  - 97A99
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

# 代数几何：从代数簇到概形

代数几何研究多项式方程组的解集及其几何性质。从古典的代数曲线与曲面，到 Grothendieck 的概形理论，再到现代的导出代数几何与镜像对称，代数几何已成为数学中最深刻、最活跃的分支之一。

## 1. 仿射代数簇

### 1.1 仿射空间与 Zariski 拓扑

**定义 1.1（仿射空间）**. 设 $k$ 为域，$n$ 维仿射空间定义为：

$$\mathbb{A}_k^n = \{(a_1, \dots, a_n) : a_i \in k\}.$$

**定义 1.2（代数集）**. 对理想 $I \subseteq k[x_1, \dots, x_n]$，定义其零点集为：

$$V(I) = \{P \in \mathbb{A}_k^n : f(P) = 0,\ \forall f \in I\}.$$

$\mathbb{A}_k^n$ 的子集称为代数集，若它是某个理想的零点集。

**定义 1.3（Zariski 拓扑）**. Zariski 闭集恰为代数集。即 $U \subseteq \mathbb{A}_k^n$ 为开集当且仅当 $\mathbb{A}_k^n \setminus U = V(I)$ 对某理想 $I$。

### 1.2 Hilbert 零点定理

**定理 1.4（Hilbert 零点定理，弱形式）**. 设 $k$ 为代数闭域，$I \subseteq k[x_1, \dots, x_n]$ 为真理想。则 $V(I) \neq \emptyset$。

*证明概要*. 利用 Noether 归一化引理将问题约化到单变量情形，或直接利用 $k[x_1, \dots, x_n]$ 为 Jacobson 环的性质：每个真理想包含于某极大理想，而极大理想在代数闭域上恰为 $(x_1 - a_1, \dots, x_n - a_n)$。$\square$

**定理 1.5（Hilbert 零点定理，强形式）**. 设 $k$ 代数闭，$I \subseteq k[x_1, \dots, x_n]$ 为理想。则 $I(V(I)) = \sqrt{I}$，其中 $\sqrt{I} = \{f : f^m \in I \text{ 对某 } m\}$ 为根理想。

*证明*. $\sqrt{I} \subseteq I(V(I))$ 显然。对 $f \notin \sqrt{I}$，局部化 $k[x_1, \dots, x_n]_f$ 中有极大理想（由弱形式），对应 $V(I)$ 中使 $f \neq 0$ 的点。$\square$

## 2. 概形初步

### 2.1 层与局部环层空间

**定义 2.1（层）**. 拓扑空间 $X$ 上的预层（presheaf）$\mathcal{F}$ 是对每个开集 $U$ 赋予 Abel 群（或环、模）$\mathcal{F}(U)$，对包含 $V \subseteq U$ 赋予限制映射 $\rho_{UV}: \mathcal{F}(U) \to \mathcal{F}(V)$，满足 $\rho_{UU} = \operatorname{id}$ 和 $\rho_{VW} \circ \rho_{UV} = \rho_{UW}$。

预层称为层（sheaf），若对任意开覆盖 $U = \bigcup_i U_i$：
1. （唯一性）若 $s, t \in \mathcal{F}(U)$ 且 $s|_{U_i} = t|_{U_i}$ 对所有 $i$，则 $s = t$；
2. （粘接性）若 $s_i \in \mathcal{F}(U_i)$ 满足 $s_i|_{U_i \cap U_j} = s_j|_{U_i \cap U_j}$，则存在 $s \in \mathcal{F}(U)$ 使 $s|_{U_i} = s_i$。

**定义 2.2（局部环层空间）**. 环层空间 $(X, \mathcal{O}_X)$ 称为局部环层空间，若对所有 $P \in X$，茎（stalk）$\mathcal{O}_{X,P}$ 为局部环。

### 2.2 仿射概形

**定义 2.3（仿射概形）**. 对交换环 $A$，其谱 $\operatorname{Spec}(A)$ 为所有素理想组成的集合，配备 Zariski 拓扑（闭集为 $V(I) = \{\mathfrak{p} : I \subseteq \mathfrak{p}\}$）和结构层 $\mathcal{O}_{\operatorname{Spec}(A)}$（在开集 $D(f) = \operatorname{Spec}(A) \setminus V((f))$ 上取值 $A_f$）。

**定理 2.4**. $(\operatorname{Spec}(A), \mathcal{O}_{\operatorname{Spec}(A)})$ 是局部环层空间，且 $\mathcal{O}_{\operatorname{Spec}(A), \mathfrak{p}} \cong A_\mathfrak{p}$。

### 2.3 概形

**定义 2.5（概形）**. 概形（scheme）是局部同构于仿射概形的局部环层空间 $(X, \mathcal{O}_X)$：存在开覆盖 $X = \bigcup_i U_i$，使得每个 $(U_i, \mathcal{O}_X|_{U_i}) \cong \operatorname{Spec}(A_i)$ 对某环 $A_i$。

## 3. 凝聚层与上同调

### 3.1 模层与拟凝聚层

**定义 3.1（$\mathcal{O}_X$-模层）**. 层 $\mathcal{F}$ 称为 $\mathcal{O}_X$-模层，若对每个开集 $U$，$\mathcal{F}(U)$ 是 $\mathcal{O}_X(U)$-模，且限制映射与模结构相容。

**定义 3.2（拟凝聚层）**. $\mathcal{O}_X$-模层 $\mathcal{F}$ 称为拟凝聚的（quasi-coherent），若存在仿射开覆盖 $X = \bigcup \operatorname{Spec}(A_i)$，使得 $\mathcal{F}|_{\operatorname{Spec}(A_i)} \cong \widetilde{M_i}$ 对某 $A_i$-模 $M_i$（其中 $\widetilde{M_i}$ 为与 $M_i$ 关联的层）。

**定义 3.3（凝聚层）**. 设 $X$ 为 Noether 概形。拟凝聚层 $\mathcal{F}$ 称为凝聚的（coherent），若每个 $M_i$ 为有限生成 $A_i$-模。

### 3.2 层上同调

**定理 3.4（Serre 定理）**. 设 $X$ 为 Noether 概形。以下等价：
1. $X$ 为仿射概形；
2. 对所有拟凝聚层 $\mathcal{F}$ 和 $q > 0$，$H^q(X, \mathcal{F}) = 0$；
3. 对所有凝聚理想层 $\mathcal{I}$，$H^1(X, \mathcal{I}) = 0$。

*证明概要*. (1) $\Rightarrow$ (2)：仿射概形上的拟凝聚层对应模，而仿射开覆盖的 Čech 上同调由局部化给出，利用交换代数中的正合性可得消失。(2) $\Rightarrow$ (3) 显然。(3) $\Rightarrow$ (1)：利用 $H^1$ 消失证明任意凝聚层由全局截面生成，进而证明 $X \cong \operatorname{Spec}(\Gamma(X, \mathcal{O}_X))$。$\square$

## 4. 例子

### 4.1 例子：仿射直线与射影直线

**仿射直线** $\mathbb{A}_k^1 = \operatorname{Spec}(k[x])$。其点对应 $k[x]$ 的素理想：
- $(0)$（泛点，generic point）；
- $(x - a)$（$a \in k$，闭点）。

Zariski 拓扑中，非空开集为有限个闭点的补集，即 $D(f) = \{x : f(x) \neq 0\}$。

**射影直线** $\mathbb{P}_k^1$ 由两个仿射片 $U_0 = \operatorname{Spec}(k[x])$ 和 $U_1 = \operatorname{Spec}(k[x^{-1}])$ 粘合而成，粘合映射在 $U_0 \cap U_1 = \operatorname{Spec}(k[x, x^{-1}])$ 上为恒等。

$\mathbb{P}_k^1$ 上的可逆层（线丛）为 $\mathcal{O}(n)$（$n \in \mathbb{Z}$），满足：
- $\Gamma(\mathbb{P}^1, \mathcal{O}(n))$ 为 $n$ 次齐次多项式空间（$n \geq 0$），维数 $n+1$；
- $H^1(\mathbb{P}^1, \mathcal{O}(n)) = 0$（$n \geq -1$）。

### 4.2 例子：椭圆曲线

设 $k$ 为特征 $\neq 2, 3$ 的代数闭域。椭圆曲线 $E$ 为 $\mathbb{P}_k^2$ 中由 Weierstrass 方程定义的射影非奇异曲线：

$$y^2 z = x^3 + axz^2 + bz^3, \quad 4a^3 + 27b^2 \neq 0.$$

其亏格 $g = 1$，且 $E$ 具有群结构：取定点 $O = [0:1:0]$（无穷远点），则对 $P, Q \in E$，$P + Q$ 定义为：过 $P, Q$ 的直线与 $E$ 的第三个交点 $R$ 关于 $x$-轴的对称点。

**定理 4.1**. 椭圆曲线上的有理函数域 $k(E)$ 的除子类群 $\operatorname{Pic}^0(E)$ 与 $E$ 的点群同构。

*证明概要*. 对 $P \in E$，定义除子 $(P) - (O)$。映射 $P \mapsto [(P) - (O)]$ 给出 $E \to \operatorname{Pic}^0(E)$。利用 Riemann-Roch 定理证明这是同构：$\dim L(D) = \deg D$ 对 $D > 0$，故 $L((P) - (O))$ 为一维，给出逆映射。$\square$

## 5. 交叉引用

- [交换代数](docs/02-代数结构/03-应用分析/交换代数-基础.md) — 环、理想与局部化
- [概形理论深化](docs/13-代数几何/Stacks-Project-金层对齐/00-索引.md) — Grothendieck 的完整理论框架
- [层论基础](docs/02-代数结构/02-核心理论/代数几何/05-层与上同调-深度版.md) — 层的范畴性质与上同调计算
- [同调代数](docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md) — 导出函子与 Ext/Tor
- [黎曼曲面](docs/04-几何与拓扑/02-微分几何-扩展/03-复几何/01-黎曼曲面基础.md) — 复一维代数几何
- [代数数论](docs/05-数论/代数数论-基础.md) — 算术几何的数论基础

---

**适用**：docs/02-代数结构/02-核心理论/代数几何/
