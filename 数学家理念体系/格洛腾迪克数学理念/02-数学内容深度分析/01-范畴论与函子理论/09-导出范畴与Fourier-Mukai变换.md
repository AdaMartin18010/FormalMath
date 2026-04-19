---
title: "导出范畴与Fourier-Mukai变换：Grothendieck范畴遗产的现代发展"
level: gold
course: Grothendieck数学理念
msc_primary: 18
msc_secondary:
  - 18E30
references:
  textbooks:
    - title: "Triangulated Categories"
      author: "A. Neeman"
      edition: "Annals of Mathematics Studies 148"
      year: 2001
    - title: "Fourier-Mukai Transforms in Algebraic Geometry"
      author: "D. Huybrechts"
      edition: "Oxford Mathematical Monographs"
      year: 2006
  papers:
    - title: "Duality for projective morphisms"
      author: "S. Mukai"
      year: 1981
status: completed
---

## 1. 引言：从Grothendieck到Mukai的桥梁

Grothendieck在**SGA 6**和**Tohoku论文**中奠定了**同调代数**的现代基础，特别是**导出范畴（derived category）**的引入彻底改变了数学家处理复形和同调的方式。导出范畴不仅是一个技术工具，更是一种全新的数学思维方式：它将同调不变量从具体的复形中解放出来，使得**拟同构（quasi-isomorphism）**成为新的等价关系。

四十余年后，Shigeru Mukai在1981年发现了**Fourier-Mukai变换**——一种利用导出范畴的积分变换方法来研究代数簇的几何性质的技术。这一发现开启了代数几何的新篇章，将Grothendieck的范畴遗产与经典代数几何的深刻问题（如 birational geometry、模空间理论）紧密联系起来。

本文将追溯这一发展历程，分析导出范畴的核心结构，阐述Fourier-Mukai变换的基本原理，并探讨Grothendieck的范畴方法论如何在现代数学中持续产生深远影响。

## 2. 导出范畴：Grothendieck的范畴革命

### 2.1 从复形到导出范畴

设 $\mathcal{A}$ 为一个Abel范畴（如模范畴、凝聚层范畴）。传统的同调代数研究**链复形（chain complex）**范畴 $C(\mathcal{A})$，其中对象是复形，态射是链映射。两个复形之间的**同伦等价（homotopy equivalence）**是一种较弱的等价关系，但即使是同伦范畴 $K(\mathcal{A})$ 也无法完全消除"虚假的"信息。

Grothendieck的关键洞察是：真正重要的是**拟同构**——即在上同调上诱导同构的链映射。导出范畴 $D(\mathcal{A})$ 通过**形式地逆转所有拟同构**来构造：

$$D(\mathcal{A}) = K(\mathcal{A})[\{\text{quasi-isomorphisms}\}^{-1}]$$

**定理 2.1（Grothendieck–Verdier）**。上述范畴局部化存在，且 $D(\mathcal{A})$ 具有自然的**三角范畴（triangulated category）**结构。

*证明概要*：直接构造这样的局部化在集合论上存在困难（Gabriel–Zisman的局部化理论）。Verdier的解决方案是引入**Calculus of Fractions**：证明拟同构在 $K(\mathcal{A})$ 中满足适当的 Ore 条件，从而可以用" roofs "（$X \leftarrow Q \to Y$）来显式描述局部化后的态射。三角结构由**映射锥（mapping cone）**序列给出。$\square$

### 2.2 导出函子与分解

导出范畴的核心优势在于**导出函子（derived functor）**的自然构造。设 $F: \mathcal{A} \to \mathcal{B}$ 为一个左正合函子。由于 $F$ 一般不保持拟同构，它不能直接提升为导出范畴之间的函子。

Grothendieck的解决方案是利用**内射分解（injective resolution）**：

**定理 2.2（Grothendieck, Tohoku）**。若 $\mathcal{A}$ 具有足够的内射对象，则每个复形 $A^{\bullet} \in K^{+}(\mathcal{A})$ 都拟同构于一个由内射对象组成的复形 $I^{\bullet}$。

**定义 2.3（右导出函子）**。在导出范畴中，$F$ 的**右导出函子**定义为：

$$\mathbf{R}F(A^{\bullet}) = F(I^{\bullet})$$

其中 $A^{\bullet} \xrightarrow{\sim} I^{\bullet}$ 是内射分解。

这一定义的优雅之处在于：
1. **独立性**：$
\mathbf{R}F$ 不依赖于具体分解的选择（在导出范畴中唯一）。
2. **泛性质**：$\mathbf{R}F$ 是 $F$ 在导出范畴上的"最好"近似。
3. **长正合序列**：对任意短正合序列，存在连接同态诱导的长正合序列。

### 2.3 凝聚层的导出范畴

在代数几何中，设 $X$ 为一个概形。凝聚层范畴 $\operatorname{Coh}(X)$ 和拟凝聚层范畴 $\operatorname{QCoh}(X)$ 的导出范畴 $D^b_{\mathrm{coh}}(X)$ 和 $D^b_{\mathrm{qcoh}}(X)$ 是现代研究的核心对象。

**定理 2.4（Bondal–Orlov）**。设 $X$ 为光滑射影簇，$K_X$ 为丰富或反丰富典则丛。则 $X$ 的导出范畴 $D^b_{\mathrm{coh}}(X)$ 完全决定了 $X$ 的同构类。

这一惊人的结果表明，导出范畴编码了代数簇的**全部几何信息**——至少在某些情形下。

## 3. Fourier-Mukai变换：导出几何的积分演算

### 3.1 积分变换的范畴论语境

设 $X$ 和 $Y$ 为两个光滑射影簇。经典分析中的**积分变换**具有如下形式：

$$(\Phi_K f)(y) = \int_X K(x, y) f(x) \, dx$$

Mukai意识到，在导出范畴的框架中，**核（kernel）**$K$ 可以被替换为 $X \times Y$ 上的复形 $\mathcal{P}^{\bullet}$，积分则替换为**导出张量积和推出**：

**定义 3.1（Fourier-Mukai变换）**。设 $X, Y$ 为光滑射影簇，$\mathcal{P}^{\bullet} \in D^b_{\mathrm{coh}}(X \times Y)$。则**Fourier-Mukai变换**$\Phi_{\mathcal{P}^{\bullet}}: D^b_{\mathrm{coh}}(X) \to D^b_{\mathrm{coh}}(Y)$ 定义为：

$$\Phi_{\mathcal{P}^{\bullet}}(\mathcal{E}^{\bullet}) = \mathbf{R}p_{Y*}(\mathcal{P}^{\bullet} \otimes^{\mathbf{L}} p_X^*\mathcal{E}^{\bullet})$$

其中 $p_X: X \times Y \to X$ 和 $p_Y: X \times Y \to Y$ 为投影。

**定理 3.2（Mukai, 1981）**。设 $A$ 为Abel簇，$\hat{A}$ 为其对偶Abel簇，$\mathcal{P}$ 为Poincaré线丛。则Fourier-Mukai变换

$$\Phi_{\mathcal{P}}: D^b_{\mathrm{coh}}(A) \to D^b_{\mathrm{coh}}(\hat{A})$$

是**等价（equivalence）**，且 $\Phi_{\mathcal{P}} \circ \Phi_{\mathcal{P}^{\vee}[g]} \cong [-1]^*[-g]$，其中 $g = \dim A$。

*证明概要*：Mukai的证明利用了Abel簇的**群结构**和Poincaré丛的**泛性质**。关键在于证明：

1. $\Phi_{\mathcal{P}}$ 将 skyscraper sheaf 转化为平移不变的线丛。
2. 利用Parseval型恒等式证明完全忠实性。
3. 通过维度计算证明本质满性。

$\square$

### 3.2 完全忠实性与等价判据

Fourier-Mukai变换何时给出范畴等价？Bondal和Orlov给出了系统的判据：

**定理 3.3（Bondal–Orlov判据）**。Fourier-Mukai变换 $\Phi_{\mathcal{P}^{\bullet}}$ 是完全忠实的，当且仅当对所有 $x, y \in X$：

$$\operatorname{Hom}^i_{D^b(Y)}(\Phi(\mathcal{O}_x), \Phi(\mathcal{O}_y)) = \begin{cases} \mathbb{C} & i = 0, x = y \\ 0 & \text{otherwise} \end{cases}$$

若 furthermore $\Phi$ 将 $D^b_{\mathrm{coh}}(X)$ 的生成元映到 $D^b_{\mathrm{coh}}(Y)$ 的生成元，则 $\Phi$ 是等价。

### 3.3 在代数几何中的应用

Fourier-Mukai变换已成为现代代数几何的标配工具：

1. **K3曲面的Torelli定理**：Derived Torelli定理通过Fourier-Mukai等价刻画K3曲面的模空间。
2. **Birational Geometry**：Kawamata、Bridgeland等人利用导出等价研究flops和birational contractions。
3. **弦理论镜像对称**：Kontsevich的Homological Mirror Symmetry猜想预测，镜像对称对应于导出范畴的等价，而Fourier-Mukai变换是这类等价的主要候选。

## 4. 批判性比较：Grothendieck遗产的延续与超越

| 维度 | Grothendieck (导出范畴) | Mukai (FM变换) | Kontsevich (HMS) |
|------|----------------------|---------------|-----------------|
| 核心对象 | 三角范畴、导出函子 | 积分核、FM核 | $A_{\infty}$-范畴、Fukaya范畴 |
| 几何动机 | 上同调的函子性 | Abelian簇的对偶 | 弦理论的T-对偶 |
| 抽象层次 | 极高 | 高 | 极高 |
| 可计算性 | 弱 | 中等 | 弱 |
| 与现代物理的联系 | 间接 | 直接（弦论） | 直接（镜像对称） |
| 典型成果 | Tohoku、SGA 6 | Abelian簇对偶 | HMS猜想、稳定性条件 |

Grothendieck的遗产在于他开创了**用范畴论替代集合论**作为数学基础的思维方式。Mukai的贡献在于证明了这一思维方式在具体几何问题中的强大威力。Kontsevich则进一步将这一框架推广到辛几何和数学物理，形成了当代数学最活跃的前沿之一。

## 5. Lean4 形式化对照

本节展示导出范畴与Fourier-Mukai变换核心概念在 Lean4 / Mathlib4 中的形式化表达。

### 5.1 导出范畴与三角结构

```lean4
import Mathlib

-- 导出范畴在Mathlib中通过同伦范畴的局部化实现
variable (C : Type*) [Category C] [Abelian C]

-- 有界导出范畴
#check DerivedCategory C

-- 三角结构
#check Triangle (DerivedCategory C)

-- 上同调函子
#check cohomologyFunctor (DerivedCategory C) 0
```

### 5.2 Fourier-Mukai变换的形式化

```lean4
import Mathlib

-- 概形的导出范畴
variable (X Y : Scheme) [IsSmooth ℂ X] [IsSmooth ℂ Y] [Projective X] [Projective Y]

-- 对象在导出范畴中的态射
variable (P : DerivedCategory (CohSheaf X × Y))

-- Fourier-Mukai变换通过导出推出和张量积实现
-- 在Mathlib中，这需要通过具象的层操作组合实现
example (E : DerivedCategory (CohSheaf X)) :
    DerivedCategory (CohSheaf Y) := by
  sorry
```

## 6. 结论

从Grothendieck的导出范畴到Mukai的Fourier-Mukai变换，再到Kontsevich的同调镜像对称，一条清晰的演进脉络展现了抽象数学思想的持久生命力。Grothendieck在1950年代开创的范畴论框架，在1980年代被Mukai转化为具体的几何工具，在1990年代又被Kontsevich推广到数学物理的前沿。

这一发展历程验证了Grothendieck的深刻信念：正确的抽象层次能够揭示隐藏在所有具体现象背后的统一结构。导出范畴不仅是一个技术工具，更是一种**数学世界观**——在这种世界观中，对象的关系比对象本身更重要，函子性比构造性更基本，而等价性比同构性更自然。

---

**参考文献**

1. Grothendieck, A. "Sur quelques points d'algèbre homologique." *Tôhoku Math. J.* 9 (1957), 119–221.
2. Verdier, J-L. "Des catégories dérivées des catégories abéliennes." *Astérisque* 239, 1996.
3. Mukai, S. "Duality between $D(X)$ and $D(\hat{X})$ with its application to Picard sheaves." *Nagoya Math. J.* 81 (1981), 153–175.
4. Huybrechts, D. *Fourier-Mukai Transforms in Algebraic Geometry*. Oxford, 2006.
5. Bondal, A. & Orlov, D. "Reconstruction of a variety from the derived category and groups of autoequivalences." *Compositio Math.* 125 (2001), 327–344.
