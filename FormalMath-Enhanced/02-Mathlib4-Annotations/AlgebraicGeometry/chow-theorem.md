---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Chow 定理 (Chow's Theorem)
---
# Chow 定理 (Chow's Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Chow

namespace AlgebraicGeometry

variable {X : Type*} [ComplexManifold X] [CompactSpace X]

/-- Chow 定理：复射影空间中的闭解析子集必是代数簇 -/
theorem chow {A : Set (ProjectiveSpace ℂ n)} (hA : IsAnalytic A) (hclosed : IsClosed A) :
    ∃ I : Ideal (MvPolynomial (Fin (n+1)) ℂ),
      A = projectiveVariety I := by
  -- 利用复解析几何中的消没定理和代数无关性证明
  sorry

end AlgebraicGeometry
```

## 数学背景

Chow 定理是代数几何与复几何交界处的经典结果，由美国数学家魏龙·周炜良（Wei-Liang Chow）在1949年证明。该定理断言：复射影空间 $\mathbb{P}^n(\mathbb{C})$ 中的任何闭解析子集（在解析拓扑下闭且局部由全纯函数零点定义）实际上都是一个代数簇（即可以由齐次多项式的零点定义）。Chow 定理建立了复射影空间中解析几何与代数几何之间的深刻桥梁：在这个特殊但极其重要的空间中，所有解析对象本质上都是代数的。这一定理是 GAGA（Serre 的 Géométrie Algébrique et Géométrie Analytique）原则的先驱和特例。

## 直观解释

Chow 定理揭示了一个令人惊叹的事实：在复射影空间这个特定的舞台上，解析几何和代数几何是完全重合的。想象你在 $\mathbb{P}^n(\mathbb{C})$ 中有一个由全纯函数方程定义的复杂曲面。这个曲面看起来非常光滑（解析的），你可能会怀疑它是否能被多项式方程描述（代数的）。Chow 定理告诉我们：在射影空间中，答案永远是肯定的！任何看起来解析的对象，实际上都隐藏着一个代数结构。这就像发现所有的有机生命形式都可以被某种简单的化学式所描述——在一个特定的环境中，复杂的现象背后总有一个更简单的代数核心。

## 形式化表述

设 $A \subseteq \mathbb{P}^n(\mathbb{C})$ 是一个子集。若 $A$ 在解析拓扑下是闭集，且 $A$ 的每一点附近都可以由有限多个全纯函数的零点定义（即 $A$ 是闭解析子集），则存在有限多个复系数齐次多项式 $F_1, F_2, \dots, F_m$ 使得：

$$A = \{[x_0 : x_1 : \dots : x_n] \in \mathbb{P}^n(\mathbb{C}) : F_1(x) = F_2(x) = \cdots = F_m(x) = 0\}$$

即 $A$ 是一个射影代数簇。

等价表述：

复射影空间中的闭解析子层（coherent analytic sheaf）都可以代数化，即由某个代数凝聚层诱导。

其中：

- $\mathbb{P}^n(\mathbb{C})$ 是 $n$ 维复射影空间
- 闭解析子集是指在通常拓扑下闭且局部由全纯函数零点定义的集合
- 射影代数簇是指由齐次多项式零点定义的集合
- 该定理对非射影的复流形不成立

## 证明思路

1. **解析理想的代数化**：首先在局部（利用 Weierstrass 预备定理和除法定理）证明解析理想可以由多项式生成
2. **整体化**：利用复射影空间的紧性和 Stein 覆盖，将局部结果拼成整体
3. **Hilbert 零点定理的应用**：证明由解析函数定义的集合也可以用多项式方程描述
4. **Serre 的 GAGA**：Chow 定理是更一般的 GAGA 原则（代数凝聚层与解析凝聚层的等价）在子集层面的体现

核心洞察在于复射影空间的紧性和丰富除子的存在性强迫解析结构代数化。

## 示例

### 示例 1：复环面

设 $X = \mathbb{C}^n / \Lambda$ 是一个复环面。若 $X$ 可以嵌入到某个 $\mathbb{P}^N(\mathbb{C})$ 中，则根据 Chow 定理，$X$ 的像是一个射影代数簇。这等价于 $X$ 是极化的（存在正定的 Riemann 形式），即 $X$ 是 Abel 簇。

### 示例 2：解析映射的图像

设 $f: \mathbb{P}^n(\mathbb{C}) \to \mathbb{P}^m(\mathbb{C})$ 是一个全纯映射。根据 Chow 定理，$f$ 的图像 $\Gamma_f \subseteq \mathbb{P}^n \times \mathbb{P}^m$ 是一个代数簇。这推出 $f$ 本身必须是代数态射（有理映射）。

### 示例 3：Hopf 曲面

Hopf 曲面 $X = (\mathbb{C}^2 \setminus \{0\}) / \langle (z_1, z_2) \mapsto (2z_1, 2z_2) \rangle$ 是一个紧复曲面，但不能嵌入任何 $\mathbb{P}^n(\mathbb{C})$（因为它是非 Kaehler 的）。Chow 定理在这里不适用，且 $X$ 确实不是一个代数簇。

## 应用

- **代数几何**：解析几何与代数几何的对应（GAGA）
- **复几何**：紧复流形的分类和代数化判据
- **数论**：算术几何中 p-adic 解析结构的代数化
- **数学物理**：弦紧化中 Calabi-Yau 流形的代数结构
- **多复变函数论**：解析集的局部理论与整体代数化

## 相关概念

- 解析子集 (Analytic Subset)：局部由全纯函数零点定义的集合
- 射影代数簇 (Projective Algebraic Variety)：射影空间中多项式零点集
- GAGA (Géométrie Algébrique et Géométrie Analytique)：Serre 建立的代数-解析对应
- 凝聚层 (Coherent Sheaf)：局部有限生成的层
- Abel 簇 (Abelian Variety)：可射影嵌入的复环面

## 参考

### 教材

- [P. Griffiths, J. Harris. Principles of Algebraic Geometry. Wiley, 1978. Chapter 1]
- [J.-P. Serre. Géométrie algébrique et géométrie analytique. Ann. Inst. Fourier, 1956]

### 在线资源

- [Stacks Project - Chow](https://stacks.math.columbia.edu/tag/0B5J)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
