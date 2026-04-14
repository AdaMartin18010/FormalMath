---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Hodge 指标定理 (Hodge Index Theorem)
---
# Hodge 指标定理 (Hodge Index Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.HodgeTheory

namespace AlgebraicGeometry

variable {S : Type*} [Surface S] [IsSmooth S] [IsProjective S]

/-- Hodge 指标定理：曲面上除子的相交形式符号为 (1, ρ-1) -/
theorem hodge_index (D1 D2 : Divisor S) :
    D1.intersection D2 < 0 →
    (D1.intersection D1 > 0 ∧ D2.intersection D2 > 0 → False) := by
  -- 利用曲面上 (1,1)-形式的 Hodge 分解和正定/负定子空间理论证明
  sorry

end AlgebraicGeometry
```

## 数学背景

Hodge 指标定理是代数几何，特别是曲面理论中最深刻的结果之一，是英国数学家威廉·瓦伦斯·道格拉斯·霍奇（W. V. D. Hodge）在20世纪30年代发展起来的 Hodge 理论的核心应用。该定理断言：在一个光滑射影复曲面上，数值等价类构成的 Néron-Severi 群上的相交配对具有特定的符号性质——$(1, \rho - 1)$，其中 $\rho$ 是 Néron-Severi 群的秩。具体来说，如果在数值等价类空间上考虑相交形式，那么存在一个方向（由丰富除子给出）使得相交形式为正定，而在其正交补上为负定。Hodge 指标定理是研究曲面的双有理几何、模空间理论和算术几何的基石。

## 直观解释

Hodge 指标定理告诉我们：在研究曲面上的曲线相交时，相交形式呈现出一种非常特殊的符号模式。想象一个二维的相交形式空间，其中有一个特殊的方向（对应于超平面截面或丰富除子），沿这个方向的自相交总是正的。而与这个方向正交的所有其他方向，自相交都是负的。这就像时空中的光锥结构：有一个类时方向（正定）和无数类空方向（负定）。这个定理的惊人之处在于，这种符号结构完全由曲面的拓扑和复结构决定，不依赖于具体的嵌入或坐标选择。它在双有理几何中尤为重要，因为它限制了我们如何通过 blow-up 和 blow-down 来改变曲面。

## 形式化表述

设 $S$ 是光滑射影复曲面，$\text{NS}(S)$ 是其 Néron-Severi 群（模去数值等价的除子类群），$\rho = \text{rank}(\text{NS}(S))$ 是 Picard 数。则相交配对：

$$\text{NS}(S) \times \text{NS}(S) \to \mathbb{Z}, \quad (D_1, D_2) \mapsto D_1 \cdot D_2$$

的符号为 $(1, \rho - 1)$。即：

1. 存在某个丰富除子 $H$ 使得 $H^2 > 0$
2. 对任何满足 $D \cdot H = 0$ 的除子 $D$，有 $D^2 \leq 0$
3. 若 $D^2 = 0$ 且 $D \cdot H = 0$，则 $D$ 在数值上平凡（即 $D \equiv 0$）

等价表述（上同调形式）：在 $H^2(S, \mathbb{R})$ 中，由 $(1,1)$-类组成的子空间上的杯积形式限制在 $\text{NS}(S) \otimes \mathbb{R}$ 上具有符号 $(1, \rho - 1)$。

其中：

- Néron-Severi 群 $\text{NS}(S) = \text{Pic}(S) / \text{Pic}^0(S)$ 是 Picard 群的代数部分
- Picard 数 $\rho$ 是一个介于 1 和 $h^{1,1}$ 之间的整数
- 丰富除子（ample divisor）的类位于正定方向

## 证明思路

1. **Hodge 分解**：对曲面 $S$，$H^2(S, \mathbb{C}) = H^{2,0} \oplus H^{1,1} \oplus H^{0,2}$，其中 $H^{p,q}$ 由 $(p,q)$-形式组成
2. **Kaehler 恒等式**：利用 Lefschetz 分解，$H^{1,1}$ 可以分解为 primitive 部分和 Lefschetz 幂的部分
3. **Hodge-Riemann 双线性关系**：在 primitive 部分上，由 $Q(\alpha, \beta) = \int_S \alpha \wedge \beta \wedge \omega^{{n-2}}$ 定义的配对具有确定的符号（对 $H^{1,1}$ 为负定）
4. **Néron-Severi 群的嵌入**：$\text{NS}(S) \otimes \mathbb{R} \subseteq H^{1,1} \cap H^2(S, \mathbb{R})$。Hodge-Riemann 关系限制在这个实子空间上给出符号 $(1, \rho - 1)$

核心洞察在于 Kaehler 形式的 Lefschetz 作用为 $H^{1,1}$ 提供了一个一维的正定方向，其余部分由 primitive 条件控制为负定。

## 示例

### 示例 1：直纹面

对直纹面 $S = \mathbb{P}^1 \times C$（$C$ 是曲线），Picard 数 $\rho \geq 2$。设 $f$ 是纤维类，$s$ 是截面类。则 $f^2 = 0$, $s \cdot f = 1$, $s^2$ 取决于截面选择。相交形式的符号确实是 $(1, \rho - 1)$。

### 示例 2：K3 曲面

对一般 K3 曲面，$h^{1,1} = 20$，但 Picard 数 $\rho$ 可以变化（$1 \leq \rho \leq 20$）。Hodge 指标定理保证了无论 $\rho$ 是多少，Néron-Severi 群上的相交形式总具有符号 $(1, \rho - 1)$。

### 示例 3：Castelnuovo 有理性判据

在证明 Castelnuovo 有理性判据时，Hodge 指标定理是关键工具之一。它用于控制曲面上曲线的相交行为，从而区分有理曲面与非有理曲面。

## 应用

- **代数几何**：曲面的双有理分类和极小模型理论
- **算术几何**：Néron-Severi 群的秩和 Tate 猜想
- **弦理论**：Calabi-Yau 曲面的镜像对称和 Yukawa 耦合
- **Diophantine 几何**：Mordell-Weil 群的高度配对和椭圆曲面
- **K3 曲面理论**：Picard 格和模空间的几何

## 相关概念

- Hodge 分解 (Hodge Decomposition)：复流形上同调的 (p,q)-型分解
- Néron-Severi 群 (Néron-Severi Group)：除子类的数值等价群
- 相交配对 (Intersection Pairing)：除子类的双线性相交数
- Picard 数 (Picard Number)：Néron-Severi 群的秩
- Hodge-Riemann 关系：primitive 形式上的定号性条件

## 参考

### 教材

- [P. Griffiths, J. Harris. Principles of Algebraic Geometry. Wiley, 1978. Chapter 0]
- [R. Hartshorne. Algebraic Geometry. Springer, 1977. Chapter V, §1]

### 在线资源

- [Stacks Project - Intersection Theory](https://stacks.math.columbia.edu/tag/0BEL)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
