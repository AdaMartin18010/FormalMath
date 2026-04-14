---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 爆破奇点消解 (Blow-up Resolution of Singularities)
---
# 爆破奇点消解 (Blow-up Resolution of Singularities)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Blowup

namespace BlowUpResolution

-- 注：Mathlib4 中 Scheme 与 ProjectiveSpectrum 的基础理论已有形式化，
-- 但一般簇的奇点消解（Resolution of Singularities）
-- 以及一般的爆破（Blow-up）在 Mathlib4 中的完整形式化
-- 目前仍在发展中。以下给出标准的代数几何表述框架。

variable {X : Scheme} {Z : ClosedImmersion X}

/-- 标准爆破构造的泛性质 -/
def blowup (Z : ClosedImmersion X) : Scheme :=
  ProjectiveSpectrum (ReesAlgebra Z.ideal)

/-- 奇点消解：对代数簇 X，存在光滑簇 Y 和正常态射 π: Y → X
    使得 π 在光滑点上是同构 -/
theorem resolution_of_singularities {X : Scheme} [IsIntegral X] [IsOfFiniteType X]
    [CharZero (Γ X ⊤)] :
    ∃ (Y : Scheme) (π : Y ⟶ X),
      IsSmooth Y ∧ IsProper π ∧
      IsIsomorphism (π.restrict (X \ Z.singularLocus)) := by
  -- Hironaka 定理（特征零）目前在 Mathlib4 中尚未完整形式化。
  sorry

end BlowUpResolution
```

## 数学背景

奇点消解（Resolution of Singularities）是代数几何中的核心问题，旨在将一个带有奇点的代数簇转化为一个光滑簇，同时保持尽可能多的几何信息。爆破（Blow-up）是实现奇点消解的最基本和最重要的几何手术：通过将一个子簇（通常是一个点或光滑子簇）替换为其法丛的射影化，从而“展开”奇点。Heisuke Hironaka 在1964年证明了特征零域上代数簇的奇点消解存在性，并因此获得1970年菲尔兹奖。这一定理不仅在代数几何中具有根本意义，在算术几何、表示论和弦理论中也有广泛应用。

## 直观解释

**爆破**就像是把一张纸上的一个褶皱点展开成一个小圆盘：原本所有方向都挤在一个点上的曲线，在爆破后被“拉开”，变成一个光滑的圆柱面。想象用放大镜观察一个自交点（如“8”字形曲线的交叉点），爆破相当于把这个交叉点放大成一个圆周，原来相交的两条分支现在分别与这个圆周相交于不同的点，从而消除了自交。

**奇点消解**则是通过一系列这样的爆破手术，逐步“熨平”簇上的所有奇点，最终得到一个光滑簇。每一次爆破都减少了某种奇点复杂度的度量（如 Hironaka 的 invariant），保证过程在有限步内终止。

## 形式化表述

设 $X$ 为代数闭域 $k$ 上的拟射影簇（或更一般的概型），$Z \subseteq X$ 为闭子簇。

**爆破（Blow-up）**：$X$ 沿 $Z$ 的爆破是一个概型 $Bl_Z(X)$ 和一个固有态射 $\pi: Bl_Z(X) \to X$，满足：

1. $\pi$ 在 $X \setminus Z$ 上是同构
2. 例外除子 $E = \pi^{-1}(Z)$ 是 $Bl_Z(X)$ 中的 Cartier 除子
3. 爆破具有泛性质：对任意态射 $f: Y \to X$ 使得 $f^{-1}(Z)$ 为 Cartier 除子，存在唯一的 $g: Y \to Bl_Z(X)$ 使得 $f = \pi \circ g$

**奇点消解（Hironaka 定理，特征零）**：设 $X$ 为特征零的整概型且局部有限型，则存在光滑概型 $Y$ 和一个正常（proper）双有理态射 $\pi: Y \to X$，使得 $\pi$ 在 $X$ 的光滑点集上是同构。

## 证明思路

**Hironaka 定理的核心步骤**：
1. **局部化**：将问题约化为仿射簇上的局部问题
2. **不变量系统**：定义一个关于奇点的良序不变量系统（如 Hilbert-Samuel 函数、不变量序列 $\nu_1, \nu_2, \ldots$）
3. **最大轨迹爆破**：在每次迭代中，找出不变量最大的奇点子集（maximum stratum），沿其光滑中心进行爆破
4. **不变量严格下降**：证明每次爆破后，最大奇点的不变量严格下降
5. **终止性**：由于不变量系统良序，过程必在有限步后终止，得到光滑簇

核心洞察在于爆破不仅是几何手术，更是一种精细的“归纳法”工具。

## 示例

### 示例 1：尖点曲线的爆破

考虑仿射平面曲线 $C: y^2 = x^3$（尖点三次曲线），在原点有尖点奇点。对 $\mathbb{A}^2$ 在原点爆破后，在爆破图的一个坐标卡中 $x = u, y = uv$，曲线的严格变换（strict transform）为：

$$u^2 v^2 = u^3 \implies v^2 = u$$

这是抛物线，光滑！因此一次爆破就消解了尖点。

### 示例 2：结点曲线的爆破

考虑 $C: y^2 = x^3 + x^2$（结点三次曲线），在原点有结点（node）。对原点爆破后，严格变换变为：

$$v^2 = u + 1$$

这也是光滑曲线。原结点的两个分支现在分别与例外除子交于不同点。

### 示例 3：Whitney 伞的爆破

Whitney 伞是三维仿射空间中的曲面 $x^2 = y^2 z$。它的奇点集是一条直线（伞柄），且伞柄上有一个更严重的奇点（伞顶）。对这个曲面进行奇点消解通常需要多次爆破。

## 应用

- **双有理几何**：极小模型纲领（MMP）与翻转、flop 操作
- **弦理论与镜像对称**：Calabi-Yau 流形的奇点消解与拓扑变化
- **算术几何**：$p$-adic 积分、Igusa 局部 zeta 函数
- **表示论**：Springer 消解与旗簇上的几何表示论
- **计算代数几何**：奇点消解算法（Villamayor、Bierstone-Milman 算法）

## 相关概念

- 爆破 (Blow-up)：沿子簇进行的几何手术
- 严格变换 (Strict Transform)：原簇在爆破下的真变换
- 例外除子 (Exceptional Divisor)：爆破中心的原像
- 双有理态射 (Birational Morphism)：诱导函数域同构的态射
- Cartier 除子 (Cartier Divisor)：局部由单个方程定义的除子

## 参考

### 教材

- [Hartshorne. Algebraic Geometry. Springer, 1977. Chapter II, Section 7]
- [Kollár. Lectures on Resolution of Singularities. AMS, 2007]

### 历史文献

- [Hironaka. Resolution of Singularities of an Algebraic Variety Over a Field of Characteristic Zero. Annals of Math., 1964]

### 在线资源

- [Mathlib4 文档 - AlgebraicGeometry][https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry.html]
- **注意**：Mathlib4 中一般爆破与奇点消解的完整形式化目前仍在发展中。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
