---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Jordan 曲线定理 (Jordan Curve Theorem)
---
# Jordan 曲线定理 (Jordan Curve Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Homotopy.Sphere
import Mathlib.Topology.Connected

namespace JordanCurveTheorem

variable {γ : Circle → EuclideanSpace ℝ (Fin 2)} (hγ : Continuous γ) (hinj : Function.Injective γ)

/-- Jordan 曲线定理：平面简单闭曲线将平面分成两个连通分支 -/
theorem jordan_curve_theorem :
    (EuclideanSpace ℝ (Fin 2) \ Set.range γ).ConnectedComponents = 2 := by
  -- 基于平面同调或 Alexander 对偶的拓扑证明
  sorry

/-- 有界和无界分支 -/
theorem jordan_curve_components (hC : Set.range γ = frontier C) (hCopen : IsOpen C) :
    (IsBounded C ∧ (EuclideanSpace ℝ (Fin 2) \ closure C).Unbounded) ∨
    (IsBounded (EuclideanSpace ℝ (Fin 2) \ closure C) ∧ C.Unbounded) := by
  -- 应用曲线定理
  sorry

end JordanCurveTheorem
```

## 数学背景

Jordan 曲线定理是拓扑学中最基本和最直观的结果之一，由法国数学家卡米尔·若尔当（Camille Jordan）于1887年首次发表严格证明。该定理断言：平面上任何一条简单闭曲线（即不自交的连续闭曲线）都将平面分割为恰好两个连通分支——一个内部（有界）和一个外部（无界）。尽管这一结论在直观上极为显然（例如，圆将平面分为内部和外部），但其严格证明却需要深刻的拓扑工具，是代数拓扑和分析拓扑发展的重要动力。现代证明通常借助于同调论或 Alexander 对偶。

## 直观解释

Jordan 曲线定理告诉我们：**在平面上画一条不打结的闭合曲线（可以极其复杂和扭曲），它总会把平面分成"里面"和"外面"两个区域**。

想象在平面上用铅笔画了一个闭合的圈，无论这个圈是完美的圆、歪歪扭扭的土豆形状，还是像海岸线一样极其复杂的曲线，只要它不自交，就总是存在一个明确的"内部"和一个明确的"外部"。从外部走到内部，你必须至少穿过曲线一次；而且不存在一条连续路径能从内部绕到外部而不穿过曲线。这个看似显然的定理在数学上却出奇地难以严格证明，尤其当曲线是高度分形、没有切线的病态曲线时。

## 形式化表述

设 $\\gamma: S^1 \\to \\mathbb{R}^2$ 是连续的单射（即简单闭曲线），$C = \\gamma(S^1)$ 为其像集。则补集 $\\mathbb{R}^2 \\setminus C$ 恰有两个道路连通分支：

1. **内部**（Interior）：有界连通分支 $U_{\\text{int}}$
2. **外部**（Exterior）：无界连通分支 $U_{\\text{ext}}$

且 $C$ 是这两个分支的共同边界：

$$\\partial U_{\\text{int}} = \\partial U_{\\text{ext}} = C$$

### 推广：Jordan-Schoenflies 定理

进一步，存在 $\\mathbb{R}^2$ 到自身的同胚映射，将给定简单闭曲线映射为单位圆。这意味着内部同胚于开单位圆盘，外部同胚于 $\\mathbb{R}^2 \\setminus \\overline{B(0, 1)}$。

## 证明思路

### 同调论证明（现代标准方法）：

1. **Alexander 对偶**：对 $\\mathbb{R}^2$ 中的紧致子集 $C$，有：
   $$\\tilde{H}_0(\\mathbb{R}^2 \\setminus C) \\cong \\check{H}^1(C)$$
2. **简单闭曲线的上同调**：由于 $C \\cong S^1$，故 $\\check{H}^1(C) \\cong \\mathbb{Z}$
3. **约化同调的解读**：$\\tilde{H}_0(\\mathbb{R}^2 \\setminus C) \\cong \\mathbb{Z}$ 意味着 $\\mathbb{R}^2 \\setminus C$ 恰有两个道路连通分支
4. **有界性分析**：利用 $C$ 的紧致性，一个分支包含于某个大圆盘内（有界），另一个分支延伸至无穷远（无界）

### 初等拓扑证明（Maehara, 1984）：

基于 Tietze 扩张定理和 Brouwer 不动点定理，可以构造一个不依赖于代数拓扑的相对初等的证明。

## 示例

### 示例 1：单位圆

单位圆 $S^1 = \\{(x, y) : x^2 + y^2 = 1\\}$ 将平面分为：
- 内部：$x^2 + y^2 < 1$（有界开单位圆盘）
- 外部：$x^2 + y^2 > 1$（无界区域）

这是 Jordan 曲线定理最简单、最直观的例子。

### 示例 2：科赫雪花曲线

科赫雪花是一条连续、处处不可微、长度无穷的简单闭曲线。尽管其几何性质极为复杂，Jordan 曲线定理仍然保证它有一个明确的有界内部和一个无界外部。

### 示例 3：计算几何中的点在多边形内判定

给定一个简单多边形（顶点的闭折线），判断一个点是否在多边形内部。Jordan 曲线定理保证了"内部"和"外部"是良定义的，因此射线投射算法（如 even-odd rule）在数学上有坚实的基础。

## 应用

- **计算几何**：点在多边形内判定、平面区域三角剖分
- **图像处理**：轮廓提取和区域分割
- **复分析**：单连通区域和柯西积分定理的应用
- **计算机图形学**：二维建模和碰撞检测
- **地理信息系统（GIS）**：边界识别和空间分析

## 相关概念

- 简单闭曲线 (Simple Closed Curve)：连续且不自交的闭曲线，同胚于 $S^1$
- [Brouwer 不动点定理 (Brouwer Fixed-Point Theorem)](./brouwer-fixed-point-theorem.md)：Jordan 曲线定理某些初等证明的关键工具
- Alexander 对偶 (Alexander Duality)：连接空间与其补集同调群的定理
- 单连通区域 (Simply Connected Region)：Jordan 曲线内部的标准性质
- [Jordan-Schoenflies 定理](./jordan-curve-theorem.md)：Jordan 曲线定理的更强形式

## 参考

### 教材

- [Munkres. Topology. Pearson, 2nd edition, 2000. Section 63]
- [Hatcher. Algebraic Topology. Cambridge, 2002. Section 2.B]

### 历史文献

- [Jordan. Cours d'analyse de l'École Polytechnique. 1887]
- [Maehara. The Jordan curve theorem via the Brouwer fixed point theorem. AMM, 1984]

### 在线资源

- [Mathlib4 文档 - Homotopy.Sphere][https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Homotopy/Sphere.html]
- [Hales. The Jordan curve theorem, formally and informally. AMM, 2007]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
