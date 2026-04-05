---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 闭图像定理 (Closed Graph Theorem)
---
# 闭图像定理 (Closed Graph Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Topology.Graph

namespace ClosedGraphTheorem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- 闭图像定理 -/
theorem closed_graph {T : E → F} (hT : LinearMap ℝ E F T)
    (hclosed : IsClosed {p : E × F | p.2 = T p.1}) :
    Continuous T := by
  -- 图像到E的投影是同胚
  let G := {p : E × F | p.2 = T p.1}
  have hproj : IsHomeomorph (fun (p : G) => p.1.1) := by
    sorry
  -- T是投影的复合
  sorry

end ClosedGraphTheorem
```

## 数学背景

闭图像定理是泛函分析中与开映射定理对偶的重要结果，由Stefan Banach证明。它表明，对于Banach空间之间的线性算子，闭图像蕴含连续性。这是证明微分算子等无界算子闭延拓存在性的关键工具。与开映射定理不同，闭图像定理不需要满射性假设。

## 直观解释

闭图像定理告诉我们：**如果线性算子的图像是"好"的（闭的），那么算子本身也是"好"的（连续的）**。

对于闭算子，我们可以在图像空间（也是Banach空间）上工作，利用投影的连续性得到原算子的连续性。

## 形式化表述

设 $T: E \to F$ 是Banach空间之间的线性算子，$\text{graph}(T) = \{(x, Tx)\}$。

若 $\text{graph}(T)$ 在 $E \times F$ 中闭，则 $T$ 有界（连续）。

## 应用

- 微分算子的闭延拓
- 非交换几何
- 偏微分方程的弱解理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
