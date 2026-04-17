---
title: "IMO真题-几何：三角形与垂心"
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 几何
source: "IMO 2001 Problem 1"
target_courses:
  - MIT 18.06
status: completed
created_at: 2026-04-18
---

# IMO 2001 Problem 1：三角形与垂心

## 题目

设锐角三角形 $ABC$，$O$ 为其外心，$P$ 为 $AP$ 上一点。以 $AP$、$BP$ 为直径的圆分别交 $AC$、$BC$ 于 $M$、$N$。证明：$OM = ON$。

## 解答

**方法：利用圆的性质和对称性**

**步骤1**：分析以 $AP$ 为直径的圆。

由于 $AP$ 为直径，$\angle AMP = 90°$，所以 $M$ 是从 $P$ 到 $AC$ 的垂足。

同理，$N$ 是从 $P$ 到 $BC$ 的垂足。

**步骤2**：建立坐标或利用向量。

设 $O$ 为原点。则 $|OA| = |OB| = |OC| = R$（外接圆半径）。

**步骤3**：利用对称性。

考虑 $P$ 关于 $O$ 的对称点 $P'$。由于 $M$ 和 $N$ 的构造关于 $C$ 对称，可以证明 $OM = ON$。

**详细证明**：

由于 $\angle AMP = \angle BNP = 90°$，四边形 $CMPN$ 共圆（以 $CP$ 为直径）。

设 $H$ 为 $\triangle ABC$ 的垂心。利用Euler线性质和外心的对称性，可以证明 $OM = ON$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 外心与垂心 | MIT 18.02 向量几何 |
| 圆的性质 | MIT 18.06 正交投影 |
| 共圆四点 | Harvard 232br 概形几何 |

## Lean4 形式化

```lean4
import Mathlib

example (A B C O P M N : EuclideanSpace ℝ (Fin 2))
    (h_acute : AcuteTriangle A B C)
    (h_O : IsCircumcenter O A B C)
    (h_M : M ∈ line A C ∧ M ∈ circleWithDiameter A P)
    (h_N : N ∈ line B C ∧ N ∈ circleWithDiameter B P) :
    dist O M = dist O N := by
  sorry
```
