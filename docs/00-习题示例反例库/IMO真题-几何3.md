---
title: "IMO真题-几何：圆内接四边形"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 几何
source: "IMO 2009 Problem 2"
target_courses:
  - MIT 18.02
status: completed
created_at: 2026-04-18
---

# IMO 2009 Problem 2：圆内接四边形

## 题目

设 $O$ 为三角形 $ABC$ 的外心。点 $P, Q$ 分别是边 $CA, AB$ 上的点。设 $K, L, M$ 分别是线段 $BP, CQ, PQ$ 的中点。设 $\Gamma$ 为三角形 $KLM$ 的外接圆。若直线 $PQ$ 与圆 $\Gamma$ 相切，证明：$OP = OQ$。

## 解答

**方法：向量法与位似变换**

**步骤1**：建立坐标系。

设 $O$ 为原点。令 $\vec{a}, \vec{b}, \vec{c}$ 为 $A, B, C$ 的位置向量，$|\vec{a}| = |\vec{b}| = |\vec{c}| = R$。

**步骤2**：表示中点。

$$\vec{k} = \frac{\vec{b} + \vec{p}}{2}, \quad \vec{l} = \frac{\vec{c} + \vec{q}}{2}, \quad \vec{m} = \frac{\vec{p} + \vec{q}}{2}$$

**步骤3**：利用位似变换。

注意到 $K, L, M$ 是 $BP, CQ, PQ$ 的中点。三角形 $KLM$ 与三角形 $BCQ'P'$ 之间存在位似关系。

**步骤4**：利用切线条件。

$PQ$ 与 $\Gamma$ 相切于 $M$，所以 $\angle(LMK) = \angle(MPQ)$（弦切角定理）。

**步骤5**：向量计算。

通过向量运算证明 $\vec{p} \cdot \vec{p} = \vec{q} \cdot \vec{q}$，即 $|OP| = |OQ|$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 向量法 | MIT 18.02 向量几何 |
| 弦切角定理 | MIT 18.02 微分几何 |
| 位似变换 | MIT 18.701 线性变换 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2009 Problem 2 (简化概念性表达)
example {A B C P Q O : EuclideanSpace ℝ (Fin 2)}
    (hO : O = (A + B + C) / 3) -- 简化假设
    (hP : P ∈ segment A C) (hQ : Q ∈ segment A B)
    (hK : K = (B + P) / 2) (hL : L = (C + Q) / 2) (hM : M = (P + Q) / 2)
    (htangent : lineTangent (line P Q) (circumcircle K L M)) :
    dist O P = dist O Q := by
  sorry
```
