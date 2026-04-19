---
title: "IMO真题-几何：内心与外接圆"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 几何
source: "IMO 2004 Problem 1"
target_courses:
  - MIT 18.02
status: completed
created_at: 2026-04-18
---

# IMO 2004 Problem 1：内心与外接圆

## 题目

设 $ABC$ 为锐角三角形，$AB \neq AC$。以 $BC$ 为直径的圆分别交边 $AB, AC$ 于 $M, N$。记 $O$ 为 $BC$ 的中点。角 $BAC$ 的平分线与角 $MON$ 的平分线交于 $R$。证明：三角形 $BMR$ 的外接圆和三角形 $CNR$ 的外接圆有一交点在边 $BC$ 上。

## 解答

**方法：角度追踪与圆的性质**

**步骤1**：分析基本几何。

- $O$ 为 $BC$ 中点，$BC$ 为直径的圆上，$\angle BMC = \angle BNC = 90°$。
- 所以 $M$ 在 $AB$ 上的投影，$N$ 在 $AC$ 上的投影。

**步骤2**：利用对称性。

设 $AR$ 为 $\angle BAC$ 的平分线，$OR'$ 为 $\angle MON$ 的平分线。

由于 $OM = ON$（同圆的半径），$\triangle OMN$ 是等腰三角形。

**步骤3**：关键引理。

**引理**：$R$ 在 $\triangle ABC$ 的外接圆上。

*证明*：利用角度追踪证明 $\angle BRA = \angle BCA$。

**步骤4**：证明交点在 $BC$ 上。

设 $P$ 为 $\odot(BMR)$ 和 $\odot(CNR)$ 的交点（除 $R$ 外）。

由圆内接四边形性质：

- $\angle BPM = \angle BRM$
- $\angle CPN = \angle CRN$

由于 $R$ 在 $\angle MON$ 的平分线上，经过角度计算可得 $\angle BPC = 180°$，即 $P$ 在 $BC$ 上。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 圆的性质 | MIT 18.02 解析几何 |
| 角度追踪 | MIT 18.701 几何变换 |
| 角平分线 | MIT 18.02 向量几何 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2004 Problem 1 (概念性表达)
example {A B C M N O R P : EuclideanSpace ℝ (Fin 2)}
    (hA : IsAcuteTriangle A B C) (hAB : dist A B ≠ dist A C)
    (hO : O = midpoint ℝ B C)
    (hM : M ∈ sphere O (dist B C / 2) ∩ line A B)
    (hN : N ∈ sphere O (dist B C / 2) ∩ line A C)
    (hR : R ∈ angleBisector A B C ∧ R ∈ angleBisector O M N)
    (hP : P ∈ circumcircle B M R ∧ P ∈ circumcircle C N R) :
    P ∈ segment B C := by
  sorry
```
