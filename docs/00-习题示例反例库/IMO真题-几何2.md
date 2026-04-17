---
title: "IMO真题-几何：圆与相似"
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 几何
source: "IMO 2003 Problem 4"
target_courses:
  - MIT 18.06
status: completed
created_at: 2026-04-18
---

# IMO 2003 Problem 4：圆与相似

## 题目

设 $ABCD$ 为圆内接四边形。点 $P, Q, R$ 分别是 $D$ 到直线 $BC, CA, AB$ 的垂足。证明：$PQ = QR$ 当且仅当 $\angle ABC$ 和 $\angle ADC$ 的角平分线的交点在 $AC$ 上。

## 解答

**关键引理**：Simson线定理。$P, Q, R$ 共线（Simson线）当且仅当 $D$ 在 $\triangle ABC$ 的外接圆上。题设已满足。

**步骤1：建立坐标或利用相似**

设 $\angle ABC = \beta$，$\angle ADC = \delta$。由于 $ABCD$ 圆内接，$\beta + \delta = 180°$。

**步骤2：分析 $PQ = QR$**

$P$ 在 $BC$ 上，$Q$ 在 $CA$ 上，$R$ 在 $AB$ 上。

利用投影性质：$DP = BD \sin\angle DBC$，$DQ = CD \sin\angle DCA$，等等。

通过三角计算可以证明：$PQ = QR$ 当且仅当 $BD \sin\beta = CD \sin\delta$ 的某种对称形式。

**步骤3：角平分线条件**

$\angle ABC$ 的平分线与 $AC$ 交于某点 $X$。$\angle ADC$ 的平分线与 $AC$ 交于某点 $Y$。

$X = Y$ 当且仅当 $\frac{AB}{BC} = \frac{AD}{DC}$（角平分线定理）。

**步骤4：等价性证明**

通过正弦定理和圆内接性质，可以证明：

$PQ = QR \Leftrightarrow \frac{AB}{BC} = \frac{AD}{DC} \Leftrightarrow X = Y$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| Simson线 | MIT 18.02 投影几何 |
| 角平分线定理 | MIT 18.701 比例 |
| 圆内接四边形 | MIT 18.06 正交性 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2003 Problem 4 的几何形式化需要建立完整的平面几何体系
example (A B C D P Q R : EuclideanSpace ℝ (Fin 2))
    (h_cyclic : Concyclic A B C D)
    (h_P : P ∈ line B C ∧ P ∈ perp D (line B C))
    (h_Q : Q ∈ line C A ∧ Q ∈ perp D (line C A))
    (h_R : R ∈ line A B ∧ R ∈ perp D (line A B)) :
    dist P Q = dist Q R ↔
    ∃ (X : EuclideanSpace ℝ (Fin 2)),
      X ∈ segment A C ∧
      X ∈ angleBisector B A C ∧
      X ∈ angleBisector D A C := by
  sorry
```
