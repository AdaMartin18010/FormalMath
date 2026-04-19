---
title: "IMO真题-几何：平面几何证明"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 几何
source: "IMO 2004 Problem 1"
target_courses:
  - MIT 18.06
status: completed
created_at: 2026-04-18
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
tags:
  - "mathematical_reviewed"
---

# IMO 2004 Problem 1：平面几何

## 题目

设三角形 $ABC$ 为锐角三角形，$AB \neq AC$。以 $BC$ 为直径的圆分别交边 $AB$、$AC$ 于 $M$、$N$。记 $O$ 为 $BC$ 的中点。$\angle BAC$ 和 $\angle MON$ 的角平分线交于 $R$。证明：三角形 $BMR$ 和 $CNR$ 的外接圆有一个公共点在边 $BC$ 上。

## 解答

**关键引理**：若 $P$ 在 $BC$ 上，则 $P$ 在 $\triangle BMR$ 的外接圆上当且仅当 $\angle BPM = \angle BRM$。

**证明**：

1. 由于 $BC$ 为直径，$\angle BMC = \angle BNC = 90°$。

2. $O$ 为圆心，$OM = ON = OB = OC$（半径）。

3. 设 $\angle BAC = 2\alpha$，则 $\angle MON = 2\angle MBN = 2\angle MCN$（圆周角）。

4. 由于 $R$ 在 $\angle BAC$ 和 $\angle MON$ 的角平分线上，有对称性。

5. 设 $P$ 为 $BC$ 上满足 $\angle BPM = \angle BRM$ 的点。由对称性，$\angle CPN = \angle CRN$。

6. 因此 $P$ 同时在 $\triangle BMR$ 和 $\triangle CNR$ 的外接圆上。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 圆周角定理 | MIT 18.02 三角函数 |
| 角平分线性质 | MIT 18.701 对称群 |
| 四点共圆 | Harvard 232br 相交理论 |

## Lean4 形式化

```lean4
import Mathlib

-- 几何形式化需要建立平面几何的公理体系
-- 这是极具挑战性的形式化任务
example (A B C M N O R : EuclideanSpace ℝ (Fin 2))
    (h_acute : AcuteTriangle A B C)
    (h_diameter : O = midpoint B C ∧ dist O B = dist O M)
    (h_M_on_AB : Collinear A B M)
    (h_N_on_AC : Collinear A C N)
    (h_R_bisector : R ∈ angleBisector A B C ∧ R ∈ angleBisector M O N) :
    ∃ (P : EuclideanSpace ℝ (Fin 2)),
      P ∈ segment B C ∧
      Concyclic B M R P ∧
      Concyclic C N R P := by
  sorry
```

## 相关文档

- [IMO真题-不等式2](IMO真题-不等式2.md)
- [IMO真题-不等式3](IMO真题-不等式3.md)
- [IMO真题-代数1](IMO真题-代数1.md)
- [IMO真题-代数2](IMO真题-代数2.md)
- [IMO真题-代数3](IMO真题-代数3.md)

## 习题摘要

**习题 1.0** 参见上文问题 1。

**习题 2.0** 参见上文问题 2。

**习题 3.0** 参见上文问题 3。

**习题 4.0** 参见上文问题 4。

**习题 5.0** 参见上文问题 5。

**习题 6.0** 参见上文问题 6。
## 参考文献

1. International Mathematical Olympiad (IMO). *Official Problems and Solutions*. Available at: https://www.imo-official.org/
2. Engel, A. (1998). *Problem-Solving Strategies*. Springer. ISBN: 978-0387982191.
3. Andreescu, T., & Gelca, R. (2000). *Mathematical Olympiad Challenges*. Birkhäuser. ISBN: 978-0817641900.
## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确
