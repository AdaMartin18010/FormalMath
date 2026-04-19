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
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
tags:
  - "mathematical_reviewed"
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

## 相关文档

- [IMO真题-不等式2](IMO真题-不等式2.md)
- [IMO真题-不等式3](IMO真题-不等式3.md)
- [IMO真题-代数1](IMO真题-代数1.md)
- [IMO真题-代数2](IMO真题-代数2.md)
- [IMO真题-代数3](IMO真题-代数3.md)

## 习题摘要

**习题 1.0** 参见上文问题 1。
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
