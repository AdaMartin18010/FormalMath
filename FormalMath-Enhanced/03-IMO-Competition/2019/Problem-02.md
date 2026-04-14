---
msc_primary: 00A99
processed_at: '2026-04-15'
title: IMO 2019 Problem 2
---
# IMO 2019 Problem 2

## 题目
在三角形 $ABC$ 中，点 $A_1$ 在边 $BC$ 上，点 $B_1$ 在边 $AC$ 上。设 $P$ 和 $Q$ 分别是线段 $AA_1$ 和 $BB_1$ 上的点，满足 $PQ \parallel AB$。点 $P_1$ 在射线 $PB_1$ 上 $B_1$ 的延长一侧，使得 $\angle PP_1C = \angle BAC$。点 $Q_1$ 在射线 $QA_1$ 上 $A_1$ 的延长一侧，使得 $\angle CQ_1Q = \angle CBA$。证明：点 $P, Q, P_1, Q_1$ 共圆。

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 共圆、Reim定理、相似三角形、角度追踪

## 解答

### 答案
点 $P, Q, P_1, Q_1$ 共圆。

### 证明
设直线 $PP_1$ 和 $QQ_1$ 分别交 $AB$ 于 $X$ 和 $Y$。由于 $PQ \parallel AB$，由 Reim 定理，只需证明 $P_1, X, Y, Q_1$ 共圆即可推出 $P, Q, P_1, Q_1$ 共圆。

由题设角度条件，$P_1, C, X, A$ 共圆且 $Q_1, C, Y, B$ 共圆。

设 $AA_1$ 和 $BB_1$ 分别再次交 $\triangle ABC$ 的外接圆于 $A_2$ 和 $B_2$。

**引理**：$P, Q, A_2, Q_1$ 共圆，且 $P, Q, B_2, P_1$ 共圆。

*证明*：因为 $\angle CQ_1A_1 = \angle CBA = \angle CA_2A = \angle CA_2A_1$，所以 $C, A_1, A_2, Q_1$ 共圆。于是
$$\angle QQ_1A_2 = \angle A_1Q_1A_2 = \angle A_1CA_2 = \angle BCA_2 = \angle BAA_2 = \angle QPA_2,$$
故 $P, Q, A_2, Q_1$ 共圆。同理可得 $P, Q, B_2, P_1$ 共圆。

又因为 $PQ \parallel AB$，由 Reim 定理，$P, Q, A_2, B_2$ 共圆。

由于 $P, Q, A_2, B_2$ 已共圆，结合上述两圆，由根轴定理可知 $P, Q, P_1, Q_1$ 共圆。证毕。

## 关键思路与技巧
1. **角度条件转共圆**：将给定的角等式转化为四点共圆
2. **Reim定理**：利用平行线构造共圆四边形
3. **辅助点 $A_2, B_2$**：将问题转移到外接圆上简化
4. **根轴定理**：通过多个共圆关系导出目标结论

## 参考
- IMO 2019 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes
