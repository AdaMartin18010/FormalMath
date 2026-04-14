---
msc_primary: 00A99
processed_at: '2026-04-15'
title: IMO 2020 Problem 1
---
# IMO 2020 Problem 1

## 题目
设凸四边形 $ABCD$ 内有一点 $P$，满足
$$\angle PAD : \angle PBA : \angle DPA = 1:2:3 = \angle CBP : \angle BAP : \angle BPC.$$
证明：$\angle ADP$ 的内角平分线、$\angle PCB$ 的内角平分线与线段 $AB$ 的垂直平分线三线共点。

## 分类信息
- **领域**: 几何
- **难度**: 4分
- **涉及概念**: 角度追踪、外心、共点、圆的性质

## 解答

### 答案
三线共点于 $\triangle PAB$ 的外心 $O$。

### 证明
设 $O$ 为 $\triangle PAB$ 的外心。显然 $O$ 在 $AB$ 的垂直平分线上。

由角度比例，设 $\angle PAD = \alpha$，$\angle PBA = 2\alpha$，$\angle DPA = 3\alpha$。同理 $\angle CBP = \alpha$，$\angle BAP = 2\alpha$，$\angle BPC = 3\alpha$。

**步骤1：计算相关角度**

在 $\triangle ADP$ 中：
$$\angle ADP = 180^\circ - \angle PAD - \angle DPA = 180^\circ - \alpha - 3\alpha = 180^\circ - 4\alpha.$$

在 $\triangle BCP$ 中：
$$\angle BCP = 180^\circ - \angle CBP - \angle BPC = 180^\circ - \alpha - 3\alpha = 180^\circ - 4\alpha.$$

**步骤2：证明 $O$ 在 $\angle ADP$ 的平分线上**

由于 $O$ 是 $\triangle PAB$ 的外心，$OA = OP$，故 $\angle AOP = 2\angle ABP = 4\alpha$（圆心角）。

考虑四边形 $AOPD$：
$$\angle OAP = 90^\circ - \angle ABP = 90^\circ - 2\alpha.$$
又 $\angle PAD = \alpha$，所以
$$\angle OAD = \angle OAP + \angle PAD = 90^\circ - 2\alpha + \alpha = 90^\circ - \alpha.$$

在等腰三角形 $OAP$ 中，$\angle OPA = \angle OAP = 90^\circ - 2\alpha$。
于是
$$\angle OPD = \angle DPA - \angle OPA = 3\alpha - (90^\circ - 2\alpha) = 5\alpha - 90^\circ.$$

但这路径较繁琐。更简洁的方法是：

**关键观察**：$\angle BOP = 2\angle BAP = 4\alpha$。
而 $\angle BCP = 180^\circ - 4\alpha$，故
$$\angle BCP + \angle BOP = 180^\circ,$$
因此 $B, C, P, O$ 共圆！

由于 $OB = OP$（$O$ 为外心），$O$ 在弦 $BP$ 的垂直平分线上，故 $O$ 平分弧 $BP$（不含 $C$ 的那一段），从而 $O$ 在 $\angle BCP$ 的平分线上。

同理，由 $\angle AOP = 2\angle ABP = 4\alpha$ 且 $\angle ADP = 180^\circ - 4\alpha$，可得 $A, D, P, O$ 共圆，于是 $O$ 也在 $\angle ADP$ 的平分线上。

因此三线共点于 $O$。证毕。

## 关键思路与技巧
1. **外心猜想**：通过角度比例猜测共点可能为 $\triangle PAB$ 的外心
2. **四点共圆**：利用圆心角与圆周角关系证明 $B,C,P,O$ 和 $A,D,P,O$ 共圆
3. **弧中点性质**：外心位于等腰三角形底边的垂直平分线上，从而落在角平分线上
4. **角度计算**：严谨的角度追踪是证明共圆和共点的核心

## 参考
- IMO 2020 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes
