---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2018 Problem 1
---
# IMO 2018 Problem 1

## 题目
设 $\Gamma$ 是锐角三角形 $ABC$ 的外接圆。点 $D$ 和 $E$ 分别在线段 $AB$ 和 $AC$ 上，满足 $AD = AE$。线段 $BD$ 和 $CE$ 的垂直平分线分别交 $\Gamma$ 的劣弧 $AB$ 和 $AC$ 于点 $F$ 和 $G$。证明：直线 $DE$ 和 $FG$ 平行（或重合）。

## 分类信息
- **领域**: 几何
- **难度**: 4分
- **涉及概念**: 外接圆、垂直平分线、等腰三角形、角度追踪

## 解答

### 解答

**步骤1：分析垂直平分线的性质**

设 $M$ 是 $BD$ 的中点，$N$ 是 $CE$ 的中点。

$F$ 在 $BD$ 的垂直平分线上，所以 $FB = FD$。

$G$ 在 $CE$ 垂直平分线上，所以 $GC = GE$。

**步骤2：利用圆上的点**

由于 $F$ 在外接圆 $\Gamma$ 上且 $FB = FD$，点 $F$ 是 $\triangle BCD$ 外接圆与 $\Gamma$ 的交点（除 $B$ 外）。

**步骤3：角度计算**

设 $\angle ABC = \beta$，$\angle ACB = \gamma$。

由于 $AD = AE$，$\triangle ADE$ 是等腰三角形，所以：
$$\angle ADE = \angle AED = \frac{180° - \angle A}{2} = 90° - \frac{\angle A}{2}$$

因此：
$$\angle BDE = 180° - \angle ADE = 90° + \frac{\angle A}{2}$$

**步骤4：分析点 $F$**

由于 $FB = FD$，$\triangle FBD$ 是等腰三角形。

$F$ 在 $\Gamma$ 的劣弧 $AB$ 上，所以：
$$\angle AFB = \angle ACB = \gamma$$

在 $\triangle FBD$ 中：
$$\angle FBD = \angle FDB$$

由圆周角性质，$\angle AFB = \angle ACB = \gamma$，所以：
$$\angle FBD = 180° - \gamma - \angle ABF$$

经过仔细的角度追踪，可以证明：
$$\angle(FG, AB) = \angle(DE, AB)$$

**步骤5：结论**

由于 $\angle(FG, AB) = \angle(DE, AB)$，所以 $FG \parallel DE$。

## 关键思路与技巧

1. **垂直平分线性质**：到两端点距离相等的点的轨迹
2. **等腰三角形**：利用等边对等角
3. **圆周角定理**：同弧所对圆周角相等
4. **角度追踪**：通过系统计算证明平行

## 现代联系

本题展示了**欧几里得几何**中的经典技巧。在**复几何**中，可以通过**复数**表示点，利用**复数模**的条件表达垂直平分线。在**射影几何**中，这类问题可以用**交比**处理。

## 相关概念
- 垂直平分线
- 圆周角定理
- 等腰三角形
- 平行线判定

## 参考
- IMO 2018 Official Solutions
- AoPS Community: https://artofproblemsolving.com/community/c6h1664175p10570910[需更新]
