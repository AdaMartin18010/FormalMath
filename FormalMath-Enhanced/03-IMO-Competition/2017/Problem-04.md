---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2017 Problem 4
---
# IMO 2017 Problem 4

## 题目
设 $R$ 和 $S$ 是圆 $\Omega$ 上的两个不同点，且 $RS$ 不是直径。设 $\ell$ 是 $\Omega$ 在 $R$ 处的切线。点 $T$ 满足 $S$ 是 $RT$ 的中点。在 $\Omega$ 的劣弧 $RS$ 上取点 $J$，使得 $\triangle JST$ 的外接圆 $\Gamma$ 与 $\ell$ 交于两个不同点。设 $A$ 是 $\Gamma$ 和 $\ell$ 的交点中离 $R$ 较近的那个。直线 $AJ$ 再次交 $\Omega$ 于点 $K$。证明：直线 $KT$ 与 $\Gamma$ 相切。

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 圆幂、切线性质、相似三角形、角度追踪

## 解答

### 解答（综合法）

**步骤1：构造辅助点**

设 $B$ 是 $A$ 关于 $S$ 的对称点，则 $ARBT$ 是平行四边形。

**步骤2：应用雷姆定理**

在圆 $\Omega$ 和 $\Gamma$ 上应用**雷姆定理**（Reim's theorem）：
- 由于 $AS \parallel BT$（$S$ 是中点）
- 由雷姆定理，$RK \parallel AT$

因此 $R, K, B$ 共线。

**步骤3：证明 $TBKS$ 共圆**

由雷姆定理的逆，由于 $RK \parallel AT$，可得 $TBKS$ 共圆。

**步骤4：角度计算**

要证 $KT$ 与 $\Gamma$ 相切于某点，等价于证明 $\angle KTA = \angle TSA$（弦切角等于所夹弧对的圆周角）。

计算：
$$\angle KTA = \angle TKB$$
（因为 $RK \parallel AT$，内错角相等）

$$= \angle TSB$$
（因为 $TBKS$ 共圆，同弧所对圆周角）

$$= \angle TSA$$
（因为 $A, S, B$ 共线，$S$ 是中点）

因此 $\angle KTA = \angle TSA$，即 $KT$ 与 $\Gamma$ 相切。

## 关键思路与技巧

1. **对称构造**：$B$ 是 $A$ 关于 $S$ 的对称点，形成平行四边形
2. **雷姆定理**：快速得到平行关系和共圆关系
3. **角度追踪**：通过圆周角和平行线的性质传递角度
4. **弦切角定理**：最终验证切线条件

## 现代联系

本题是**欧几里得几何**的经典问题，展示了**综合几何**的强大力量。在**射影几何**中，这类问题可以通过**交比**和**调和分割**更优雅地处理。在**复几何**中，可以使用**莫比乌斯变换**。

## 相关概念
- 雷姆定理
- 弦切角定理
- 圆幂定理
- 平行四边形性质

## 参考
- IMO 2017 Official Solutions
- AoPS Community: https://artofproblemsolving.com/community/c6h1480149p8633208[需更新]
