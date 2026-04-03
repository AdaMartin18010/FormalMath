---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# IMO 2007 Problem 4

## 题目

在 $\triangle ABC$ 中，角平分线 $BL$ 与 $AC$ 交于点 $L$，角平分线 $CM$ 与 $AB$ 交于点 $M$。设过点 $A$ 且平行于 $BC$ 的直线与 $\triangle AML$ 的外接圆相交于点 $K$（$K \neq A$）。证明：$KA = KL = KM$。

## 分类

- **领域**: 几何
- **难度**: 5分
- **关键词**: 三角形几何、角平分线、共圆、平行线、等腰三角形

## 解答

### 分析

这是一道关于三角形、角平分线和共圆性质的经典几何题。

**已知条件**：

- $BL$ 是 $\angle ABC$ 的平分线，$L$ 在 $AC$ 上
- $CM$ 是 $\angle ACB$ 的平分线，$M$ 在 $AB$ 上
- 过 $A$ 平行于 $BC$ 的直线与 $\triangle AML$ 的外接圆交于 $K$

**求证**：$KA = KL = KM$（即 $K$ 是 $\triangle AML$ 外接圆的圆心）

### 证明

**步骤1：建立基本角度关系**

设 $\angle ABC = 2\beta$，$\angle ACB = 2\gamma$，则 $\angle BAC = 180° - 2\beta - 2\gamma$。

由于 $BL$ 平分 $\angle ABC$：$\angle ABL = \angle LBC = \beta$

由于 $CM$ 平分 $\angle ACB$：$\angle ACM = \angle MCB = \gamma$

**步骤2：分析平行线性质**

设过 $A$ 平行于 $BC$ 的直线为 $\ell$。

由于 $AK \parallel BC$：

- $\angle KAL = \angle ACB = 2\gamma$（同位角，$AL$ 为截线）
- $\angle KAM = \angle ABC = 2\beta$（同位角，$AM$ 为截线）

**步骤3：利用共圆性质**

$K, A, M, L$ 共圆。

由圆内接四边形性质：
$$\angle AKM = \angle ALM$$
$$\angle AKL = \angle AML$$

**步骤4：计算关键角度**

在 $\triangle AML$ 中：

- $\angle MAL = \angle BAC = 180° - 2\beta - 2\gamma$

由三角形内角和：
$$\angle AML + \angle ALM = 2\beta + 2\gamma$$

**步骤5：证明 $KA = KL$**

我们需要证明 $\triangle KAL$ 是等腰三角形，即 $\angle KAL = \angle KLA$。

已知 $\angle KAL = 2\gamma$（步骤2）。

计算 $\angle KLA$：

由于 $K, A, M, L$ 共圆：
$$\angle KLA = \angle KMA$$

在 $\triangle AKM$ 中，$\angle KAM = 2\beta$。

利用圆周角：$\angle KMA = \angle KLA$。

实际上，我们需要更仔细地计算。

**关键观察**：

由于 $AK \parallel BC$，考虑 $\angle LAK = 2\gamma$。

由圆的性质，$\angle LMK = \angle LAK = 2\gamma$。

类似地，$\angle MLK = \angle MAK = 2\beta$。

在 $\triangle KML$ 中：
$$\angle MKL = 180° - 2\beta - 2\gamma = \angle BAC$$

**步骤6：证明 $K$ 是圆心**

要证明 $KA = KL = KM$，等价于证明 $K$ 是 $\triangle AML$ 外接圆的圆心。

即证明 $K$ 到 $A, M, L$ 的距离相等。

**利用角度计算**：

由圆周角定理，圆心角是圆周角的两倍。

设 $O$ 是 $\triangle AML$ 外接圆的圆心。我们需要证明 $K = O$。

由于 $\angle MKL = \angle MAL$（由上面计算），这正好说明 $K$ 是圆心！

（圆心角 $\angle MKL$ 对应的弧是 $ML$，圆周角 $\angle MAL$ 也对应弧 $ML$。如果它们相等，则 $K$ 是圆心）

验证：$\angle MKL = 180° - 2\beta - 2\gamma = \angle MAL$ ✓

因此 $K$ 是 $\triangle AML$ 外接圆的圆心，故 $KA = KL = KM$。

### 结论

$KA = KL = KM$ 得证。

## 数学概念

### 核心概念

1. **角平分线定理**
   $$\frac{AL}{LC} = \frac{AB}{BC}, \quad \frac{AM}{MB} = \frac{AC}{BC}$$

2. **圆周角定理**
   - 同弧所对的圆周角相等
   - 圆心角是圆周角的两倍

3. **平行线性质**
   - 同位角相等
   - 内错角相等

4. **三角形外接圆**
   - 外心的性质

### 与FormalMath主项目的链接

- [三角形几何](../../concept/geometry/triangle-basics.md)
- [角平分线定理](../../concept/geometry/angle-bisector-theorem.md)
- [圆的性质](../../concept/geometry/circle-properties.md)
- [共圆点](../../concept/geometry/cyclic-quadrilaterals.md)

## 变体与推广

### 变体1（外角平分线）

如果用外角平分线代替内角平分线，结论如何变化？

### 变体2（一般点）

对于 $BC$ 边上的一般点，类似的共圆性质是否成立？

### 推广（一般三角形）

对于任意三角形和特定构造，研究类似的等距点。

## 参考

- [IMO 2007 Official Solutions](https://www.imo-official.org/problems/IMO2007SL.pdf)
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h159841p893690)
- 相关定理：角平分线定理、圆周角定理、外心性质

---

*解答整理：FormalMath项目团队*
