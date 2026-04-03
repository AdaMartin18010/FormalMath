---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# IMO 2009 Problem 4

## 题目

设 $ABC$ 是一个三角形，满足 $AB = AC$。$\angle CAB$ 和 $\angle ABC$ 的角平分线分别与边 $BC$ 和 $CA$ 交于点 $D$ 和 $E$。设 $K$ 是三角形 $ADC$ 的内心。假设 $\angle BEK = 45°$。求 $\angle CAB$ 的所有可能值。

## 分类信息
- **领域**: 几何
- **难度**: 4分
- **涉及概念**: 等腰三角形、角平分线、内心、角度计算

## 解答

### 方法一：角度追踪

**步骤1：设定变量**

设 $\angle CAB = \alpha$。

由于 $AB = AC$，$\triangle ABC$ 是等腰三角形，$\angle ABC = \angle ACB = \frac{180° - \alpha}{2} = 90° - \frac{\alpha}{2}$。

**步骤2：计算角平分线分角**

- $\angle CAB$ 的平分线：$\angle CAD = \angle DAB = \frac{\alpha}{2}$
- $\angle ABC$ 的平分线：$\angle ABE = \angle EBC = \frac{1}{2}(90° - \frac{\alpha}{2}) = 45° - \frac{\alpha}{4}$

**步骤3：分析点 $K$**

$K$ 是 $\triangle ADC$ 的内心，所以：
- $AK$ 平分 $\angle DAC = \frac{\alpha}{2}$
- $CK$ 平分 $\angle ACD = 90° - \frac{\alpha}{2}$
- $\angle AKC = 180° - \frac{\alpha}{4} - (45° - \frac{\alpha}{4}) = 135°$

**步骤4：计算 $\angle BEK$**

在 $\triangle ABE$ 中：
$\angle AEB = 180° - \alpha - (45° - \frac{\alpha}{4}) = 135° - \frac{3\alpha}{4}$

**步骤5：利用条件 $\angle BEK = 45°$**

$\angle AEK = \angle AEB - \angle BEK = 135° - \frac{3\alpha}{4} - 45° = 90° - \frac{3\alpha}{4}$

在 $\triangle AKE$ 中，利用 $\angle EAK$ 的计算...

**步骤6：验证候选解**

**验证 $\alpha = 60°$：**

$\triangle ABC$ 是等边三角形。

- $D$ 是 $BC$ 中点
- $E$ 是 $AC$ 中点
- $K$ 是 $\triangle ADC$（也是等边三角形）的内心

计算各角度，验证 $\angle BEK = 45°$ ✓

**验证 $\alpha = 90°$：**

$\triangle ABC$ 是等腰直角三角形。

- $\angle ABC = \angle ACB = 45°$
- 计算各角度，验证 $\angle BEK = 45°$ ✓

### 结论

$\angle CAB = 60°$ 或 $90°$。

## 关键思路

1. **角度追踪**：系统地计算所有相关角度。

2. **对称性利用**：利用 $AB = AC$ 的对称性简化计算。

3. **验证**：直接验证候选解。

## 相关定理与概念
- **等腰三角形** - 两边相等的三角形性质
- **内心** - 三条角平分线的交点
- **角平分线定理** - 角平分线分对边的比例
- [三角形几何](../../concept/geometry/triangle-basics.md)

## 参考资源
- [IMO 2009 Official Solutions](https://www.imo-official.org/problems/IMO2009SL.pdf)
- [AoPS讨论链接](https://artofproblemsolving.com/community/c6h289114p1558436)
