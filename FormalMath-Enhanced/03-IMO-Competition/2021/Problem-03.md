---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2021 Problem 3
---
# IMO 2021 Problem 3

## 题目
设 $D$ 为锐角三角形 $ABC$ 内部一点，$AB>AC$，$\angle DAB=\angle CAD$。点 $E$ 在 $AC$ 上，满足 $\angle ADE=\angle BCD$；点 $F$ 在 $AB$ 上，满足 $\angle FDA=\angle DBC$；点 $X$ 在直线 $AC$ 上，满足 $CX=BX$。设 $O_1,O_2$ 分别为 $\triangle ADC$ 和 $\triangle EXD$ 的外心。证明：直线 $BC$、$EF$、$O_1O_2$ 三线共点。

## 分类信息
- **领域**: 几何
- **难度**: 7分
- **涉及概念**: 等角共轭、Miquel点、外心、根轴

## 解答

### 答案
$BC$、$EF$、$O_1O_2$ 三线共点。

### 证明
设 $D'$ 为 $D$ 关于 $\angle A$ 的等角共轭点。由角度条件，$CEDD'$ 和 $BFDD'$ 均为圆内接四边形。由幂点定理，
$$AE\cdot AC=AD\cdot AD'=AF\cdot AB,$$
故 $BCEF$ 为圆内接四边形。

设 $Z=EF\cap BC$。由 $CEDD'$ 和 $BFDD'$ 的圆性质，可知 $ZD$ 与圆 $(BCD)$ 和 $(DEF)$ 均相切。

设 $M$ 为圆内接四边形 $BCEF$ 的 Miquel 点。由 Miquel 构型，$A,M,Z$ 共线，且 $(AFEM)$、$(ZCEM)$ 共圆。

**引理**：$B,X,M,E$ 共圆。
*证明*：$\angle EMB=180^\circ-\angle AMB-\angle EMZ=180^\circ-2\angle ACB=\angle EXB$，故共圆。

设 $N$ 为圆 $(ACD)$ 与 $(DEX)$ 的第二交点，$R=AC\cap EX$。由幂点定理，$R$ 在两圆的根轴上，故 $N,R,D$ 共线。进一步可证 $B,D,M,N$ 共圆。

于是 $(ACD)$、$(BDMN)$、$(DEX)$ 三圆共轴，它们的圆心 $O_1$、$(BDMN)$ 的圆心、$O_2$ 共线。

最后，取以 $Z$ 为圆心、$ZD$ 为半径的圆 $\omega$ 作反演。由
$$ZC\cdot ZB=ZD^2=ZE\cdot ZF=ZM\cdot ZA,$$
可知 $\omega$ 将 $(ACD)$ 与 $(BDMN)$ 互换。因此 $O_1$ 与 $(BDMN)$ 的圆心必与反演中心 $Z$ 共线。结合前面的共轴性，得 $O_1,O_2,Z$ 共线，即 $BC,EF,O_1O_2$ 共点于 $Z$。

## 关键思路与技巧
1. **等角共轭**：引入 $D'$ 揭示隐藏的圆内接四边形
2. **Miquel点**：利用 $BCEF$ 的 Miquel 构型建立多点共圆关系
3. **根轴与共轴圆**：通过三圆共轴性导出圆心共线
4. **反演**：以 $Z$ 为中心的反演将问题转化为共线性

## 参考
- IMO 2021 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
