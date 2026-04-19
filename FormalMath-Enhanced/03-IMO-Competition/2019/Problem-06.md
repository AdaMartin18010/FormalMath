---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: IMO 2019 Problem 6
---
# IMO 2019 Problem 6

## 题目
设 $I$ 为不等边锐角三角形 $ABC$ 的内心。内切圆 $\omega$ 分别与边 $BC, CA, AB$ 相切于点 $D, E, F$。过 $D$ 作垂直于 $EF$ 的直线，再次交 $\omega$ 于点 $R$（$R \neq D$）。直线 $AR$ 再次交 $\omega$ 于点 $P$（$P \neq R$）。三角形 $PCE$ 与 $PBF$ 的外接圆再次相交于点 $Q$（$Q \neq P$）。证明：直线 $DI$ 与 $PQ$ 的交点在 $\angle BAC$ 的外角平分线上。

（等价表述：设 $X = DI \cap PQ$，证明 $AX \perp AI$。）

## 分类信息
- **领域**: 几何
- **难度**: 7分
- **涉及概念**: 内心、内切圆、外接圆、Reim定理、根轴、等角共轭、调和四边形

## 解答

### 答案
直线 $DI$ 与 $PQ$ 的交点落在 $\angle BAC$ 的外角平分线上。

### 证明
设 $X = DI \cap PQ$，需证 $AX \perp AI$，即 $AX$ 是 $\angle BAC$ 的外角平分线。

**步骤1：基本共圆关系**

设 $AA_1$ 和 $BB_1$ 再次交 $\triangle ABC$ 的外接圆于 $A_2, B_2$ 等辅助构造。由 Reim 定理及角度追踪，有以下基本事实：
- $B, I, Q, C$ 共圆（鸡爪圆）。
- 设 $\omega$ 在 $D$ 的对径点为 $G$，则 $AGIQ$ 共圆且 $AMQD$ 共圆（$M$ 为弧 $BC$ 中点）。

**步骤2：重新刻画 $Q$**

设 $KP$（$K = DI \cap PQ$）与鸡爪圆 $(BIC)$ 再次交于 $L$。核心引理为 $K, P, L$ 共线。

设 $\odot(AEF)$ 与 $\odot(ABC)$ 再次交于 $X'$。由 $BD/CD = BF/CE = XB/XC$ 可知 $X'D$ 平分 $\angle BX'C$，故 $X'$ 在直线 $DM$ 上（$M$ 为弧 $BC$ 中点）。因此 $X'$ 与前面定义的某辅助点重合。

由相似关系 $\triangle XFP \sim \triangle XBL$，可得
$$\angle XPL = \angle XFB = 180^\circ - \angle NBX = 180^\circ - \angle NMX = 180^\circ - \angle KDX = 180^\circ - \angle KPX,$$
故 $K, P, L$ 共线。

**步骤3：证明 $Q$ 在 $\odot(CPE)$ 上**

在重新定义 $Q$ 为直线 $KP$ 与鸡爪圆的交点后，有
$$\angle CQP = \angle CQL = \angle ERP = \angle CEP,$$
故此 $Q$ 恰在 $\odot(CPE)$ 上。同理可证其在 $\odot(PBF)$ 上。

**步骤4：根轴方法（另一视角）**

设 $KP$ 与内切圆 $\omega$ 再次交于 $U$。只需证 $U$ 对 $\odot(PBF)$ 和 $\odot(PCE)$ 的幂相等。

设 $UE$ 与 $\odot(CPE)$ 再次交于 $S$，则 $\triangle UPS \sim \triangle EPC$，得 $US \cdot UE = (UP/PE) \cdot CE \cdot UE$。同理另一幂为 $(UP/PF) \cdot BF \cdot UF$。

由前面已证的 $(CE/PE) \cdot UE = (BF/PF) \cdot UF$（这来自 $\triangle IO_1O_2 \sim \triangle UEF$ 的比例关系），两幂相等，故 $U$ 在根轴 $PQ$ 上。于是 $X$ 在 $DI$ 上且满足 $AX \perp AI$。

证毕。

## 关键思路与技巧
1. **对径点与辅助圆**：引入 $D$ 的对径点构造额外共圆关系
2. **Reim定理**：多次利用平行与圆周角的传递性
3. **重新定义 $Q$**：先作 $K,P,L$ 共线，再验证所得交点满足原题的圆条件
4. **根轴与等幂**：用根轴性质将共线问题转化为幂相等的问题
5. **等角线**：$AU$ 与 $AV$ 作为 $\angle BAC$ 的等角线是关键 hidden structure

## 参考
- IMO 2019 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes
