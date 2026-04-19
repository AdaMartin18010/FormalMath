---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: 2026-04-15
title: IMO 2022 Problem 4
---
# IMO 2022 Problem 4

## 题目
设 $ABCDE$ 为凸五边形，$BC=DE$。假设五边形内部存在一点 $T$，满足 $TB=TD$，$TC=TE$，且 $\angle ABT=\angle TEA$。设直线 $AB$ 分别交 $CD$、$CT$ 于 $P$、$Q$（顺序为 $P,B,A,Q$）；直线 $AE$ 分别交 $CD$、$DT$ 于 $R$、$S$（顺序为 $R,E,A,S$）。证明：$P,S,Q,R$ 四点共圆。

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 相似三角形、Reim定理、比例、共圆

## 解答

### 答案
$P,S,Q,R$ 四点共圆。

### 证明
由条件 $TB=TD$，$TC=TE$，$BC=DE$，得 $\triangle BTC\cong\triangle DTE$。

定义辅助点：$K=CT\cap AE$，$L=DT\cap AB$，$X=BT\cap AE$，$Y=ET\cap AB$。

**关键引理**：$\triangle BTQ\sim\triangle ETS$，且 $BY:YL:LQ=EX:XK:KS$。
*证明*：已知 $\triangle BTY\sim\triangle ETX$。又
$$\angle BTL=\angle BTD=\angle CTE=\angle KTE,\quad \angle BTQ=\angle BTC=\angle DTE=\angle ST E,$$
故得相似及比例关系。*

由引理的比例关系：
- $\frac{TL}{TQ}=\frac{TK}{TS}$，即 $TL\cdot TS=TK\cdot TQ$，故 $K,L,S,Q$ 共圆。
- $\frac{TC}{TK}=\frac{TE}{TK}=\frac{TB}{TL}=\frac{TD}{TL}$，故 $KL\parallel PQ$（因为 $C,T,Q$ 和 $D,T,S$ 分别共线）。

由 Reim 定理的逆，$KL\parallel PQ$ 且 $K,L,S,Q$ 共圆，推出 $P,S,Q,R$ 共圆。

## 关键思路与技巧
1. **全等三角形**：利用 $BC=DE$ 和等腰条件证明核心全等
2. **辅助点构造**：引入 $K,L,X,Y$ 建立比例桥梁
3. **相似与比例**：通过相似三角形导出幂等关系
4. **Reim定理**：利用平行线与共圆关系导出目标四点共圆

## 参考
- IMO 2022 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
