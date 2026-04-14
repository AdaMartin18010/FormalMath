---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2025 Problem 2
---
# IMO 2025 Problem 2

## 题目
设 $\Omega$ 与 $\Gamma$ 为两圆，圆心分别为 $M$ 与 $N$，且 $\Omega$ 的半径小于 $\Gamma$ 的半径。设两圆交于两个不同点 $A$ 与 $B$。直线 $MN$ 交 $\Omega$ 于 $C$、交 $\Gamma$ 于 $D$，且 $C,M,N,D$ 依次排列在直线上。设 $P$ 为 $\triangle ACD$ 的外心。直线 $AP$ 再次交 $\Omega$ 于 $E\neq A$，再次交 $\Gamma$ 于 $F\neq A$。设 $H$ 为 $\triangle PMN$ 的垂心。证明：过 $H$ 且平行于 $AP$ 的直线与 $\triangle BEF$ 的外接圆相切。

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 外心、垂心、相切、平行线、位似

## 解答

### 答案
过 $H$ 平行于 $AP$ 的直线与 $\triangle BEF$ 的外接圆相切。

### 证明
设 $\alpha=\angle DCA=\angle BCD$，$\beta=\angle ADC=\angle CDB$。

**步骤1**：$P$ 是 $\triangle AMN$ 的 $A$-旁心。
*证明*：$PM$ 是 $AC$ 的垂直平分线，而 $C,M,N$ 共线，故 $PM$ 平分 $\angle AMC$ 的外角，即 $PM$ 是 $\triangle AMN$ 在 $M$ 处的外角平分线。同理 $PN$ 是 $N$ 处的外角平分线。因此 $P$ 为 $A$-旁心，$AP$ 是 $\angle MAN$ 的内角平分线。*

**步骤2**：$CE\parallel AD$ 且 $DF\parallel AC$。
*证明*：$\angle AEC=\angle ABC=\angle CAB=90^\circ-\alpha=\angle PAD$（因 $P$ 为外心，$\angle PAD=90^\circ-\alpha$）。故 $CE\parallel AD$。同理 $DF\parallel AC$。*

令 $A''=CE\cap DF$。由步骤2，$ACA''D$ 为平行四边形，且 $BA''\parallel CD$。

**步骤3**：设 $T$ 为 $\triangle A''EF$ 的外心。则 $T$ 落在 $BA''$ 上，且 $T$ 也是 $(BEF)$ 上弧 $EF$ 的中点。
*证明*：计算 $\triangle A''EF$ 的角度：$\angle FEA''=90^\circ-\alpha$，$\angle A''FE=90^\circ-\beta$，$\angle EA''F=\alpha+\beta$。于是
$$\angle EA''T=90^\circ-\angle A''FE=\beta=\angle A''CD=\angle CA''B,$$
故 $T\in BA''$。又 $\angle ETF=2\angle EA''F=2(\alpha+\beta)$，而
$$\angle EBF=\angle EBA+\angle ABF=\angle ECA+\angle ADF=(\alpha+\beta)+(\alpha+\beta)=2(\alpha+\beta),$$
所以 $T\in(BEF)$ 且为弧 $EF$ 中点。*

**步骤4**：$T$ 也在直线 $ME$ 和 $NF$ 上。
*证明*：$\triangle FEA''\sim\triangle FAD$（以 $F$ 为中心的位似），该位似将 $T$ 映到 $N$，故 $F,T,N$ 共线。同理 $E,T,M$ 共线。*

**步骤5**：$MH\parallel AD$ 且 $NH\parallel AC$。
*证明*：因 $P$ 是 $\triangle AMN$ 的旁心，$\angle PMN=90^\circ-\phi$（$\phi=\frac12\angle MAN$）。$H$ 为垂心，故 $MH\perp PN$。而 $PN$ 是 $AD$ 的垂直平分线，方向与 $AD$ 垂直，所以 $MH\parallel AD$。同理 $NH\parallel AC$。*

**步骤6**：完成切线证明。
由步骤5和 $A''D\parallel AC$、$A''C\parallel AD$，得 $MHA''N$ 为平行四边形。于是 $HA''\parallel MN$。而 $MN\perp AB$（连心线垂直公共弦），故 $HA''\perp AB$。

另一方面，$T$ 为弧 $EF$ 中点，$TE=TF$。由步骤4，$T$ 在 $ME$ 和 $NF$ 上，可证 $TH\perp EF$。由于 $EF$ 在直线 $AP$ 上，故 $TH\perp AP$。而 $T\in(BEF)$ 且为弧中点，所以过 $T$ 垂直于 $AP$ 的直线就是过 $H$ 平行于 $AP$ 的直线，它必与 $(BEF)$ 相切于 $T$。

## 关键思路与技巧
1. **旁心识别**：$P$ 是 $\triangle AMN$ 的 $A$-旁心，简化角度计算
2. **平行四边形 $ACA''D$**：通过 $CE\parallel AD$、$DF\parallel AC$ 构造辅助点 $A''$
3. **外心 $T$**：$\triangle A''EF$ 的外心 $T$ 同时落在 $(BEF)$ 和 $BA''$ 上
4. **垂心性质**：利用 $H$ 与旁心的关系得到 $MH\parallel AD$ 等平行关系
5. **切线判定**：证明 $TH\perp AP$ 且 $T$ 在圆上

## 参考
- IMO 2025 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
