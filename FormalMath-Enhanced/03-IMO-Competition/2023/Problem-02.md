---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: 2026-04-15
title: IMO 2023 Problem 2
---
# IMO 2023 Problem 2

## 题目
设 $\triangle ABC$ 为锐角三角形，$AB<AC$。设 $\Omega$ 为其外接圆，$S$ 为弧 $BC$（含 $A$）的中点。过 $A$ 作 $BC$ 的垂线，交 $BS$ 于 $D$，再交 $\Omega$ 于 $E\neq A$。过 $D$ 作 $BC$ 的平行线，交 $BE$ 于 $L$。设 $\omega$ 为 $\triangle BDL$ 的外接圆，$\omega$ 再交 $\Omega$ 于 $P\neq B$。证明：$\omega$ 在 $P$ 处的切线与直线 $BS$ 的交点落在 $\angle BAC$ 的内角平分线上。

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 外接圆、切线、角度追踪、射影几何、调和分割

## 解答

### 答案
切线与 $BS$ 的交点在 $\angle BAC$ 的内角平分线上。

### 证明
设 $F$ 为 $A$ 的对径点，则 $AMFS$ 为矩形（$M$ 为某适当点）。

**步骤1**：$\angle LPS=\angle LDS=\angle CBS=\angle SCP$（由平行和圆周角），故 $L,P,S$ 共线。

**步骤2**：设 $PDF$ 的延长线交 $AM$ 于 $Y$。由调和 bundle：
$$-1=(SM;EF)_A=(S,X;D,AF\cap ES)_F=(\infty X;YA),$$
其中 $\infty=AM\cap SF$ 为无穷远点（因 $AMFS$ 是矩形）。于是 $XY=XA$，即 $X$ 是 $YA$ 的中点。

**步骤3**：由于 $\triangle APY$ 是直角三角形（$\angle APY=90^\circ$），$X$ 为斜边 $YA$ 中点，故 $XP=XA$。

**步骤4**：$XP=XA$ 意味着弧 $\widehat{PM}$ 与弧 $\widehat{AQ}$（$Q$ 为 $PX$ 延长线与 $\Omega$ 的另一交点）度数相等。结合 $\widehat{AS}=\widehat{EM}$，可得 $\widehat{PE}=\widehat{SQ}$。因此
$$\angle QPL=\angle QPS=\angle PQE=\angle PFE=\angle SPL,$$
这说明 $PQ$ 与 $\omega$ 相切于 $P$，即 $PX$ 就是所求切线。而 $X$ 在 $BS$ 上，故切线与 $BS$ 的交点 $X$ 满足 $XP=XA$，即 $X$ 在 $\angle BAC$ 的平分线上（因为 $P$ 和 $A$ 关于 $\angle BAC$ 的平分线对称等价于弧相等）。

## 关键思路与技巧
1. **对径点与矩形**：引入 $A$ 的对径点 $F$ 构造矩形 $AMFS$
2. **角度追踪**：证明 $L,P,S$ 共线是简化问题的关键一步
3. **调和分割**：利用交比 $-1=(SM;EF)_A$ 导出中点关系
4. **切线判定**：通过弧相等证明 $PX$ 是切线

## 参考
- IMO 2023 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
