---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2021 Problem 4
---
# IMO 2021 Problem 4

## 题目
设 $\Gamma$ 是以 $I$ 为圆心的圆，$ABCD$ 是凸四边形，$AB,BC,CD,DA$ 均与 $\Gamma$ 相切。设 $\Omega$ 为 $\triangle AIC$ 的外接圆。延长 $BA$ 交 $\Omega$ 于 $X$，延长 $BC$ 交 $\Omega$ 于 $Z$；延长 $AD$ 和 $CD$ 分别交 $\Omega$ 于 $Y$ 和 $T$。证明：
$$AD+DT+TX+XA=CD+DY+YZ+ZC.$$

## 分类信息
- **领域**: 几何
- **难度**: 5分
- **涉及概念**: 切线四边形、外接圆、螺旋相似、全等三角形

## 解答

### 答案
等式成立。

### 证明
设 $P,Q,R,S$ 分别为 $\Gamma$ 与 $AB,BC,CD,DA$ 的切点。

**关键引理**：$\triangle IQZ\cong\triangle IRT$，且 $\triangle IPX\cong\triangle ISY$。
*证明*：考虑圆 $(CQIR)$ 和 $(CITZ)$，存在以 $I$ 为中心的螺旋相似将 $\triangle IQZ$ 映到 $\triangle IRT$。由于 $IQ=IR$（同为 $\Gamma$ 半径），这实际上是全等。同理可证第二式。*

由全等得 $IX=IY$，$IT=IZ$，进而 $TX=YZ$。

计算左边：
\begin{align*}
AD+DT+XA&=AD+(RT-RD)+(XP-AP)\\
&=(AD-RD-AP)+RT+XP\\
&=RT+XP\quad(\text{因为 }AD=AS+SD=AP+RD\text{ 由切线性质}).
\end{align*}

同理，右边：
\begin{align*}
CD+DY+ZC&=CD+(SY-SD)+(ZQ-QC)\\
&=SY+ZQ.
\end{align*}

由引理，$RT=ZQ$ 且 $XP=SY$，故左边等于右边。

## 关键思路与技巧
1. **切点标记**：引入 $P,Q,R,S$ 利用切线长公式
2. **螺旋相似转全等**：利用共圆和等半径证明三角形全等
3. **线段拆分**：将折线段拆分为切线长与全等三角形的对应边
4. **对称性**：等式两边的结构对称，通过全等一一对应

## 参考
- IMO 2021 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
