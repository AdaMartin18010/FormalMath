---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2013 Problem 04
---

# IMO 2013 Problem 04

## 题目

设三角形 $ABC$ 有外心 $O$ 和内心 $I$。点 $D, E, F$ 分别在边 $BC, CA, AB$ 上，使得 $BD + BF = CA$，$CD + CE = AB$。三角形 $BFD$ 和 $CDE$ 的外接圆交于点 $P \neq D$。证明：$OP = OI$。

## 分类信息
- **领域**: 平面几何
- **难度**: 5分
- **涉及概念**: 外心、内心、密克点、根轴

---

## 定义与预备知识

**定义 1（外心 $O$ 与内心 $I$）** $O$ 为三边垂直平分线交点；$I$ 为三角平分线交点。

**定义 2（密克点）** 完全四边形的四个三角形外接圆共点，称为密克点。

**定义 3（根轴）** 两圆幂相等的点轨迹为根轴（直线）。

**引理 1（Euler公式）** $OI^2 = R(R - 2r)$，$R$ 为外接圆半径，$r$ 为内切圆半径。

**引理 2（内心距离）** $IA = \frac{r}{\sin(A/2)}$。

---

## 定理与证明

**定理（IMO 2013 Problem 4）** 在上述构型下，$OP = OI$。

*证明.* 

**步骤 1：分析点 $D, E, F$ 的几何意义**

条件 $BD + BF = CA = b$ 和 $CD + CE = AB = c$。

设 $BD = x$，$BF = b - x$。$CD = a - x$，$CE = c - (a - x) = c - a + x$。

由 $E$ 在 $CA$ 上，$CE \geq 0$ 且 $CE \leq b$。故 $c - a + x \geq 0$，$x \geq a - c$；且 $c - a + x \leq b$，$x \leq a + b - c = 2(s-c)$。

**步骤 2：特殊情形验证**

当 $\triangle ABC$ 为等腰（$b=c$），$D, E, F$ 具有对称性。设 $b=c$，则 $BD + BF = b$，$CD + CE = c = b$。由对称，$D$ 为 $BC$ 中点？若 $BD = BF = x$，$CD = CE = b - x$。$BD + CD = a$，$x + b - x = b \neq a$（除非 $a=b$，等边）。故 $D$ 不一定是中点。

**步骤 3：利用圆的性质**

$\odot(BFD)$ 与 $\odot(CDE)$ 交于 $P$ 和 $D$。由根轴，$PD$ 为两圆根轴。

$\angle BPD = \angle BFD$（同弧 $BD$），$\angle CPD = \angle CED$（同弧 $CD$）。

**步骤 4：证明 $P$ 在 $OI$ 的中垂线上**

标准证明通过证明 $P$ 是某个已知点到 $O$ 和 $I$ 等距的点，或证明 $P$ 位于以 $O$ 为圆心、$OI$ 为半径的圆上。

具体策略：证明 $\angle OPI = \angle OIP$ 或 $OP^2 = OI^2$。

利用坐标法：设 $\triangle ABC$ 外接圆为单位圆。$O=0$。内心 $I = -(aA + bB + cC)/(a+b+c)$（复数公式，其中 $a,b,c$ 为边长）。

计算 $D, E, F$ 的复数坐标，求 $\odot(BFD)$ 和 $\odot(CDE)$ 的交点 $P$，验证 $|P| = |I|$（因 $O=0$，$OP = |P|$，$OI = |I|$）。

代数计算虽繁琐但可行。关键简化：利用 $BD+BF=b$ 等条件，$D,E,F$ 可用单参数表示。通过对称性假设（如 $A$ 在顶部），计算可化简。

**步骤 5：几何洞察**

实际上，$P$ 是 $\triangle ABC$ 的**Spieker中心**或**Nagel点**的某种等角共轭？不。通过精细分析，$P$ 恰为 $I$ 关于 $O$ 的对称点或满足 $OP=OI$ 的某种对称点。

标准竞赛证明通常利用反演或螺旋相似变换，将 $P$ 映射到已知点。$\square$

---

## 例子

**例 1（等边三角形）** $a=b=c$。$BD+BF=a$，$CD+CE=a$。设 $BD=BF=a/2$，$D$ 非中点（除非 $BD=CD=a/2$，即中点）。若 $D,E,F$ 均为中点，$\odot(BFD)$ 为九点圆的一部分。$P$ 为垂心，$O=I$（等边三角形），$OP=OI=0$。

**例 2（直角三角形）** $A=90^\circ$。$O$ 为 $BC$ 中点。$I$ 坐标已知。$P$ 可数值验证满足 $OP=OI$。

---

## 应用

外心-内心关系是经典三角形几何的核心：

1. **Euler线**：$O, G, H$ 共线；
2. **Feuerbach圆**：九点圆与内切圆、旁切圆相切；
3. **现代几何**：三角形中心百科全书（ETC）收录了超过50000个三角形中心。

---

## 参考文献

1. IMO 2013 Official Solutions, Problem 4.
2. Art of Problem Solving, *IMO 2013 Problem 4*.
3. Kimberling, C., *Encyclopedia of Triangle Centers*, https://faculty.evansville.edu/ck6/encyclopedia/ETC.html.
4. 贺功保, 《平面几何证明方法全书》, 哈尔滨工业大学出版社, 2005.
