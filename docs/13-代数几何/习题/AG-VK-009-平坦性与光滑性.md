---
title: 平坦性与光滑性
msc_primary: 14-01
msc_secondary:
- 14B25
- 14D15
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 22-25
topic: 形变理论基础
exercise_type: TEC (技术型)
difficulty: ⭐⭐⭐⭐
importance: ★★
---

# AG-VK-009: 平坦性与光滑性

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 22-25: 平坦性与光滑性 |
| **对应FOAG习题** | 22.3.F, 23.4.H, 25.3.C |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $f: X \to Y$ 是概形的态射，$\mathcal{F}$ 是 $X$ 上的凝聚层。

**(a)** **平坦性的局部判据**：

设 $Y$ 是整Noether概形，$f: X \to Y$ 是有限型态射。证明：$\mathcal{F}$ 在 $Y$ 上平坦当且仅当Hilbert多项式 $P_y(t) = \chi(X_y, \mathcal{F}_y(t))$ 在 $y \in Y$ 上局部常值。

**(b)** **光滑性的Jacobian判据**：

设 $X = \operatorname{Spec} k[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$ 是有限型 $k$-概形，$p \in X$ 是闭点。证明：$X$ 在 $p$ 处光滑当且仅当Jacobian矩阵：
$$J = \left(\frac{\partial f_i}{\partial x_j}(p)\right)_{r \times n}$$

在 $p$ 处有秩 $r$（即在 $p$ 处是满射）。

**(c)** **形式光滑性**：

设 $f: X \to Y$ 是局部有限展示态射。证明：$f$ 是形式光滑的当且仅当 $f$ 是光滑的。

（形式光滑性：对任意仿射概形 $Z$ 和幂零理想 $I \subset \mathcal{O}_Z$，映射 $X(Z) \to X(Z/I)$ 是满射）

---

## 解题思路

### 思路概述

本题涉及**形变理论的基础**：
- **平坦性** - 连续变化的代数条件
- **光滑性** - 微分几何的推广
- **形式光滑性** - 无穷小提升性质

### 概念层级

```
态射的性质强度

平坦 ←──── 光滑 ←──── 平展
 │          │           │
 │          │           │
 ▼          ▼           ▼
连续变化    微分流形    局部同构
无跳跃     局部标准形   覆叠映射
```

---

## 详细解答

### (a) 平坦性的Hilbert多项式判据

**定理**（Grothendieck）：设 $Y$ 是整Noether概形，$f: X \to Y$ 是投射态射，$\mathcal{F}$ 是 $X$ 上的凝聚层。

则以下等价：
1. $\mathcal{F}$ 在 $Y$ 上平坦
2. Hilbert多项式 $y \mapsto P_{\mathcal{F}_y}(t)$ 是局部常值函数

**证明概要**：

**$(\Rightarrow)$** 平坦 $\Rightarrow$ 多项式常值。

这是半连续性定理的推论。平坦性保证上同调的跳跃被控制。

具体地，设 $y \in Y$，考虑形式完备化。平坦性保证：
$$H^i(X_y, \mathcal{F}_y(n)) = H^i(X, \mathcal{F}(n)) \otimes k(y)$$

对所有 $n$。所以Hilbert多项式在 $y$ 附近不变。

**$(\Leftarrow)$** 多项式常值 $\Rightarrow$ 平坦。

这是更深刻的结果。需要证明：若Hilbert多项式不变，则 $\mathcal{F}$ 是局部自由的（作为 $\mathcal{O}_Y$-模）。

由有限性定理，$R^if_*\mathcal{F}(n)$ 是凝聚层。

Hilbert多项式不变 $\Rightarrow$ $h^i$ 的跳跃被抵消 $\Rightarrow$ 由Grauert定理，$f_*\mathcal{F}(n)$ 局部自由（$n \gg 0$）。

这推出平坦性。∎

### (b) 光滑性的Jacobian判据

**定理**：设 $X = \operatorname{Spec} k[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$，$p \in X$。

$X$ 在 $p$ 处光滑 $\Leftrightarrow$ $\operatorname{rank} J(p) = r$。

**证明**：

**准备**：设 $A = k[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$，$\mathfrak{m}$ 是对应于 $p$ 的极大理想。

**步骤1**: 光滑性的定义。

$X$ 在 $p$ 处光滑 $\Leftrightarrow$：
1. $\Omega_{A/k}$ 在 $p$ 处局部自由
2. $\dim_k \Omega_{A/k} \otimes k(p) = \dim_p X$

**步骤2**: 计算Kähler微分。

$$0 \to (f_1, \ldots, f_r)/(f)^2 \to \Omega_{k[x]/k} \otimes A \to \Omega_{A/k} \to 0$$

在 $p$ 处，这是：
$$k^r \xrightarrow{J(p)} k^n \to \Omega_{A/k} \otimes k(p) \to 0$$

所以：
$$\dim \Omega_{A/k} \otimes k(p) = n - \operatorname{rank} J(p)$$

**步骤3**: 维数条件。

$\dim_p X = n - r$（若Jacobian条件满足，这是光滑性的维数条件）。

所以：$\operatorname{rank} J(p) = r$ $\Leftrightarrow$ $\dim \Omega = n - r = \dim X$。

∎

### (c) 形式光滑性

**定义**：$f: X \to Y$ 是形式光滑的，如果对任意仿射 $Z$ 和幂零理想 $I \subset \mathcal{O}_Z$：
$$\operatorname{Hom}(Z, X) \to \operatorname{Hom}(Z/I, X)$$

在纤维积上是满射。

**定理**（Grothendieck）：对局部有限展示态射，形式光滑 $\Leftrightarrow$ 光滑。

**证明概要**：

**$(\Rightarrow)$** 形式光滑 $\Rightarrow$ 光滑。

需证明：
1. 平坦性
2. 几何纤维光滑

**平坦性**：用形式光滑性的无穷小提升性质，可以证明 $\operatorname{Tor}$ 消失，即平坦。

**几何纤维**：设 $y \in Y$，考虑 $X_y = X \times_Y \operatorname{Spec} k(y)$。

形式光滑性在基变换下保持，所以 $X_y \to \operatorname{Spec} k(y)$ 形式光滑。

对域上的概形，形式光滑 $\Leftrightarrow$ 几何正则 $\Leftrightarrow$ 光滑（对有限型概形）。

**$(\Leftarrow)$** 光滑 $\Rightarrow$ 形式光滑。

这是光滑性的标准性质。光滑映射有étale局部标准形：

$$X \xleftarrow{\text{étale}} \mathbb{A}^n_Y \to Y$$

étale映射是形式平展的（更一般地是形式光滑的），而 $\mathbb{A}^n_Y \to Y$ 显然是形式光滑的。

∎

---

## 关键概念

### 平坦性

**代数定义**：$A$-模 $M$ 是平坦的，如果 $-\otimes_A M$ 是正合函子。

**几何意义**：纤维"连续变化"，无"跳跃"。

**例子**：
- 自由模是平坦的
- 投射模是平坦的
- $\mathbb{Z}/2$ 不是 $\mathbb{Z}$-平坦的

### 光滑性

**等价条件**：局部有限展示态射 $f: X \to Y$ 光滑当且仅当：
1. 平坦
2. 几何纤维是正则局部环
3. 形式光滑
4. Jacobian条件（局部）

### 形式性质

| 性质 | 无穷小提升 |
|------|-----------|
| 形式平展 | 唯一提升 |
| 形式光滑 | 存在提升 |
| 形式无 ramification | 最多一个提升 |

---

## 重要应用

### 形变理论

光滑性是形变理论的基础。若 $X$ 在 $k$ 上光滑，则：

一阶形变（在 $k[\epsilon]/\epsilon^2$ 上）由 $H^1(X, T_X)$ 分类。

障碍在 $H^2(X, T_X)$。

---

## 变式练习

### 变式 1: 平展态射

证明：$f$ 是平展的 $\Leftrightarrow$ 形式平展 + 局部有限展示。

### 变式 2: 平坦性的Tor判据

证明：$M$ 是 $A$-平坦的 $\Leftrightarrow$ $\operatorname{Tor}^A_1(M, N) = 0$ 对所有 $N$。

### 变式 3: 光滑性的维数判据

证明：若 $X$ 在 $k$ 上有限型，则 $X$ 光滑 $\Leftrightarrow$ $\Omega_{X/k}$ 局部自由且秩等于维数。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为平坦意味着光滑 | 平坦是更弱的条件 |
| 混淆形式光滑和光滑 | 对有限展示态射等价，但一般不同 |
| 忽略Jacobian的秩条件 | 需要满秩，不只是极大秩 |

---

## 学习建议

1. **理解平坦性的几何**：平坦族"连续变化"
2. **练习Jacobian计算**：验证具体例子的光滑性
3. **学习形变理论**：形式光滑性是形变理论的语言

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-009-平坦性与光滑性.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
