---
title: 常微分方程习题与数值解
msc_primary: 34
---

# 常微分方程习题与数值解

常微分方程（ODE）理论是分析学与应用数学的核心，从 Newton 的经典力学到现代动力系统的混沌理论，ODE 始终是描述演化过程的数学语言。本节结合解析方法与数值方法，展示存在性、稳定性与数值收敛性的经典技巧。

## 1. 存在性与唯一性理论

### 1.1 Picard-Lindelöf 定理

**定义 1.1（Lipschitz 条件）**. 函数 $f: D \subseteq \mathbb{R}^{n+1} \to \mathbb{R}^n$ 关于 $y$ 满足 Lipschitz 条件，若存在 $L > 0$ 使得：

$$\|f(t, y_1) - f(t, y_2)\| \leq L \|y_1 - y_2\|$$

对所有 $(t, y_1), (t, y_2) \in D$ 成立。

**定理 1.2（Picard-Lindelöf）**. 设 $f$ 在矩形 $R = \{(t,y) : |t-t_0| \leq a, \|y-y_0\| \leq b\}$ 上连续且关于 $y$ 满足 Lipschitz 条件。则初值问题

$$y' = f(t, y), \quad y(t_0) = y_0$$

在 $|t - t_0| \leq \min(a, b/M)$ 上存在唯一解，其中 $M = \max_R \|f\|$。

*证明*. 将初值问题化为积分方程：

$$y(t) = y_0 + \int_{t_0}^t f(s, y(s)) ds.$$

定义 Picard 迭代：$y_0(t) = y_0$，$y_{n+1}(t) = y_0 + \int_{t_0}^t f(s, y_n(s)) ds$。

归纳证明 $y_n$ 停留在矩形内：$\|y_{n+1}(t) - y_0\| \leq M|t-t_0| \leq b$。

证明 $\{y_n\}$ 为 Cauchy 列：

$$\|y_{n+1}(t) - y_n(t)\| \leq L \int_{t_0}^t \|y_n(s) - y_{n-1}(s)\| ds.$$

归纳得 $\|y_{n+1} - y_n\| \leq \frac{ML^n |t-t_0|^{n+1}}{(n+1)!}$，故级数 $\sum (y_{n+1} - y_n)$ 一致收敛。极限 $y$ 满足积分方程。唯一性：设 $y, z$ 均为解，则 $\|y(t) - z(t)\| \leq L\int_{t_0}^t \|y-z\|$，由 Gronwall 不等式得 $y = z$。$\square$

### 1.2 Peano 存在定理

**定理 1.3（Peano）**. 若 $f$ 在 $R$ 上连续（无需 Lipschitz），则初值问题至少存在一个解。

*证明概要*. 构造 Euler 折线：对步长 $h$，定义 $y_h(t_{k+1}) = y_h(t_k) + h f(t_k, y_h(t_k))$，线性插值。由 Arzelà-Ascoli 定理，$\{y_h\}$ 有一致收敛子列，极限满足积分方程。$\square$

## 2. 线性方程组与稳定性

### 2.1 常系数线性系统

**定理 2.1**. 设 $A \in M_n(\mathbb{C})$。方程 $y' = Ay$ 的通解为 $y(t) = e^{At} C$，其中 $e^{At} = \sum_{k=0}^\infty \frac{(At)^k}{k!}$。

*证明*. 级数在任何紧集上一致收敛，逐项微分得 $\frac{d}{dt}e^{At} = A e^{At}$。$\square$

### 2.2 稳定性判据

**定义 2.2（稳定性）**. 系统 $y' = f(y)$ 的平衡点 $y^*$（$f(y^*) = 0$）称为：
- **Lyapunov 稳定**：对任意 $\epsilon > 0$，存在 $\delta > 0$ 使 $\|y(0) - y^*\| < \delta$ 蕴含 $\|y(t) - y^*\| < \epsilon$（$t \geq 0$）；
- **渐近稳定**：Lyapunov 稳定且 $y(t) \to y^*$（$t \to \infty$）。

**定理 2.3（线性化稳定性）**. 设 $f(y^*) = 0$，$A = Df(y^*)$。
- 若 $A$ 的所有特征值实部 $< 0$，则 $y^*$ 渐近稳定；
- 若某特征值实部 $> 0$，则 $y^*$ 不稳定。

## 3. 数值方法

### 3.1 Euler 方法与收敛性

**定义 3.1（显式 Euler）**. $y_{n+1} = y_n + h f(t_n, y_n)$。

**定理 3.2**. 若 $f$ 满足 Lipschitz 条件，则显式 Euler 方法收敛：$\max_n \|y_n - y(t_n)\| \to 0$（$h \to 0$）。

*证明*. 局部截断误差 $\tau_n = y(t_{n+1}) - y(t_n) - h y'(t_n) = O(h^2)$。整体误差 $e_n = y_n - y(t_n)$ 满足：

$$e_{n+1} = e_n + h[f(t_n, y_n) - f(t_n, y(t_n))] - \tau_n,$$

故 $\|e_{n+1}\| \leq (1+hL)\|e_n\| + Ch^2$。递推并利用 $(1+hL)^n \leq e^{nhL} \leq e^{TL}$（$T = nh$）得 $\|e_n\| = O(h)$。$\square$

### 3.2 Runge-Kutta 方法

**定义 3.3（经典 RK4）**. 

$$y_{n+1} = y_n + \frac{h}{6}(k_1 + 2k_2 + 2k_3 + k_4),$$

其中 $k_1 = f(t_n, y_n)$，$k_2 = f(t_n + h/2, y_n + hk_1/2)$，$k_3 = f(t_n + h/2, y_n + hk_2/2)$，$k_4 = f(t_n + h, y_n + hk_3)$。

**定理 3.4**. RK4 的局部截断误差为 $O(h^5)$，整体误差为 $O(h^4)$。

## 4. 例子

### 4.1 例子：单摆方程

单摆方程：$\theta'' + \frac{g}{l}\sin\theta = 0$。令 $\omega = \theta'$，化为一阶系统：

$$\begin{cases} \theta' = \omega \\ \omega' = -\frac{g}{l}\sin\theta \end{cases}$$

平衡点 $(0, 0)$：线性化矩阵 $\begin{pmatrix} 0 & 1 \\ -g/l & 0 \end{pmatrix}$，特征值 $\pm i\sqrt{g/l}$，纯虚数 $
Rightarrow$ 中心（Lyapunov 稳定但非渐近稳定）。

平衡点 $(\pi, 0)$：线性化矩阵 $\begin{pmatrix} 0 & 1 \\ g/l & 0 \end{pmatrix}$，特征值 $\pm \sqrt{g/l}$，一正一负 $
Rightarrow$ 鞍点（不稳定）。

### 4.2 例子：Van der Pol 振子

$$x'' - \mu(1-x^2)x' + x = 0, \quad \mu > 0.$$

化为一阶系统：$x' = y$，$y' = \mu(1-x^2)y - x$。

唯一平衡点 $(0,0)$：线性化特征值 $\lambda = \frac{\mu \pm \sqrt{\mu^2 - 4}}{2}$，实部 $> 0$（$\mu > 0$），故不稳定。数值模拟显示系统存在稳定的极限环。

## 5. 交叉引用

- [实分析](docs/03-分析学/01-实分析/01-实分析.md) — 收敛性与完备性
- [动力系统](docs/11-高级数学/动力系统-扩展/01-常微分方程定性理论/00-README.md) — 定性理论与混沌
- [数值分析](docs/08-计算数学/01-数值分析基础.md) — 数值方法的系统理论
- [泛函分析](docs/03-分析学/03-泛函分析/03-泛函分析.md) — 算子半群与演化方程
- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 流形上的向量场

---

**适用**：docs/03-分析学/
