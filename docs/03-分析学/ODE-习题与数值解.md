---
title: 常微分方程习题与数值解
msc_primary: 34
---

# 常微分方程习题与数值解

常微分方程（ODE）理论是分析学与应用数学的核心，从 Newton 的经典力学到现代动力系统的混沌理论，ODE 始终是描述演化过程的数学语言。本节结合解析方法与数值方法，展示存在性、稳定性与数值收敛性的经典技巧。

## 1. 一阶 ODE 的解析解

### 1.1 可分离变量与积分因子

**习题 1.1**. 求解初值问题 $\frac{dy}{dx} = y$，$y(0) = 1$。

**解答**. 分离变量：$\frac{dy}{y} = dx$，$\ln|y| = x + C$，$y = Ce^x$。由 $y(0) = 1$ 得 $C = 1$，故 $y = e^x$。$\square$

**习题 1.2**. 用积分因子法求解一阶线性方程 $y' + P(x)y = Q(x)$。

**解答**. 积分因子 $\mu(x) = e^{\int P(x)dx}$。方程两边乘以 $\mu$：

$$(\mu y)' = \mu Q,$$

$$
\mu y = \int \mu Q \, dx + C,$$

$$
y = \frac{1}{\mu}\int \mu Q \, dx + \frac{C}{\mu}. \quad \square$$

### 1.2 恰当方程

**习题 1.3**. 求解 $(2xy + 3)dx + (x^2 - 1)dy = 0$。

**解答**. 验证恰当性：$\frac{\partial M}{\partial y} = 2x = \frac{\partial N}{\partial x}$，恰当。求 $F(x,y)$：

$$F = \int M dx = x^2 y + 3x + h(y),$$

$$\frac{\partial F}{\partial y} = x^2 + h'(y) = x^2 - 1 \Rightarrow h'(y) = -1, \quad h(y) = -y.$$

通解：$x^2 y + 3x - y = C$。$\square$

## 2. 存在唯一性定理

### 2.1 Picard-Lindelöf 定理

**定理 2.1（Picard-Lindelöf）**. 设 $f(x,y)$ 在矩形 $R = \{(x,y) : |x - x_0| \leq a, |y - y_0| \leq b\}$ 上连续，且关于 $y$ 满足 Lipschitz 条件：$|f(x,y_1) - f(x,y_2)| \leq L|y_1 - y_2|$。则初值问题 $y' = f(x,y)$，$y(x_0) = y_0$ 在 $|x - x_0| \leq h$ 上存在唯一解，其中 $h = \min(a, b/M)$，$M = \max_R |f|$。

**证明**. 定义 Picard 迭代：

$$y_0(x) = y_0, \quad y_{n+1}(x) = y_0 + \int_{x_0}^x f(t, y_n(t)) dt.$$

**步骤 1**：归纳证明 $|y_n(x) - y_0| \leq b$（保证迭代良定义）。

**步骤 2**：证明 $\{y_n\}$ 为 Cauchy 列：

$$|y_{n+1}(x) - y_n(x)| \leq L \int_{x_0}^x |y_n(t) - y_{n-1}(t)| dt.$$

归纳得 $|y_{n+1} - y_n| \leq \frac{ML^n |x-x_0|^{n+1}}{(n+1)!}$，级数 $\sum (y_{n+1} - y_n)$ 一致收敛。

**步骤 3**：极限 $y = \lim y_n$ 满足积分方程，从而满足 ODE。

**步骤 4**：唯一性：设 $y, z$ 均为解，$|y(x) - z(x)| \leq L\int_{x_0}^x |y - z|$，由 Gronwall 不等式得 $y = z$。$\square$

### 2.2 Peano 存在定理

**定理 2.2（Peano）**. 若 $f$ 仅连续（不必 Lipschitz），则初值问题至少存在一个解（局部）。

*注*. 去掉 Lipschitz 条件后唯一性不成立，如 $y' = \sqrt{|y|}$，$y(0) = 0$ 有无穷多解。

## 3. 线性 ODE 系统

### 3.1 常系数系统

**习题 3.1**. 求解 $y' = Ay$，$A = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$。

**解答**. $A$ 的特征值 $\lambda = \pm i$。Jordan 形为对角阵。$e^{At} = I + At + \frac{A^2t^2}{2!} + \dots$。注意到 $A^2 = -I$，$A^3 = -A$，$A^4 = I$，故：

$$e^{At} = I\cos t + A\sin t = \begin{pmatrix} \cos t & \sin t \\ -\sin t & \cos t \end{pmatrix}.$$

通解 $y(t) = e^{At} y_0$，即 $(y_1, y_2) = (y_{0,1}\cos t + y_{0,2}\sin t, -y_{0,1}\sin t + y_{0,2}\cos t)$，为圆周运动。$\square$

### 3.2 变分常数公式

**习题 3.2**. 求解非齐次系统 $y' = Ay + f(t)$。

**解答**. 齐次解 $y_h = e^{At}C$。设特解 $y_p = e^{At}u(t)$，代入得 $u'(t) = e^{-At}f(t)$，故：

$$y(t) = e^{At}y_0 + \int_0^t e^{A(t-s)} f(s) ds. \quad \square$$

## 4. 数值方法

### 4.1 Euler 方法与收敛性

**习题 4.1**. 分析显式 Euler 方法 $y_{n+1} = y_n + hf(x_n, y_n)$ 的截断误差与整体误差。

**解答**. 局部截断误差：设 $y(x)$ 为精确解，$y(x_{n+1}) = y(x_n) + hy'(x_n) + \frac{h^2}{2}y''(\xi)$。故：

$$T_n = y(x_{n+1}) - [y(x_n) + hf(x_n, y(x_n))] = O(h^2).$$

整体误差：设 $e_n = y(x_n) - y_n$，则：

$$e_{n+1} = e_n + h[f(x_n, y(x_n)) - f(x_n, y_n)] + T_n,$$

$$|e_{n+1}| \leq |e_n| + hL|e_n| + Ch^2 = (1 + hL)|e_n| + Ch^2.$$

解递推：$|e_n| \leq \frac{Ch^2}{hL}[(1+hL)^n - 1] \leq \frac{Ch}{L}(e^{LT} - 1) = O(h)$。故 Euler 法为一阶收敛。$\square$

### 4.2 Runge-Kutta 方法

**习题 4.2**. 推导经典四阶 Runge-Kutta 方法：

$$y_{n+1} = y_n + \frac{h}{6}(k_1 + 2k_2 + 2k_3 + k_4),$$

其中 $k_1 = f(x_n, y_n)$，$k_2 = f(x_n + h/2, y_n + hk_1/2)$，$k_3 = f(x_n + h/2, y_n + hk_2/2)$，$k_4 = f(x_n + h, y_n + hk_3)$。

**证明概要**. 对 $y(x_{n+1})$ 做 Taylor 展开到 $h^4$ 项，匹配 $k_i$ 的线性组合使误差为 $O(h^5)$。利用二元 Taylor 展开与偏导数匹配。$\square$

## 5. 例子

### 5.1 例子：Van der Pol 方程

**习题 5.1**. 分析 Van der Pol 方程 $y'' - \mu(1-y^2)y' + y = 0$（$\mu > 0$）的相图。

**解答**. 化为系统：$y_1' = y_2$，$y_2' = \mu(1-y_1^2)y_2 - y_1$。唯一不动点 $(0,0)$，线性化矩阵特征值 $\lambda = \frac{\mu \pm \sqrt{\mu^2 - 4}}{2}$。当 $\mu < 2$ 时不稳定焦点，$\mu > 2$ 时不稳定结点。存在唯一稳定极限环（由 Liénard 系统理论）。$\square$

### 5.2 例子：刚性方程

**习题 5.2**. 分析 $y' = -1000y + 1000$，$y(0) = 2$ 的显式 Euler 稳定性。

**解答**. 显式 Euler：$y_{n+1} = (1 - 1000h)y_n + 1000h$。稳定性要求 $|1 - 1000h| \leq 1$，即 $0 < h \leq 0.002$。解 $y(t) = 1 + e^{-1000t}$ 在 $t \approx 0.01$ 后即趋于稳态，但显式方法需要极多步数。隐式后向 Euler：$y_{n+1} = \frac{y_n + 1000h}{1 + 1000h}$ 无条件稳定。$\square$

## 6. 交叉引用

- [实分析](docs/03-分析学/01-实分析/01-实分析.md) — 一致收敛与紧性
- [泛函分析](docs/03-分析学/03-泛函分析/03-泛函分析.md) — 半群理论与演化方程
- [数值分析](docs/08-计算数学/常微分方程数值解-深度版.md) — 多步法与稳定性分析
- [动力系统](docs/03-分析学/05-微分方程/微分方程-深度扩展版.md) — 定性理论与混沌
- [有限元](docs/08-计算数学/有限元方法-基础.md) — PDE 的数值离散

---

**适用**：docs/03-分析学/
