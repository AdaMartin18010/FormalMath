---
msc_primary: 20A99
msc_secondary:
- 35A99
- 00A99
- 00A99
title: Lotka-Volterra捕食者-猎物模型
processed_at: '2026-04-05'
---
# Lotka-Volterra捕食者-猎物模型

## 应用领域

**学科**: 数学生态学 / 动力系统  
**具体应用**: 生态系统管理、渔业管理、害虫控制、传染病动力学  
**MSC分类**: 92D25 (Population dynamics), 34C25 (Periodic solutions), 37N25 (Dynamical systems in biology)

---

## 数学概念

### 核心数学工具

1. **常微分方程组**: 二元非线性系统
2. **相平面分析**: 轨迹的几何性质
3. **平衡点分析**: 线性化与稳定性
4. **首次积分**: 守恒量
5. **周期轨道**: 闭合轨迹

### 关键定义

- **平衡点**: $\dot{x} = \dot{y} = 0$ 的点
- **Jacobian矩阵**: 线性化矩阵
- **Lyapunov稳定性**: 小扰动下的回归性

---

## 问题描述

### 生态背景

**捕食者-猎物系统**: 
- 猎物（如兔子）：有食物时指数增长
- 捕食者（如狐狸）：依赖猎物生存

**观察现象**:
- 种群周期性振荡
- 捕食者峰值滞后于猎物峰值
- 系统长期共存

### 核心问题

1. 两个物种能否长期共存？
2. 种群数量的周期性如何产生？
3. 环境参数如何影响动态？

---

## 数学模型

### Lotka-Volterra方程

**猎物种群** $x(t)$:

$$\frac{dx}{dt} = \alpha x - \beta x y$$

**捕食者种群** $y(t)$:

$$\frac{dy}{dt} = \delta x y - \gamma y$$

**参数**:
- $\alpha > 0$: 猎物自然增长率
- $\beta > 0$: 捕食率
- $\gamma > 0$: 捕食者死亡率
- $\delta > 0$: 捕食效率（转化为捕食者增长）

### 平衡点分析

**平衡点**: 令 $\dot{x} = \dot{y} = 0$

**平凡平衡点**: $(0, 0)$（灭绝）

**共存平衡点**: $(x^*, y^*) = \left(\frac{\gamma}{\delta}, \frac{\alpha}{\beta}\right)$

**Jacobian矩阵**:

$$J(x, y) = \begin{pmatrix} \alpha - \beta y & -\beta x \\ \delta y & \delta x - \gamma \end{pmatrix}$$

**在共存点的Jacobian**:

$$J(x^*, y^*) = \begin{pmatrix} 0 & -\frac{\beta\gamma}{\delta} \\ \frac{\alpha\delta}{\beta} & 0 \end{pmatrix}$$

**特征值**: $\lambda = \pm i\sqrt{\alpha\gamma}$（纯虚数）

**结论**: 中心型平衡点，周期轨道。

### 首次积分（守恒量）

**构造**:

$$H(x, y) = \delta x - \gamma \ln x + \beta y - \alpha \ln y$$

**性质**: $\frac{dH}{dt} = 0$，即 $H(x, y) = \text{const}$ 沿轨迹。

**相图**: 闭合曲线环绕 $(x^*, y^*)$。

---

## 求解过程

### 步骤1：无量纲化

**尺度变换**:

$$u = \frac{\delta}{\gamma}x, \quad v = \frac{\beta}{\alpha}y, \quad \tau = \sqrt{\alpha\gamma}t$$

**无量纲方程**:

$$\frac{du}{d\tau} = a u(1 - v)$$
$$\frac{dv}{d\tau} = -b v(1 - u)$$

其中 $a = \sqrt{\alpha/\gamma}$, $b = \sqrt{\gamma/\alpha}$。

### 步骤2：数值求解

**欧拉法**（教学用，不稳定）:

$$x_{n+1} = x_n + h(\alpha x_n - \beta x_n y_n)$$
$$y_{n+1} = y_n + h(\delta x_n y_n - \gamma y_n)$$

**改进方法**:
- Runge-Kutta 4阶
- 辛积分器（保持相空间结构）

### 步骤3：平均种群计算

**时间平均**:

$$\bar{x} = \frac{1}{T}\int_0^T x(t) dt, \quad \bar{y} = \frac{1}{T}\int_0^T y(t) dt$$

**定理**: 对任何周期轨道:

$$\bar{x} = x^* = \frac{\gamma}{\delta}, \quad \bar{y} = y^* = \frac{\alpha}{\beta}$$

**证明**: 从 $\frac{1}{x}\frac{dx}{dt} = \alpha - \beta y$，积分一个周期:

$$0 = \ln x(T) - \ln x(0) = \alpha T - \beta \int_0^T y(t) dt$$

因此 $\bar{y} = \frac{\alpha}{\beta}$。同理 $\bar{x} = \frac{\gamma}{\delta}$。 ∎

---

## 结果分析

### 周期振荡特征

| 特征 | 表达式 | 依赖关系 |
|------|--------|----------|
| **周期** | $T \approx 2\pi/\sqrt{\alpha\gamma}$ | 与增长率、死亡率相关 |
| **振幅** | 取决于初始条件 | 大偏离 → 大振幅 |
| **相位差** | 捕食者滞后猎物 ~90° | 固有结构 |

### 模型局限性

| 局限 | 解释 | 改进方向 |
|------|------|----------|
| **中性稳定** | 小扰动产生新轨道，不回归 | Logistic增长修正 |
| **结构不稳定** | 参数微小变化改变定性行为 | 添加密度依赖 |
| **无极限环** | 所有轨道周期但周期不同 | 更复杂的非线性 |

### 改进模型

**Logistic捕食者-猎物模型**:

$$\frac{dx}{dt} = rx\left(1 - \frac{x}{K}\right) - \beta x y$$
$$\frac{dy}{dt} = \delta x y - \gamma y$$

其中 $K$ 是环境容纳量。

**结果**: 可产生稳定焦点（螺旋收敛到平衡）或极限环。

### 实际应用

**渔业管理**:
- MSY（最大可持续产量）分析
- 最优捕捞策略

**生物控制**:
- 引入天敌控制害虫
- 避免过度捕食导致天敌灭绝

---

## 参考资源

### 历史文献

- **Lotka, A.J.** (1925). *Elements of Physical Biology*.
- **Volterra, V.** (1926). "Variazioni e fluttuazioni del numero d'individui in specie animali conviventi". *Mem. Accad. Lincei*.

### 推荐教材

- **Murray, J.D.** *Mathematical Biology I: An Introduction*.
- **Edelstein-Keshet, L.** *Mathematical Models in Biology*.
- **Britton, N.F.** *Essential Mathematical Biology*.

---

**创建日期**: 2026年4月2日  
**最后更新**: 2026年4月2日
