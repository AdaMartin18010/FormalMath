---
msc_primary: 00

  - 00A99
title: 常微分方程定性理论
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 常微分方程定性理论

定性理论研究微分方程解的长期行为，不依赖于显式求解方程，而是通过分析相空间的几何结构来理解系统动力学。

## 1. 基础概念

### 1.1 平衡点与稳定性

**定义 1.1（平衡点）**. $x^*$ 为系统 $\dot{x} = f(x)$ 的平衡点，若 $f(x^*) = 0$。

**定义 1.2（Lyapunov 稳定）**. $x^*$ Lyapunov 稳定，若对任意 $\epsilon > 0$，存在 $\delta > 0$ 使 $\|x(0) - x^*\| < \delta$ 蕴含 $\|x(t) - x^*\| < \epsilon$（$t \geq 0$）。

**定义 1.3（渐近稳定）**. Lyapunov 稳定且 $x(t) \to x^*$（$t \to \infty$）。

### 1.2 线性化

**定理 1.4（Hartman-Grobman）**. 若 $Df(x^*)$ 无实部为零的特征值，则系统在 $x^*$ 附近拓扑共轭于其线性化。

## 2. Lyapunov 方法

**定理 2.1（Lyapunov 直接法）**. 设 $V$ 为 $x^*$ 邻域上的 $C^1$ 函数，$V(x^*) = 0$，$V(x) > 0$（$x \neq x^*$）。若 $\dot{V} = \nabla V \cdot f \leq 0$，则 $x^*$ Lyapunov 稳定；若 $\dot{V} < 0$（$x \neq x^*$），则渐近稳定。

## 3. Poincaré-Bendixson 定理

**定理 3.1**. 设 $\Omega \subset \mathbb{R}^2$ 为正不变集，不含平衡点。则 $\Omega$ 中存在周期轨道。

## 4. 例子

### 4.1 例子：Van der Pol 振子

$$\ddot{x} - \mu(1-x^2)\dot{x} + x = 0$$

对 $\mu > 0$，存在唯一稳定极限环。

### 4.2 例子：Lorenz 系统

$$\begin{cases} \dot{x} = \sigma(y-x) \\ \dot{y} = x(\rho-z) - y \\ \dot{z} = xy - \beta z \end{cases}$$

对 $\sigma=10, \beta=8/3, \rho=28$，系统呈现混沌行为（奇怪吸引子）。

## 5. 交叉引用

- [ODE](docs/03-分析学/ODE-习题与数值解.md) — 常微分方程基础
- [动力系统](docs/11-高级数学/动力系统-扩展/02-拓扑动力系统/00-README.md) — 拓扑动力系统
- [混沌](docs/11-高级数学/动力系统-扩展/05-复动力系统/00-README.md) — 复动力系统
- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 流形上的向量场

---

**适用**：docs/11-高级数学/
