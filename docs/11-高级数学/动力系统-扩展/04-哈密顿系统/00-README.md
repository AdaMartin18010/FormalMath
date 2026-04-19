---
msc_primary: 00

  - 00A99
title: 哈密顿系统
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 哈密顿系统

哈密顿系统描述能量守恒的经典力学系统，是动力系统中最优美、最深刻的分支之一，连接微分几何、辛拓扑与可积系统理论。

## 1. 哈密顿方程

**定义 1.1（哈密顿量）**. $H: T^*Q \to \mathbb{R}$，通常为动能加势能 $H(q,p) = \frac{1}{2}p^TM^{-1}p + V(q)$。

**定义 1.2（哈密顿方程）**.

$$\dot{q}^i = \frac{\partial H}{\partial p_i}, \quad \dot{p}_i = -\frac{\partial H}{\partial q^i}.$$

## 2. Liouville 定理

**定理 2.1（Liouville）**. 哈密顿流保持相空间体积。

*证明*. 哈密顿向量场散度 $\nabla \cdot X_H = \sum_i (\frac{\partial^2 H}{\partial q^i \partial p_i} - \frac{\partial^2 H}{\partial p_i \partial q^i}) = 0$。$\square$

## 3. 可积系统

**定义 3.1（完全可积）**. $2n$ 维哈密顿系统完全可积，若存在 $n$ 个互相对合的独立首次积分 $F_1, \dots, F_n$（$\{F_i, F_j\} = 0$）。

**定理 3.2（Liouville-Arnold）**. 完全可积系统的紧等能面为环面，运动为准周期。

## 4. 例子

### 4.1 例子：谐振子

$H = \frac{1}{2}(p^2 + q^2)$。解为 $q(t) = A\cos(t+\phi)$，$p(t) = -A\sin(t+\phi)$。

### 4.2 例子：Kepler 问题

$H = \frac{p^2}{2m} - \frac{k}{r}$。轨道为椭圆、抛物线或双曲线（由能量决定）。

## 5. 交叉引用

- [辛几何](docs/04-几何与拓扑/辛几何-基础.md) — 辛结构与 Hamilton 力学
- [定性理论](docs/11-高级数学/动力系统-扩展/01-常微分方程定性理论/00-README.md) — ODE 定性理论
- [拓扑系统](docs/11-高级数学/动力系统-扩展/02-拓扑动力系统/00-README.md) — 拓扑动力系统
- [光滑系统](docs/11-高级数学/动力系统-扩展/03-光滑动力系统/00-README.md) — 光滑动力系统

---

**适用**：docs/11-高级数学/
