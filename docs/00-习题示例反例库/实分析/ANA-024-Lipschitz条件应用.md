---
msc_primary: 26

  - 26A16
exercise_id: ANA-024
title: Lipschitz条件应用
difficulty: 3
type: PRF
topic: 实分析
subtopic: 连续性应用
source:
  course: MIT 18.100A
  chapter: "4.3"
  original: true
processed_at: '2026-04-09'
---

# ANA-024: Lipschitz条件应用

**题号**: ANA-024
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 证明型 (PRF)
**来源**: MIT 18.100A Chapter 4.3
**主题**: Lipschitz连续性与应用

---

## 题目

**(a)** 证明 $f(x) = |x|$ 在 $\mathbb{R}$ 上是Lipschitz连续的，并求最佳Lipschitz常数

**(b)** 设 $f: [a,b] \to \mathbb{R}$ 可导，且 $|f'(x)| \leq M$ 对所有 $x \in [a,b]$ 成立。证明 $f$ 是Lipschitz连续的，常数为 $M$

**(c)** 设 $f(x) = \sqrt{x}$ 在 $[0,1]$ 上。证明 $f$ 不是Lipschitz连续的，但是Hölder连续的（指数为 $1/2$）

---

## 解答

### 回顾：Lipschitz连续

$f$ 在区间 $I$ 上是**Lipschitz连续**的，如果存在常数 $L > 0$ 使得：
$$|f(x) - f(y)| \leq L|x-y|, \quad \forall x,y \in I$$

最小的这样的 $L$ 称为**最佳Lipschitz常数**。

---

### (a) 绝对值函数的Lipschitz性质

**证明**:

对任意 $x, y \in \mathbb{R}$：
$$||x| - |y|| \leq |x - y|$$

（由三角不等式的变形：$|x| = |(x-y) + y| \leq |x-y| + |y|$）

因此 $f(x) = |x|$ 是Lipschitz连续的，$L = 1$ 是一个Lipschitz常数。

**最佳常数**: $L = 1$ 是最佳的。

取 $x = 1, y = 0$：
$$||1| - |0|| = 1 = 1 \cdot |1 - 0|$$

因此最佳Lipschitz常数为 $1$。 $\square$

---

### (b) 导数有界蕴含Lipschitz连续

**证明**:

对任意 $x, y \in [a,b]$，$x \neq y$。

由中值定理，存在 $\xi$ 在 $x$ 与 $y$ 之间，使得：
$$f(x) - f(y) = f'(\xi)(x - y)$$

因此：
$$|f(x) - f(y)| = |f'(\xi)| \cdot |x - y| \leq M|x - y|$$

所以 $f$ 是Lipschitz连续的，常数为 $M$。 $\square$

---

### (c) 平方根函数的Hölder连续性

**证明**:

**不是Lipschitz连续**:

假设存在 $L > 0$ 使得对所有 $x, y \in [0,1]$：
$$|\sqrt{x} - \sqrt{y}| \leq L|x - y|$$

取 $y = 0$，$x > 0$：
$$\sqrt{x} \leq Lx \Rightarrow \frac{1}{\sqrt{x}} \leq L$$

当 $x \to 0^+$，左边趋于 $+\infty$，矛盾。

因此 $f$ 在 $[0,1]$ 上不是Lipschitz连续的。

**是Hölder连续的（指数 $1/2$）**:

对 $x, y \in [0,1]$：
$$|\sqrt{x} - \sqrt{y}| = \frac{|x-y|}{\sqrt{x} + \sqrt{y}}$$

不妨设 $x > y \geq 0$。令 $x = y + h$，$h > 0$：
$$\frac{h}{\sqrt{y+h} + \sqrt{y}} \leq \frac{h}{\sqrt{h}} = \sqrt{h} = |x-y|^{1/2}$$

因此：
$$|\sqrt{x} - \sqrt{y}| \leq |x-y|^{1/2}$$

$f$ 是Hölder连续的，指数为 $\alpha = 1/2$，常数为 $1$。 $\square$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 三角不等式 | (a) | $||x|-|y|| \leq |x-y|$ |
| 中值定理 | (b) | 导数控制函数变化 |
| 反证法 | (c) | 假设Lipschitz导出矛盾 |
| 有理化 | (c) | 处理根式差的常用技巧 |

### 关键洞察

1. **Lipschitz vs 可导**: Lipschitz连续不一定可导（如 $|x|$）
2. **导数有界**: 可导且导数有界 $\Rightarrow$ Lipschitz
3. **Hölder连续**: 比Lipschitz弱但比一致连续强的条件

---

## 常见错误

### 错误1: 混淆Lipschitz与可导

❌ **错误做法**:
> 认为Lipschitz连续一定可导

✅ **正确理解**:
> $|x|$ Lipschitz连续但在0不可导

### 错误2: 忽略定义域端点

❌ **错误做法**:
> 在(c)中，不考虑$x=0$的特殊性

✅ **正确做法**:
> 端点处的奇异性是关键

### 错误3: 最佳常数计算错误

❌ **错误做法**:
> 认为$|x|$的Lipschitz常数可以小于1

✅ **正确做法**:
> 通过具体点验证常数的最佳性

---

## 变式练习

### 变式1（难度⭐⭐⭐）

证明 $f(x) = x^2$ 在 $[0,1]$ 上是Lipschitz连续的，但在 $[0,+\infty)$ 上不是

### 变式2（难度⭐⭐⭐⭐）

设 $f: [0,1] \to \mathbb{R}$ 满足 $|f(x) - f(y)| \leq M|x-y|^\alpha$，其中 $0 < \alpha \leq 1$。

证明若 $\alpha > 1$，则 $f$ 为常数

**提示**: 考虑 $n$ 等分，估计 $|f(1) - f(0)|$

### 变式3（难度⭐⭐⭐⭐⭐）

证明：$f$ 在 $[a,b]$ 上Lipschitz连续当且仅当 $f$ 是绝对连续且 $|f'| \leq M$ a.e.

**提示**: 利用Lebesgue积分的性质

---

## 相关概念

| 概念 | 关系 |
|------|------|
| 绝对连续 | 比Lipschitz弱但比一致连续强 |
| Rademacher定理 | Lipschitz函数几乎处处可导 |
| Hölder空间 | 函数空间的分类 |

**标签**: #Lipschitz条件 #Hölder连续 #中值定理 #实分析 #MIT-18.100A
