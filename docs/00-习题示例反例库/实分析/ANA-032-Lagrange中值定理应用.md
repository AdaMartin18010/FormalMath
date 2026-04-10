---
msc_primary: 26A06
exercise_id: ANA-032
title: Lagrange中值定理应用
difficulty: 3
type: APP
topic: 实分析
subtopic: 微分中值定理
source:
  course: MIT 18.100A
  chapter: "5.2"
  original: true
processed_at: '2026-04-09'
---

# ANA-032: Lagrange中值定理应用

**题号**: ANA-032
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 应用型 (APP)
**来源**: MIT 18.100A Chapter 5.2
**主题**: Lagrange中值定理(LMVT)的经典应用

---

## 题目

**(a)** 设 $f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导。证明存在 $c \in (a,b)$ 使得
$$f'(c) = \frac{f(b) - f(a)}{b - a}$$

**(b)** 设 $f$ 在 $[0,1]$ 上可导，$|f'(x)| \leq M$。估计 $|f(1) - f(0)|$

**(c)** 证明：$|\sin x - \sin y| \leq |x - y|$ 对所有 $x, y \in \mathbb{R}$ 成立

---

## 解答

### (a) Lagrange中值定理（证明）

**证明**:

构造辅助函数：
$$g(x) = f(x) - \frac{f(b) - f(a)}{b - a}(x - a)$$

**验证Rolle条件**:
- $g(a) = f(a)$
- $g(b) = f(b) - (f(b) - f(a)) = f(a)$

所以 $g(a) = g(b) = f(a)$。

由Rolle定理，存在 $c \in (a,b)$ 使得 $g'(c) = 0$。

**计算**:
$$g'(x) = f'(x) - \frac{f(b) - f(a)}{b - a}$$

因此：
$$f'(c) = \frac{f(b) - f(a)}{b - a} \quad \square$$

---

### (b) 导数有界的估计

**解**:

由Lagrange中值定理，存在 $c \in (0,1)$ 使得：
$$f(1) - f(0) = f'(c)(1 - 0) = f'(c)$$

因此：
$$|f(1) - f(0)| = |f'(c)| \leq M$$

即 $|f(1) - f(0)| \leq M$。 $\square$

---

### (c) 三角函数不等式

**证明**:

设 $x < y$（$x = y$ 时显然）。

由LMVT，存在 $c \in (x,y)$ 使得：
$$\frac{\sin y - \sin x}{y - x} = \cos c$$

因此：
$$\sin y - \sin x = (y - x)\cos c$$

取绝对值：
$$|\sin y - \sin x| = |y - x| \cdot |\cos c| \leq |y - x|$$

即 $|\sin x - \sin y| \leq |x - y|$。 $\square$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 线性修正 | (a) | 构造$g$使端点值相等 |
| 导数控制 | (b) | 用$|f'|$的界估计函数差 |
| 中值等式 | (c) | 将函数差表示为导数乘区间长 |
| 三角函数 | (c) | $|\cos c| \leq 1$是关键 |

### 关键洞察

1. **LMVT的核心**: 平均变化率 = 某点瞬时变化率
2. **估计工具**: 用$|f'|$的界估计函数变化
3. **Lipschitz条件**: $|f'| \leq M$ 蕴含 $M$-Lipschitz

---

## 常见错误

### 错误1: 区间错误

❌ **错误做法**:
> 在(a)中，直接说$f'(c) = f(b) - f(a)$（遗漏分母$b-a$）

✅ **正确做法**:
> 记住是平均变化率 $\frac{f(b)-f(a)}{b-a}$

### 错误2: 忽略中间点存在性

❌ **错误做法**:
> 断言$f'(c)$对所有$c$有界

✅ **正确做法**:
> LMVT只保证某点$c$的存在，不是任意点

### 错误3: 开闭区间混淆

❌ **错误做法**:
> 在$c \in (a,b)$处讨论$f'$的连续性

✅ **正确做法**:
> 只需要$f'$在$(a,b)$存在，不需要连续

---

## 变式练习

### 变式1（难度⭐⭐⭐）

证明：$|\arctan x - \arctan y| \leq |x - y|$，且等号仅在$x = y$时成立

### 变式2（难度⭐⭐⭐⭐）

设 $f$ 在 $[a,b]$ 上二阶可导，$f(a) = f(b) = 0$，$|f''(x)| \leq M$。证明
$$|f(x)| \leq \frac{M(b-a)^2}{8}, \quad \forall x \in [a,b]$$

### 变式3（难度⭐⭐⭐⭐）

设 $f$ 在 $[0,1]$ 上可导，$f(0) = 0$，$f(1) = 1$。证明存在不同的 $c_1, c_2 \in (0,1)$ 使得
$$\frac{1}{f'(c_1)} + \frac{1}{f'(c_2)} = 2$$

**提示**: 利用中间值$f(1/2) = 1/2$或其他值

---

## 相关概念

| 概念 | 关系 |
|------|------|
| Cauchy中值定理 | LMVT的推广 |
| Taylor定理 | LMVT的高阶推广 |
| 凸函数 | LMVT在凸性中的应用 |

**标签**: #Lagrange中值定理 #LMVT #导数估计 #实分析 #MIT-18.100A
