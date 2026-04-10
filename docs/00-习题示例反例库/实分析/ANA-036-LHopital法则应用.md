---
msc_primary: 26A24
exercise_id: ANA-036
title: L'Hôpital法则应用
difficulty: 3
type: CALC
topic: 实分析
subtopic: 微分中值定理
source:
  course: MIT 18.100A
  chapter: "5.2"
  original: true
processed_at: '2026-04-09'
---

# ANA-036: L'Hôpital法则应用

**题号**: ANA-036
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 计算型 (CALC)
**来源**: MIT 18.100A Chapter 5.2
**主题**: L'Hôpital法则及其应用

---

## 题目

**(a)** 叙述L'Hôpital法则（$\frac{0}{0}$ 和 $\frac{\infty}{\infty}$ 型），并用Cauchy中值定理证明 $\frac{0}{0}$ 型

**(b)** 计算 $\displaystyle\lim_{x\to 0} \frac{\tan x - x}{x^3}$

**(c)** 计算 $\displaystyle\lim_{x\to +\infty} \frac{\ln x}{x^\alpha}$（$\alpha > 0$）和 $\displaystyle\lim_{x\to +\infty} \frac{x^n}{e^x}$

---

## 解答

### (a) L'Hôpital法则及证明

**定理**（$\frac{0}{0}$ 型）:

设 $f, g$ 在 $(a,b)$ 可导，$g'(x) \neq 0$。

若 $\lim_{x\to a^+} f(x) = \lim_{x\to a^+} g(x) = 0$，且 $\lim_{x\to a^+} \frac{f'(x)}{g'(x)} = L$，则：
$$\lim_{x\to a^+} \frac{f(x)}{g(x)} = L$$

**证明**:

补充定义 $f(a) = g(a) = 0$ 使函数在 $[a,b]$ 连续。

对 $x \in (a,b)$，由Cauchy中值定理，存在 $\xi \in (a,x)$ 使得：
$$\frac{f(x)}{g(x)} = \frac{f(x) - f(a)}{g(x) - g(a)} = \frac{f'(\xi)}{g'(\xi)}$$

当 $x \to a^+$，$\xi \to a^+$，因此：
$$\lim_{x\to a^+} \frac{f(x)}{g(x)} = \lim_{\xi \to a^+} \frac{f'(\xi)}{g'(\xi)} = L \quad \square$$

---

### (b) 三角函数极限

**解**:

$\frac{0}{0}$ 型，用L'Hôpital：

**第一次**:
$$\lim_{x\to 0} \frac{\tan x - x}{x^3} = \lim_{x\to 0} \frac{\sec^2 x - 1}{3x^2}$$

仍是 $\frac{0}{0}$。

**第二次**:
$$= \lim_{x\to 0} \frac{2\sec x \cdot \sec x \tan x}{6x} = \lim_{x\to 0} \frac{2\sec^2 x \tan x}{6x}$$

**第三次**:

或直接化简：
$$\frac{\sec^2 x - 1}{3x^2} = \frac{\tan^2 x}{3x^2} = \frac{1}{3}\left(\frac{\tan x}{x}\right)^2 \to \frac{1}{3}$$

因此：
$$\lim_{x\to 0} \frac{\tan x - x}{x^3} = \frac{1}{3} \quad \square$$

---

### (c) 无穷远处的阶

**第一个极限**（$\alpha > 0$）:

$\frac{\infty}{\infty}$ 型：
$$\lim_{x\to +\infty} \frac{\ln x}{x^\alpha} = \lim_{x\to +\infty} \frac{1/x}{\alpha x^{\alpha-1}} = \lim_{x\to +\infty} \frac{1}{\alpha x^\alpha} = 0$$

**结论**: 任何正幂函数比对数增长快。

**第二个极限**:

$\frac{\infty}{\infty}$ 型，反复用L'Hôpital $n$ 次：
$$\lim_{x\to +\infty} \frac{x^n}{e^x} = \lim_{x\to +\infty} \frac{nx^{n-1}}{e^x} = \cdots = \lim_{x\to +\infty} \frac{n!}{e^x} = 0$$

**结论**: 指数函数比任何多项式增长快。

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| CMVT证明 | (a) | L'Hôpital的严格证明 |
| 多次应用 | (b) | 可多次用直到确定极限 |
| 化简优先 | (b) | 有时化简比继续求导简单 |
| 阶的比较 | (c) | 建立增长阶的层次 |

### 关键洞察

1. **L'Hôpital的本质**: CMVT的极限形式
2. **增长阶**: $\ln x \ll x^\alpha \ll e^x$（$\alpha > 0$）
3. **多次应用**: 只要仍是未定式就可继续

---

## 常见错误

### 错误1: 非未定式用L'Hôpital

❌ **错误做法**:
> 对$\frac{1}{1}$用L'Hôpital

✅ **正确做法**:
> 必须是$\frac{0}{0}$或$\frac{\infty}{\infty}$

### 错误2: 导数比极限不存在

❌ **错误做法**:
> $\lim f'/g'$不存在就认为原极限不存在

✅ **正确理解**:
> L'Hôpital是充分条件，不是必要条件

### 错误3: 分子分母分别求导

❌ **错误做法**:
> 对$f/g$直接$(f/g)'$

✅ **正确做法**:
> 是分别求导再比：$f'/g'$

---

## 变式练习

### 变式1（难度⭐⭐⭐）

计算 $\displaystyle\lim_{x\to 0} \frac{e^{-\frac{1}{x^2}}}{x^n}$（$n$为正整数）

**答案**: $0$

**提示**: 令$t = 1/x^2$转化

### 变式2（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{x\to 0} \left(\frac{\sin x}{x}\right)^{\frac{1}{x^2}}$

**答案**: $e^{-1/6}$

**提示**: 取对数后用L'Hôpital

### 变式3（难度⭐⭐⭐⭐）

设 $f$ 在 $(0,+\infty)$ 可导，$\lim_{x\to+\infty} [f(x) + f'(x)] = L$。证明 $\lim_{x\to+\infty} f(x) = L$ 且 $\lim_{x\to+\infty} f'(x) = 0$

**提示**: 考虑$e^x f(x)$的导数

---

## 相关概念

| 概念 | 关系 |
|------|------|
| 阶的比较 | L'Hôpital确定函数增长的相对速度 |
| Stolz定理 | 数列版本的L'Hôpital |
| 渐近分析 | 比较无穷小和无穷大的阶 |

**标签**: #L'Hôpital法则 #未定式 #阶的比较 #实分析 #MIT-18.100A
