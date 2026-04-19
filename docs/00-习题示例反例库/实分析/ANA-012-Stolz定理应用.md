---
msc_primary: 40

  - 40A05
exercise_id: ANA-012
title: Stolz定理应用
difficulty: 3
type: CALC
topic: 实分析
subtopic: 极限计算
source:
  course: MIT 18.100A
  chapter: "2.3"
  original: true
processed_at: '2026-04-09'
---

# ANA-012: Stolz定理应用

**题号**: ANA-012
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 计算型 (CALC)
**来源**: MIT 18.100A Chapter 2.3
**主题**: Stolz定理求极限

---

## 题目

利用Stolz定理计算下列极限：

**(a)** 计算 $\displaystyle\lim_{n\to\infty} \frac{1 + 2 + \cdots + n}{n^2}$

**(b)** 计算 $\displaystyle\lim_{n\to\infty} \frac{1^2 + 2^2 + \cdots + n^2}{n^3}$

**(c)** 设 $\lim_{n\to\infty} a_n = a$（有限或$+\infty$），计算 $\displaystyle\lim_{n\to\infty} \frac{a_1 + a_2 + \cdots + a_n}{n}$

---

## 解答

### Stolz定理回顾

设 $\{y_n\}$ 严格单调递增且趋于 $+\infty$，若
$$\lim_{n\to\infty} \frac{x_{n+1} - x_n}{y_{n+1} - y_n} = L$$
则
$$\lim_{n\to\infty} \frac{x_n}{y_n} = L$$

---

### (a) 求 $\displaystyle\lim_{n\to\infty} \frac{1 + 2 + \cdots + n}{n^2}$

**解**:

设 $x_n = 1 + 2 + \cdots + n = \frac{n(n+1)}{2}$，$y_n = n^2$。

验证条件：$y_n = n^2$ 严格单调递增趋于 $+\infty$。✓

计算差分比：
$$\frac{x_{n+1} - x_n}{y_{n+1} - y_n} = \frac{(n+1)}{(n+1)^2 - n^2} = \frac{n+1}{2n+1}$$

求极限：
$$\lim_{n\to\infty} \frac{n+1}{2n+1} = \lim_{n\to\infty} \frac{1 + \frac{1}{n}}{2 + \frac{1}{n}} = \frac{1}{2}$$

由Stolz定理：
$$\lim_{n\to\infty} \frac{1 + 2 + \cdots + n}{n^2} = \frac{1}{2} \quad \square$$

---

### (b) 求 $\displaystyle\lim_{n\to\infty} \frac{1^2 + 2^2 + \cdots + n^2}{n^3}$

**解**:

设 $x_n = \sum_{k=1}^{n} k^2 = \frac{n(n+1)(2n+1)}{6}$，$y_n = n^3$。

验证条件：$y_n = n^3$ 严格单调递增趋于 $+\infty$。✓

计算差分：
- $x_{n+1} - x_n = (n+1)^2$
- $y_{n+1} - y_n = (n+1)^3 - n^3 = 3n^2 + 3n + 1$

差分比：
$$\frac{x_{n+1} - x_n}{y_{n+1} - y_n} = \frac{(n+1)^2}{3n^2 + 3n + 1} = \frac{n^2 + 2n + 1}{3n^2 + 3n + 1}$$

求极限：
$$\lim_{n\to\infty} \frac{n^2 + 2n + 1}{3n^2 + 3n + 1} = \frac{1}{3}$$

由Stolz定理：
$$\lim_{n\to\infty} \frac{1^2 + 2^2 + \cdots + n^2}{n^3} = \frac{1}{3} \quad \square$$

---

### (c) 算术平均的极限

**解**:

设 $x_n = a_1 + a_2 + \cdots + a_n$，$y_n = n$。

验证条件：$y_n = n$ 严格单调递增趋于 $+\infty$。✓

计算差分比：
$$\frac{x_{n+1} - x_n}{y_{n+1} - y_n} = \frac{a_{n+1}}{1} = a_{n+1}$$

由已知 $\lim_{n\to\infty} a_n = a$，得：
$$\lim_{n\to\infty} \frac{x_{n+1} - x_n}{y_{n+1} - y_n} = a$$

由Stolz定理：
$$\lim_{n\to\infty} \frac{a_1 + a_2 + \cdots + a_n}{n} = a \quad \square$$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 识别Stolz形式 | 全部 | $\frac{\infty}{\infty}$ 型不定式，分子为部分和 |
| 差分计算 | 全部 | 准确计算 $x_{n+1} - x_n$ 和 $y_{n+1} - y_n$ |
| 条件验证 | 全部 | 必须验证 $y_n$ 严格单调递增趋于无穷 |
| Cesàro平均 | (c)部分 | Stolz定理的重要推论 |

### 关键洞察

1. **Stolz定理是离散的洛必达法则**: 适用于 $\frac{\infty}{\infty}$ 型数列极限
2. **Cesàro平均定理**: 收敛序列的算术平均收敛于同一极限
3. **逆命题不成立**: 算术平均收敛不代表原序列收敛（如 $a_n = (-1)^n$）

---

## 常见错误

### 错误1: 忽略条件验证

❌ **错误做法**:
> 直接使用Stolz定理而不验证 $y_n$ 严格单调递增趋于无穷

✅ **正确做法**:
> 必须先验证 $y_n$ 满足条件，特别是严格单调性

### 错误2: 差分计算错误

❌ **错误做法**:
> $x_{n+1} - x_n = a_{n+1} - a_n$（混淆差分定义）

✅ **正确做法**:
> 若 $x_n = \sum_{k=1}^n a_k$，则 $x_{n+1} - x_n = a_{n+1}$

### 错误3: 应用于不适当形式

❌ **错误做法**:
> 对 $\frac{0}{0}$ 型或普通分式使用Stolz定理

✅ **正确做法**:
> Stolz定理仅适用于特定形式，需先化为标准形式

---

## 变式练习

### 变式1（难度⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \frac{\ln 1 + \ln 2 + \cdots + \ln n}{n \ln n}$

**答案**: $1$

**提示**: 利用 $\ln n! = \sum_{k=1}^n \ln k$，用Stolz定理

### 变式2（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \frac{1 + \frac{1}{2} + \cdots + \frac{1}{n}}{\ln n}$

**答案**: $1$

**提示**: 利用调和级数与对数的关系，$\frac{1}{n+1} \sim \ln(n+1) - \ln n$

### 变式3（难度⭐⭐⭐⭐）

设 $a_n > 0$ 且 $\lim_{n\to\infty} \frac{a_{n+1}}{a_n} = L$，证明：
$$\lim_{n\to\infty} \sqrt[n]{a_n} = L$$

**提示**: 令 $b_n = \ln a_n$，利用Stolz定理求 $\frac{b_n}{n}$ 的极限

---

## 相关概念

| 概念 | 关系 |
|------|------|
| Cesàro平均 | Stolz定理的直接应用 |
| 调和级数 | 变式2的核心 |
| 洛必达法则 | Stolz定理的连续类比 |

**标签**: #Stolz定理 #Cesàro平均 #极限计算 #实分析 #MIT-18.100A
