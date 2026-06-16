---
msc_primary: '26

  - 26A06'
exercise_id: ANA-031
title: Rolle定理应用
difficulty: 3
type: APP
topic: 实分析
subtopic: 微分中值定理
source:
  course: MIT 18.100A Real Analysis
  chapter: '5.2'
  original: true
processed_at: '2026-04-09'
references:
  textbooks:
  - title: Principles of Mathematical Analysis
    author: Walter Rudin
    edition: 3rd
    publisher: McGraw-Hill
    year: 1976
    isbn: '9780070542358'
    mr_number: MR0385023
  - title: Understanding Analysis
    author: Stephen Abbott
    edition: 2nd
    publisher: Springer
    year: 2015
    isbn: '9781493927111'
    doi: 10.1007/978-1-4939-2712-8
  - title: Real Mathematical Analysis
    author: Charles C. Pugh
    edition: 1st
    publisher: Springer
    year: 2002
    isbn: '9780387952970'
    mr_number: MR1639930
    doi: 10.1007/978-0-387-21676-7
  - title: Analysis I
    author: Terence Tao
    edition: 3rd
    publisher: Springer
    year: 2016
    isbn: '9789811017896'
    mr_number: MR3728289
    doi: 10.1007/978-981-10-1789-6
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=26A06
---
# ANA-031: Rolle定理应用

**题号**: ANA-031
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 应用型 (APP)
**来源**: MIT 18.100A Chapter 5.2
**主题**: Rolle定理的经典应用

---

## 题目

**(a)** 设 $f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导，且 $f(a) = f(b) = 0$。证明对任意实数 $\lambda$，存在 $c \in (a,b)$ 使得 $f'(c) = \lambda f(c)$

**(b)** 设 $f$ 在 $[0,1]$ 上可导，$f(0) = 0$，$f(1) = 1$。证明存在 $c \in (0,1)$ 使得 $f'(c) = 2c$

**(c)** 设 $P(x)$ 是可微函数，$a < b$ 是 $P$ 的两个零点。证明 $P'(x) + P(x)$ 在 $(a,b)$ 内至少有一个零点

---

## 解答

### Rolle定理回顾

若 $f$ 在 $[a,b]$ 连续，$(a,b)$ 可导，且 $f(a) = f(b)$，则存在 $c \in (a,b)$ 使得 $f'(c) = 0$。

---

### (a) 广义Rolle应用

**证明**:

构造辅助函数 $g(x) = e^{-\lambda x} f(x)$。

**验证条件**:
- $g$ 在 $[a,b]$ 连续（$f$ 连续，指数函数连续）
- $g$ 在 $(a,b)$ 可导
- $g(a) = e^{-\lambda a} f(a) = 0$，$g(b) = e^{-\lambda b} f(b) = 0$

由Rolle定理，存在 $c \in (a,b)$ 使得 $g'(c) = 0$。

**计算导数**:
$$g'(x) = e^{-\lambda x} f'(x) - \lambda e^{-\lambda x} f(x) = e^{-\lambda x}[f'(x) - \lambda f(x)]$$

由 $g'(c) = 0$ 且 $e^{-\lambda c} \neq 0$：
$$f'(c) - \lambda f(c) = 0$$

即 $f'(c) = \lambda f(c)$。 $\square$

---

### (b) 构造辅助函数

**证明**:

构造 $g(x) = f(x) - x^2$。

**验证条件**:
- $g(0) = f(0) - 0 = 0$
- $g(1) = f(1) - 1 = 0$

由Rolle定理，存在 $c \in (0,1)$ 使得 $g'(c) = 0$。

**计算**:
$$g'(x) = f'(x) - 2x$$

因此 $g'(c) = f'(c) - 2c = 0$，即 $f'(c) = 2c$。 $\square$

---

### (c) 微分方程视角

**证明**:

令 $f(x) = e^x P(x)$。

**边界条件**:
- $f(a) = e^a P(a) = 0$
- $f(b) = e^b P(b) = 0$

由Rolle定理，存在 $c \in (a,b)$ 使得 $f'(c) = 0$。

**计算导数**:
$$f'(x) = e^x P(x) + e^x P'(x) = e^x[P(x) + P'(x)]$$

由 $f'(c) = 0$ 且 $e^c \neq 0$：
$$P(c) + P'(c) = 0$$

因此 $P'(x) + P(x)$ 在 $(a,b)$ 内有零点。 $\square$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 指数加权 | (a)(c) | $e^{\lambda x}$ 或 $e^x$ 构造辅助函数 |
| 多项式调整 | (b) | 减去目标导数的原函数 |
| Rolle条件构造 | 全部 | 使端点函数值相等 |
| 微分方程思想 | (c) | 将条件转化为导数为零 |

### 关键洞察

1. **辅助函数构造**: Rolle定理应用的核心是找到合适的 $g$
2. **指数因子**: 处理含 $f'$ 和 $f$ 的线性组合时常用
3. **端点归零**: 通过构造使 $g(a) = g(b)$

---

## 常见错误

### 错误1: 辅助函数选择不当

❌ **错误做法**:
> 直接对$f$用Rolle定理，忽略$f(a) \neq f(b)$

✅ **正确做法**:
> 构造新函数使端点值相等

### 错误2: 导数计算错误

❌ **错误做法**:
> 在(a)中，忘记链式法则对$e^{-\lambda x}$求导

✅ **正确做法**:
> 仔细计算：$(e^{-\lambda x})' = -\lambda e^{-\lambda x}$

### 错误3: 忽略非零因子

❌ **错误做法**:
> 不说明$e^{-\lambda c} \neq 0$就推出$f'(c) = \lambda f(c)$

✅ **正确做法**:
> 明确指出指数函数恒正

---

## 变式练习

### 变式1（难度⭐⭐⭐）

设 $f$ 在 $[a,b]$ 上二阶可导，$f(a) = f(b) = f(c) = 0$（$a < c < b$）。证明存在 $\xi \in (a,b)$ 使得 $f''(\xi) = 0$

### 变式2（难度⭐⭐⭐⭐）

设 $f$ 在 $[0,1]$ 上可导，$f(0) = 0$，$f(1) = 1$。对任意正数 $a, b$，证明存在不同的 $c_1, c_2 \in (0,1)$ 使得
$$\frac{a}{f'(c_1)} + \frac{b}{f'(c_2)} = a + b$$

### 变式3（难度⭐⭐⭐⭐⭐）

设 $f$ 在 $[0,+\infty)$ 上可导，$f(0) = 0$，$|f'(x)| \leq |f(x)|$。证明 $f \equiv 0$

**提示**: 考虑$g(x) = f^2(x)e^{-2x}$

---

## 相关概念

| 概念 | 关系 |
|------|------|
| 微分方程 | 辅助函数与积分因子的联系 |
| Gronwall不等式 | 变式3的推广 |
| 唯一性定理 | ODE解的唯一性 |

**标签**: #Rolle定理 #辅助函数 #微分中值定理 #实分析 #MIT-18.100A

---

## 参考文献

- Walter Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, ISBN: 9780070542358 / MR0385023
- Stephen Abbott, *Understanding Analysis*, 2nd ed., Springer, 2015, ISBN: 9781493927111
- Charles C. Pugh, *Real Mathematical Analysis*, 1st ed., Springer, 2002, ISBN: 9780387952970 / MR1639930
- Terence Tao, *Analysis I*, 3rd ed., Springer, 2016, ISBN: 9789811017896 / MR3728289