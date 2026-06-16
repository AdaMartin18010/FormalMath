---
msc_primary: '26

  - 26A42'
exercise_id: ANA-041
title: Riemann和计算
difficulty: 3
type: CALC
topic: 实分析
subtopic: Riemann积分
source:
  course: MIT 18.100A Real Analysis
  chapter: '6.1'
  original: true
processed_at: '2026-04-09'
external_ids:
  wikipedia_url: https://en.wikipedia.org/wiki/Bernhard_Riemann
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Riemann/
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=26A42
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q42299
    consulted_at: '2026-06-16'
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
---
# ANA-041: Riemann和计算

**题号**: ANA-041
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 计算型 (CALC)
**来源**: MIT 18.100A Chapter 6.1
**主题**: Riemann和与积分计算

---

## 题目

**(a)** 用Riemann和的定义计算 $\displaystyle\int_0^1 x^2 \, dx$

**(b)** 计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^n \frac{k}{n^2 + k^2}$

**(c)** 计算 $\displaystyle\lim_{n\to\infty} \frac{1}{n} \sqrt[n]{(n+1)(n+2)\cdots(2n)}$

---

## 解答

### (a) Riemann和计算积分

**解**:

取 $[0,1]$ 的 $n$ 等分，分点 $x_k = \frac{k}{n}$，$k = 0, 1, \ldots, n$。

取右端点：$\xi_k = x_k = \frac{k}{n}$。

Riemann和：
$$S_n = \sum_{k=1}^n f(\xi_k)\Delta x = \sum_{k=1}^n \left(\frac{k}{n}\right)^2 \cdot \frac{1}{n} = \frac{1}{n^3}\sum_{k=1}^n k^2$$

利用 $\sum_{k=1}^n k^2 = \frac{n(n+1)(2n+1)}{6}$：
$$S_n = \frac{n(n+1)(2n+1)}{6n^3} = \frac{(n+1)(2n+1)}{6n^2}$$
$$= \frac{2n^2 + 3n + 1}{6n^2} = \frac{1}{3} + \frac{1}{2n} + \frac{1}{6n^2}$$

取极限：
$$\int_0^1 x^2 \, dx = \lim_{n\to\infty} S_n = \frac{1}{3} \quad \square$$

---

### (b) 和式极限转化为积分

**解**:

改写：
$$\sum_{k=1}^n \frac{k}{n^2 + k^2} = \sum_{k=1}^n \frac{k/n}{1 + (k/n)^2} \cdot \frac{1}{n}$$

这是函数 $f(x) = \frac{x}{1+x^2}$ 在 $[0,1]$ 上的Riemann和（取 $\xi_k = k/n$）。

因此：
$$\lim_{n\to\infty} \sum_{k=1}^n \frac{k}{n^2 + k^2} = \int_0^1 \frac{x}{1+x^2} \, dx$$

计算积分：
$$= \frac{1}{2}\ln(1+x^2)\Big|_0^1 = \frac{1}{2}\ln 2 \quad \square$$

---

### (c) 对数转换与积分

**解**:

设 $L = \displaystyle\lim_{n\to\infty} \frac{1}{n} \sqrt[n]{(n+1)(n+2)\cdots(2n)}$

取对数：
$$\ln L = \lim_{n\to\infty} \left[\frac{1}{n}\sum_{k=1}^n \ln(n+k) - \ln n\right]$$
$$= \lim_{n\to\infty} \frac{1}{n}\sum_{k=1}^n \ln\frac{n+k}{n}$$
$$= \lim_{n\to\infty} \frac{1}{n}\sum_{k=1}^n \ln\left(1 + \frac{k}{n}\right)$$

这是 $\int_0^1 \ln(1+x) \, dx$ 的Riemann和。

计算积分：
$$\int_0^1 \ln(1+x) \, dx = [(1+x)\ln(1+x) - (1+x)]_0^1$$
$$= (2\ln 2 - 2) - (1\ln 1 - 1) = 2\ln 2 - 1$$

因此：
$$\ln L = 2\ln 2 - 1 = \ln 4 - \ln e = \ln\frac{4}{e}$$

$$L = \frac{4}{e} \quad \square$$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 等分选取 | (a) | 最简单的Riemann和构造 |
| 和式转化 | (b) | 提取$1/n$因子识别Riemann和 |
| 对数转换 | (c) | 将乘积转化为求和 |
| 积分公式 | (c) | 分部积分计算对数积分 |

### 关键洞察

1. **Riemann和的形式**: $\sum f(k/n) \cdot (1/n) \to \int_0^1 f(x)\,dx$
2. **识别技巧**: 寻找 $k/n$ 和 $1/n$ 的模式
3. **对数技巧**: 乘积的极限常转化为求和的积分

---

## 常见错误

### 错误1: 分点选择错误

❌ **错误做法**:
> 在(b)中，误认为是$\int_0^1 \frac{1}{1+x}\,dx$

✅ **正确做法**:
> 仔细检查分子是$k/n$还是常数

### 错误2: 积分限错误

❌ **错误做法**:
> 在(c)中，积分限取为$[1,2]$

✅ **正确做法**:
> 变量替换后是$[0,1]$上的积分

### 错误3: 极限与对数交换

❌ **错误做法**:
> 不验证连续性就直接$\ln(\lim) = \lim(\ln)$

✅ **正确做法**:
> 指数函数的连续性保证可交换

---

## 变式练习

### 变式1（难度⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^n \frac{n}{n^2 + k^2}$

**答案**: $\frac{\pi}{4}$

### 变式2（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \frac{1}{n^2} \sum_{k=1}^n \sqrt{n^2 - k^2}$

**答案**: $\frac{\pi}{4}$

### 变式3（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \frac{\sqrt[n]{n!}}{n}$

**答案**: $\frac{1}{e}$

**提示**: 用Stirling公式或转化为积分

---

## 相关概念

| 概念 | 关系 |
|------|------|
| Darboux和 | Riemann和的上下估计 |
| 可积性 | Riemann可积的条件 |
| 反常积分 | 无穷区间或无界函数的积分 |

**标签**: #Riemann和 #定积分 #极限计算 #实分析 #MIT-18.100A

---

## 参考文献

- Walter Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, ISBN: 9780070542358 / MR0385023
- Stephen Abbott, *Understanding Analysis*, 2nd ed., Springer, 2015, ISBN: 9781493927111
- Charles C. Pugh, *Real Mathematical Analysis*, 1st ed., Springer, 2002, ISBN: 9780387952970 / MR1639930
- Terence Tao, *Analysis I*, 3rd ed., Springer, 2016, ISBN: 9789811017896 / MR3728289