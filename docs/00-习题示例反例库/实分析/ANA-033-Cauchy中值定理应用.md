---
msc_primary: '26

  - 26A06'
exercise_id: ANA-033
title: Cauchy中值定理应用
difficulty: 3
type: APP
topic: 实分析
subtopic: 微分中值定理
source:
  course: MIT 18.100A Real Analysis
  chapter: '5.2'
  original: true
processed_at: '2026-04-09'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/Cauchy+theorem
  wikipedia_url: https://en.wikipedia.org/wiki/Cauchy's_theorem_(group_theory)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=Cauchy
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Cauchy/
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=26A06
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q1139041
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
# ANA-033: Cauchy中值定理应用

**题号**: ANA-033
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 应用型 (APP)
**来源**: MIT 18.100A Chapter 5.2
**主题**: Cauchy中值定理(CMVT)及其应用

---

## 题目

**(a)** 叙述并证明Cauchy中值定理

**(b)** 设 $f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导（$a > 0$）。证明存在 $c \in (a,b)$ 使得
$$\frac{bf(b) - af(a)}{b - a} = f(c) + cf'(c)$$

**(c)** 设 $0 < a < b$，$f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导。证明存在 $c \in (a,b)$ 使得
$$f(b) - f(a) = cf'(c)\ln\frac{b}{a}$$

---

## 解答

### (a) Cauchy中值定理

**定理**: 设 $f, g$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导，且 $g'(x) \neq 0$ 对所有 $x \in (a,b)$。则存在 $c \in (a,b)$ 使得：
$$\frac{f(b) - f(a)}{g(b) - g(a)} = \frac{f'(c)}{g'(c)}$$

**证明**:

构造辅助函数：
$$h(x) = f(x) - \frac{f(b) - f(a)}{g(b) - g(a)}g(x)$$

**验证**:
- $h(a) = f(a) - \frac{f(b) - f(a)}{g(b) - g(a)}g(a) = \frac{f(a)g(b) - f(b)g(a)}{g(b) - g(a)}$
- $h(b) = f(b) - \frac{f(b) - f(a)}{g(b) - g(a)}g(b) = \frac{f(a)g(b) - f(b)g(a)}{g(b) - g(a)}$

所以 $h(a) = h(b)$。

由Rolle定理，存在 $c \in (a,b)$ 使得 $h'(c) = 0$。

计算：
$$h'(x) = f'(x) - \frac{f(b) - f(a)}{g(b) - g(a)}g'(x)$$

由 $h'(c) = 0$：
$$\frac{f(b) - f(a)}{g(b) - g(a)} = \frac{f'(c)}{g'(c)} \quad \square$$

---

### (b) 导数与函数组合

**证明**:

注意到右边 $f(c) + cf'(c) = (xf(x))'|_{x=c}$。

对 $F(x) = xf(x)$ 和 $g(x) = x$ 用CMVT：

$$\frac{F(b) - F(a)}{g(b) - g(a)} = \frac{F'(c)}{g'(c)}$$

即：
$$\frac{bf(b) - af(a)}{b - a} = \frac{f(c) + cf'(c)}{1} = f(c) + cf'(c)$$

证毕。 $\square$

---

### (c) 对数权重

**证明**:

取 $g(x) = \ln x$，则 $g'(x) = 1/x \neq 0$ 在 $(a,b)$ 上。

由CMVT：
$$\frac{f(b) - f(a)}{\ln b - \ln a} = \frac{f'(c)}{1/c} = cf'(c)$$

因此：
$$f(b) - f(a) = cf'(c)(\ln b - \ln a) = cf'(c)\ln\frac{b}{a} \quad \square$$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 识别CMVT形式 | (b)(c) | 将目标等式改写为比值形式 |
| 导数观察 | (b) | 注意$f(c) + cf'(c) = (xf(x))'$ |
| 对数选择 | (c) | $g(x) = \ln x$产生对数因子 |
| 辅助函数 | (a) | 构造$h$应用Rolle定理 |

### 关键洞察

1. **CMVT的核心**: 两个函数变化率的比值
2. **$g(x)$的选择**: 根据目标等式的形式选取
3. **LMVT特例**: 取$g(x) = x$即得Lagrange中值定理

---

## 常见错误

### 错误1: 直接对分子分母分别用LMVT

❌ **错误做法**:
> 分别找$c_1, c_2$使$f(b)-f(a) = f'(c_1)(b-a)$和$g(b)-g(a) = g'(c_2)(b-a)$

✅ **正确做法**:
> CMVT保证的是同一$c$，不能分开用LMVT

### 错误2: 忽略$g'$非零条件

❌ **错误做法**:
> 不验证$g'(x) \neq 0$就用CMVT

✅ **正确做法**:
> 必须保证$g'(c) \neq 0$才能做分母

### 错误3: $g$函数选择错误

❌ **错误做法**:
> 在(c)中选$g(x) = x$

✅ **正确做法**:
> 根据目标中的$\ln(b/a)$选择$g(x) = \ln x$

---

## 变式练习

### 变式1（难度⭐⭐⭐）

设 $0 < a < b$，$f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导。证明存在 $c \in (a,b)$ 使得
$$\frac{af(b) - bf(a)}{a - b} = f(c) - cf'(c)$$

### 变式2（难度⭐⭐⭐⭐）

设 $f$ 在 $[a,b]$ 上连续，在 $(a,b)$ 内可导（$a > 0$）。证明存在 $c \in (a,b)$ 使得
$$\frac{f(b) - f(a)}{b^2 - a^2} = \frac{f'(c)}{2c}$$

### 变式3（难度⭐⭐⭐⭐）

设 $f$ 在 $[0,1]$ 上连续，在 $(0,1)$ 内可导，$f(0) = 0$，$f(1) = 1$。证明存在不同的 $c_1, c_2 \in (0,1)$ 使得
$$\frac{1}{f'(c_1)} + \frac{1}{f'(c_2)} = 2$$

**提示**: 在$[0, 1/2]$和$[1/2, 1]$上分别用CMVT

---

## 相关概念

| 概念 | 关系 |
|------|------|
| L'Hôpital法则 | CMVT的推论 |
| 参数曲线 | CMVT的几何解释 |
| 速度-时间 | CMVT的物理解释 |

**标签**: #Cauchy中值定理 #CMVT #微分中值定理 #实分析 #MIT-18.100A

---

## 参考文献

- Walter Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, ISBN: 9780070542358 / MR0385023
- Stephen Abbott, *Understanding Analysis*, 2nd ed., Springer, 2015, ISBN: 9781493927111
- Charles C. Pugh, *Real Mathematical Analysis*, 1st ed., Springer, 2002, ISBN: 9780387952970 / MR1639930
- Terence Tao, *Analysis I*, 3rd ed., Springer, 2016, ISBN: 9789811017896 / MR3728289