---
msc_primary: 41

  - 41A58
exercise_id: ANA-035
title: Taylor展开应用
difficulty: 3
type: CALC
topic: 实分析
subtopic: 微分中值定理
source:
  course: MIT 18.100A Real Analysis
  chapter: "5.4"
  original: true
processed_at: '2026-04-09'
---

# ANA-035: Taylor展开应用

**题号**: ANA-035
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 计算型 (CALC)
**来源**: MIT 18.100A Chapter 5.4
**主题**: Taylor定理与展开应用

---

## 题目

**(a)** 写出 $e^x$、$\sin x$、$\cos x$、$\ln(1+x)$ 在 $x = 0$ 处的Taylor展开（带Lagrange余项）

**(b)** 计算 $\displaystyle\lim_{x\to 0} \frac{e^x - 1 - x}{x^2}$

**(c)** 设 $f$ 在 $[a,b]$ 上二阶可导，$f'(a) = f'(b) = 0$。证明存在 $c \in (a,b)$ 使得
$$|f''(c)| \geq \frac{4|f(b) - f(a)|}{(b-a)^2}$$

---

## 解答

### (a) Taylor展开公式

**$e^x$**:
$$e^x = \sum_{k=0}^{n} \frac{x^k}{k!} + \frac{e^{\xi}}{(n+1)!}x^{n+1}, \quad \xi \text{在} 0, x \text{之间}$$

**$\sin x$**:
$$\sin x = \sum_{k=0}^{m} (-1)^k \frac{x^{2k+1}}{(2k+1)!} + (-1)^{m+1}\frac{\cos \xi}{(2m+3)!}x^{2m+3}$$

**$\cos x$**:
$$\cos x = \sum_{k=0}^{m} (-1)^k \frac{x^{2k}}{(2k)!} + (-1)^{m+1}\frac{\cos \xi}{(2m+2)!}x^{2m+2}$$

**$\ln(1+x)$**（$|x| < 1$）：
$$\ln(1+x) = \sum_{k=1}^{n} (-1)^{k-1}\frac{x^k}{k} + \frac{(-1)^n}{(n+1)(1+\xi)^{n+1}}x^{n+1}$$

---

### (b) 极限计算

**解**:

用Taylor展开：
$$e^x = 1 + x + \frac{x^2}{2} + \frac{e^{\xi}}{6}x^3, \quad \xi \in (0, x)$$

因此：
$$e^x - 1 - x = \frac{x^2}{2} + \frac{e^{\xi}}{6}x^3$$

$$
\frac{e^x - 1 - x}{x^2} = \frac{1}{2} + \frac{e^{\xi}}{6}x
$$

当 $x \to 0$，$\xi \to 0$，$e^{\xi} \to 1$：
$$\lim_{x\to 0} \frac{e^x - 1 - x}{x^2} = \frac{1}{2} \quad \square$$

---

### (c) Taylor估计

**证明**:

在 $a$ 处展开到二阶（带Lagrange余项）：
$$f(x) = f(a) + f'(a)(x-a) + \frac{f''(\xi_1)}{2}(x-a)^2, \quad \xi_1 \in (a, x)$$

由 $f'(a) = 0$：
$$f(x) = f(a) + \frac{f''(\xi_1)}{2}(x-a)^2$$

在 $b$ 处展开：
$$f(x) = f(b) + \frac{f''(\xi_2)}{2}(x-b)^2, \quad \xi_2 \in (x, b)$$

取 $x = \frac{a+b}{2}$（中点）：

从第一个展开：
$$f\left(\frac{a+b}{2}\right) = f(a) + \frac{f''(\xi_1)}{2}\left(\frac{b-a}{2}\right)^2$$

从第二个展开：
$$f\left(\frac{a+b}{2}\right) = f(b) + \frac{f''(\xi_2)}{2}\left(\frac{a-b}{2}\right)^2$$

相减：
$$f(b) - f(a) = \frac{(b-a)^2}{8}[f''(\xi_1) - f''(\xi_2)]$$

因此：
$$|f(b) - f(a)| \leq \frac{(b-a)^2}{8}[|f''(\xi_1)| + |f''(\xi_2)|]$$

取 $c$ 使得 $|f''(c)| = \max(|f''(\xi_1)|, |f''(\xi_2)|)$：
$$|f(b) - f(a)| \leq \frac{(b-a)^2}{4}|f''(c)|$$

即：
$$|f''(c)| \geq \frac{4|f(b) - f(a)|}{(b-a)^2} \quad \square$$

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| Taylor展开 | (b)(c) | 用多项式逼近函数 |
| Lagrange余项 | (c) | 提供精确的误差估计 |
| 中点选取 | (c) | 对称性简化计算 |
| 极值选取 | (c) | 两个估计中取最大 |

### 关键洞察

1. **Taylor展开的核心**: 用导数信息在一点附近逼近函数
2. **余项的重要性**: 知道误差项才能做精确估计
3. **对称性**: 中点选取使$(x-a)^2 = (x-b)^2$

---

## 常见错误

### 错误1: 展开阶数不足

❌ **错误做法**:
> 对$e^x$只用一阶展开$e^x \approx 1+x$

✅ **正确做法**:
> 需要二阶展开才能计算$x^2$分母的极限

### 错误2: 忽略余项

❌ **错误做法**:
> 在(c)中，展开后不说余项形式

✅ **正确做法**:
> 明确写出Lagrange余项的形式

### 错误3: 中点选择错误

❌ **错误做法**:
> 在(c)中取$x$为其他值

✅ **正确做法**:
> 中点使两个余项系数相等，便于比较

---

## 变式练习

### 变式1（难度⭐⭐⭐）

计算 $\displaystyle\lim_{x\to 0} \frac{\sin x - x + x^3/6}{x^5}$

**答案**: $\frac{1}{120}$

### 变式2（难度⭐⭐⭐⭐）

设 $f$ 在 $[0,1]$ 上三阶可导，$f(0) = f'(0) = f''(0) = 0$，$f(1) = 1$。证明存在 $c \in (0,1)$ 使得 $f'''(c) \geq 6$

### 变式3（难度⭐⭐⭐⭐）

证明：$e$ 是无理数

**提示**: 用Taylor展开证明$e$不能写成$p/q$

---

## 相关概念

| 概念 | 关系 |
|------|------|
| Maclaurin展开 | $x=0$处的Taylor展开 |
| Peano余项 | 另一种余项形式 |
| Taylor级数 | 无穷级数形式的展开 |

**标签**: #Taylor展开 #Taylor定理 #Lagrange余项 #实分析 #MIT-18.100A
