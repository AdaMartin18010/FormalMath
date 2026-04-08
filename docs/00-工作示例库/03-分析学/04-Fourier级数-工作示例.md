---
msc_primary: 42A16
msc_secondary:
- 42A20
title: Fourier级数展开 - 工作示例
processed_at: '2026-04-08'
---
# Fourier级数展开 - 工作示例

**类型**: 计算示例
**领域**: 调和分析
**难度**: L2
**前置知识**: 积分、级数
**创建日期**: 2026年4月8日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 计算函数的Fourier级数展开 |
| **领域** | 分析学 / 调和分析 |
| **MSC** | 42A16（Fourier系数） |
| **相关概念** | Fourier级数、正交函数、Parseval等式 |

---

## 题目

计算下列函数在 $[-\pi, \pi]$ 上的Fourier级数展开：

1. $f(x) = x$
2. $f(x) = |x|$
3. 利用Parseval等式求 $\sum_{n=1}^{\infty} \frac{1}{n^2}$

---

## 完整解答（工作示例）

### Fourier级数公式

$$f(x) \sim \frac{a_0}{2} + \sum_{n=1}^{\infty} (a_n \cos nx + b_n \sin nx)$$

其中：
$$a_n = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \cos nx \, dx, \quad b_n = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \sin nx \, dx$$

---

**解答 1**：$f(x) = x$

**$a_n$ 的计算**：$f(x) = x$ 是奇函数，$\cos nx$ 是偶函数，故 $a_n = 0$（对所有 $n$）。

**$b_n$ 的计算**：
$$b_n = \frac{1}{\pi} \int_{-\pi}^{\pi} x \sin nx \, dx = \frac{2}{\pi} \int_{0}^{\pi} x \sin nx \, dx$$

分部积分：
$$\int x \sin nx \, dx = -\frac{x \cos nx}{n} + \frac{\sin nx}{n^2}$$

$$b_n = \frac{2}{\pi} \left[-\frac{\pi \cos n\pi}{n} + \frac{\sin n\pi}{n^2}\right] = \frac{2}{\pi} \cdot \frac{-\pi (-1)^n}{n} = \frac{2(-1)^{n+1}}{n}$$

**Fourier级数**：
$$x \sim 2\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n} \sin nx = 2\left(\sin x - \frac{\sin 2x}{2} + \frac{\sin 3x}{3} - \cdots\right)$$

---

**解答 2**：$f(x) = |x|$

**$a_0$ 的计算**：
$$a_0 = \frac{1}{\pi} \int_{-\pi}^{\pi} |x| \, dx = \frac{2}{\pi} \int_{0}^{\pi} x \, dx = \frac{2}{\pi} \cdot \frac{\pi^2}{2} = \pi$$

**$a_n$ 的计算**（$|x|$ 是偶函数，$b_n = 0$）：
$$a_n = \frac{2}{\pi} \int_{0}^{\pi} x \cos nx \, dx$$

分部积分：
$$\int x \cos nx \, dx = \frac{x \sin nx}{n} + \frac{\cos nx}{n^2}$$

$$a_n = \frac{2}{\pi} \left[\frac{\pi \sin n\pi}{n} + \frac{\cos n\pi - 1}{n^2}\right] = \frac{2}{\pi} \cdot \frac{(-1)^n - 1}{n^2}$$

当 $n$ 为偶数时，$a_n = 0$；当 $n$ 为奇数时，$a_n = \frac{-4}{\pi n^2}$。

**Fourier级数**：
$$|x| \sim \frac{\pi}{2} - \frac{4}{\pi}\sum_{k=0}^{\infty} \frac{\cos(2k+1)x}{(2k+1)^2}$$

---

**解答 3**：Parseval等式应用

**Parseval等式**：
$$\frac{1}{\pi} \int_{-\pi}^{\pi} |f(x)|^2 \, dx = \frac{a_0^2}{2} + \sum_{n=1}^{\infty} (a_n^2 + b_n^2)$$

对 $f(x) = |x|$：
$$\frac{1}{\pi} \int_{-\pi}^{\pi} x^2 \, dx = \frac{2\pi^2}{3}$$

$$\frac{a_0^2}{2} + \sum_{n=1}^{\infty} a_n^2 = \frac{\pi^2}{2} + \sum_{k=0}^{\infty} \frac{16}{\pi^2(2k+1)^4}$$

**等等**，我们用另一个方法：

对 $f(x) = x$ 在 $x = \pi$ 处：
$$\pi = 2\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n} \sin n\pi = 0$$

不收敛到 $\pi$（Gibbs现象）。

**正确方法**：对 $f(x) = |x|$ 在 $x = 0$ 处：
$$0 = \frac{\pi}{2} - \frac{4}{\pi}\sum_{k=0}^{\infty} \frac{1}{(2k+1)^2}$$

因此：
$$\sum_{k=0}^{\infty} \frac{1}{(2k+1)^2} = \frac{\pi^2}{8}$$

设 $S = \sum_{n=1}^{\infty} \frac{1}{n^2}$，则：
$$S = \sum_{n=1}^{\infty} \frac{1}{n^2} = \sum_{k=0}^{\infty} \frac{1}{(2k+1)^2} + \sum_{k=1}^{\infty} \frac{1}{(2k)^2} = \frac{\pi^2}{8} + \frac{1}{4}S$$

解得：$\frac{3}{4}S = \frac{\pi^2}{8}$，$S = \frac{\pi^2}{6}$

**结论**：$\displaystyle\sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6}$（Basel问题）

---

## 关键步骤说明

- **奇偶函数**：简化Fourier系数计算
- **分部积分**：计算 $x \sin nx$ 和 $x \cos nx$ 的积分
- **逐项求值**：在特定点求Fourier级数的值
- **Parseval等式**：联系函数范数与系数平方和

---

## 相关概念链接

- [级数](../../../concept/核心概念/级数.md)
- [分析学](../../../docs/03-分析学/01-实分析/01-实分析.md)
