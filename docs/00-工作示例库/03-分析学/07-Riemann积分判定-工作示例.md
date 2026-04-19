---
msc_primary: 26

  - 26A42
  - 26A39
title: Riemann可积性判定 - 工作示例
processed_at: '2026-04-08'
---
# Riemann可积性判定 - 工作示例

**类型**: 证明示例
**领域**: 实分析
**难度**: L2
**前置知识**: Riemann积分、上和下和
**创建日期**: 2026年4月8日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | Riemann可积的判定条件 |
| **领域** | 分析学 / 实分析 |
| **MSC** | 26A42（Riemann积分） |
| **相关概念** | Riemann积分、Darboux和、不连续点 |

---

## 题目

判定下列函数在 $[0, 1]$ 上的Riemann可积性：

1. $f(x) = x^2$
2. $f(x) = \begin{cases} 1 & x \in \mathbb{Q} \\ 0 & x \notin \mathbb{Q} \end{cases}$（Dirichlet函数）
3. $f(x) = \begin{cases} \frac{1}{q} & x = \frac{p}{q} \text{ 最简分数} \\ 0 & x \notin \mathbb{Q} \end{cases}$（Thomae函数）

---

## 完整解答（工作示例）

### Riemann可积条件

**Lebesgue准则**：有界函数 $f$ 在 $[a,b]$ 上Riemann可积当且仅当其不连续点集是零测集。

**Darboux准则**：$\lim_{\|P\| \to 0} (U(P,f) - L(P,f)) = 0$。

---

**解答 1**：$f(x) = x^2$

$x^2$ 在 $[0,1]$ 上连续，故Riemann可积。

**直接计算**：
$$\int_0^1 x^2 \, dx = \frac{1}{3}$$

---

**解答 2**：Dirichlet函数

**不连续点**：每一点都不连续（有理数和无理数都稠密）。

不连续点集 = $[0,1]$，测度为 1（非零）。

由 Lebesgue 准则，**不可积**。

**直接证明**：对任意分割，每个区间既有有理数又有无理数。

- $M_i = \sup f = 1$
- $m_i = \inf f = 0$

上和 $U(P,f) = 1$，下和 $L(P,f) = 0$。

$U - L = 1 \not\to 0$，不可积。

---

**解答 3**：Thomae函数

**在无理点**：设 $x_0$ 是无理数。

对任意 $\varepsilon > 0$，存在有限个 $q \leq 1/\varepsilon$。

在这些 $q$ 对应的有理数中，只有有限个在 $x_0$ 附近使 $f(x) \geq \varepsilon$。

可找到 $\delta$ 使得 $|x - x_0| < \delta$ 时 $f(x) < \varepsilon$。

故 $f$ 在无理点连续。

**在有理点**：设 $x_0 = p/q$ 是有理数。

取无理数列 $x_n \to x_0$，$f(x_n) = 0 \to 0 \neq f(x_0) = 1/q$。

故 $f$ 在有理点不连续。

**不连续点集**：$\mathbb{Q} \cap [0,1]$，可数，故零测。

**结论**：Thomae函数**Riemann可积**。

**积分值**：$\int_0^1 f = 0$（下和恒为 0）。

---

## 关键步骤说明

- **Lebesgue准则**：可积性等价于几乎处处连续
- **稠密性**：用于分析Dirichlet函数
- **Thomae函数**：有理点不连续但可积的经典例子
- **零测集**：可数集、Cantor集等都是零测集

---

## 相关概念链接

- [积分](../../../concept/核心概念/积分.md)
- [实分析](../../../docs/03-分析学/01-实分析/01-实分析.md)
