---
msc_primary: 00

  - 00A99
  - 26A42
  - 03B40
title: Riemann 积分与 Darboux 和 - 工作示例
description: '理解Riemann可积的等价条件，通过Darboux上下和的概念深入理解积分的本质'
author: 'FormalMath Team'
processed_at: '2026-04-05'
tags: ['实分析', 'Riemann积分', 'Darboux和', '可积性']
---

# Riemann 积分与 Darboux 和 - 工作示例

**类型**: 概念理解  
**领域**: 实分析  
**难度**: L1  
**前置知识**: 实数完备性、上确界下确界  
**创建日期**: 2026年2月2日  
**更新时间**: 2026年4月5日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 可积 ⇔ 上下 Darboux 和之差趋于 0 |
| **领域** | 实分析 / 积分理论 |
| **MSC** | 26A42（Riemann积分）|
| **关键概念** | Darboux和、上积分、下积分、可积条件 |

---

## 题目

说明 \(f : [a,b] \to \mathbb{R}\) 有界，则 \(f\) Riemann 可积当且仅当对任意 \(\varepsilon>0\) 存在分割使 \(U(P,f)-L(P,f)<\varepsilon\)。

---

## 预备知识

### Darboux 和的定义

设 \(P = \{x_0, x_1, ..., x_n\}\) 是 \([a,b]\) 的分割：

- **上确界**: \(M_i = \sup\{f(x) : x \in [x_{i-1}, x_i]\}\)
- **下确界**: \(m_i = \inf\{f(x) : x \in [x_{i-1}, x_i]\}\)
- **上和**: \(U(P,f) = \sum_{i=1}^n M_i \Delta x_i\)
- **下和**: \(L(P,f) = \sum_{i=1}^n m_i \Delta x_i\)

### 上积分与下积分

- **上积分**: \(\overline{\int_a^b} f = \inf_P U(P,f)\)
- **下积分**: \(\underline{\int_a^b} f = \sup_P L(P,f)\)

---

## 完整解答

### 证明：可积 ⇔ 上下和可任意接近

**必要性** (\(\Rightarrow\))：

设 \(f\) 在 \([a,b]\) 上 Riemann 可积，积分值为 \(I\)。

根据可积定义，对任意 \(\varepsilon > 0\)，存在 \(\delta > 0\)，使得对任意满足 \(\|P\| < \delta\) 的分割 \(P\) 和任意选取的点 \(\xi_i\)，有：
$$\left|\sum_{i=1}^n f(\xi_i)\Delta x_i - I\right| < \frac{\varepsilon}{3}$$

取定这样的分割 \(P\)：
- 选取 \(\xi_i\) 使 \(f(\xi_i)\) 接近 \(M_i\)，则上和 \(U(P,f)\) 与 \(I\) 接近
- 选取 \(\xi_i\) 使 \(f(\xi_i)\) 接近 \(m_i\)，则下和 \(L(P,f)\) 与 \(I\) 接近

因此：
$$U(P,f) - L(P,f) < \varepsilon$$

**充分性** (\(\Leftarrow\))：

设对任意 \(\varepsilon > 0\)，存在分割 \(P\) 使 \(U(P,f) - L(P,f) < \varepsilon\)。

由上和与下和的性质：
- 对所有分割，\(L(P,f) \leq \underline{\int_a^b} f \leq \overline{\int_a^b} f \leq U(P,f)\)

因此：
$$0 \leq \overline{\int_a^b} f - \underline{\int_a^b} f \leq U(P,f) - L(P,f) < \varepsilon$$

由 \(\varepsilon\) 的任意性，上积分等于下积分，即 \(f\) Riemann 可积。

---

## 直观理解

### 几何解释

Darboux 和之差 \(U(P,f) - L(P,f)\) 表示函数在分割区间上的"振荡总和"：
- **上和 - 下和** = 小矩形条的总面积（函数上下波动部分）
- 当分割越来越细，这些小条面积趋于 0，函数可积

### 可积的充分条件

| 条件 | 结论 |
|-----|------|
| 连续 | 可积 |
| 单调 | 可积 |
| 只有有限个间断点 | 可积 |
| 间断点集测度为零 | 可积（Lebesgue判据）|

---

## 总结

| 要点 | 内容 |
|-----|------|
| **核心等价** | 可积 ⇔ 上下积分相等 ⇔ 上下和可任意接近 |
| **本质** | 函数"振荡"可被控制 |
| **应用** | 证明函数可积性、估计积分值 |

---

**文档状态**: ✅ 完成  
**最后更新**: 2026年4月5日
