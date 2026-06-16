---
msc_primary: 00A99
习题编号: ANA-200
学科: 实分析
知识点: 多复变-Monge-Ampere方程
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
title: 复Monge Ampere方程
references:
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
---
# 复 Monge-Ampère 方程

## 题目

**(a)** 证明紧 Kähler 流形上复 Monge-Ampère 方程的可解性（Yau）。

**(b)** 讨论退化复 Monge-Ampère 方程及其在复动力系统和复几何中的应用。

**(c)** 证明 Kolodziej 的 L^∞ 估计。

## 解答

### (a) Yau 定理

$$(\omega + dd^c\phi)^n = e^f \omega^n, \quad \int_M e^f \omega^n = \int_M \omega^n$$

连续性方法：$C^0$ 估计（Moser 迭代）、$C^2$ 估计（Yau）、$C^{2,\alpha}$（Evans-Krylov）。

### (b) 退化情形

允许右端为零集，解在 pluripotential 意义下定义，联系到复动力系统的 Green 函数。

### (c) Kolodziej 估计

若右端在 L^p (p>1)，则解有界。利用 Monge-Ampère 测度的容量估计。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845