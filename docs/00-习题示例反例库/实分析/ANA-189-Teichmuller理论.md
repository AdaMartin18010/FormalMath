---
msc_primary: 00A99
习题编号: ANA-189
学科: 实分析
知识点: 复分析-Teichmuller理论
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
title: Teichmuller理论
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
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
# Teichmüller 理论

## 题目

**(a)** 定义 Teichmüller 空间 $T_g$ 并证明其复结构。

**(b)** 证明 Teichmüller 唯一性定理：在每个拟共形同伦类中存在唯一的极值映射。

**(c)** 讨论 Teichmüller 空间的度量和曲率。

## 解答

### (a) Teichmüller 空间

$$T_g = \{(X, f) : X \text{ 亏格 } g \text{ Riemann 面}, f: X_0 \to X\} / \sim$$
模空间的万有覆盖，复维 $3g-3$。

### (b) Teichmüller 唯一性

极值映射由全纯二次微分 $\phi dz^2$ 诱导，Beltrami 微分 $\mu = k \frac{\bar{\phi}}{|\phi|}$。

### (c) Weil-Petersson 度规

$\langle \mu, \nu \rangle = \int_X \mu \bar{\nu} \cdot (\text{Im } z)^2 dA$，负曲率（Wolpert）。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845