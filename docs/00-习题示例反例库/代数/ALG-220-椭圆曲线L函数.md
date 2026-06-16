---
msc_primary: 00A99
习题编号: ALG-220
学科: 代数
知识点: 代数数论-L函数
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
title: ALG 220 椭圆曲线L函数
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/function
  wikipedia_url: https://en.wikipedia.org/wiki/Function_(mathematics)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E5%87%BD%E6%95%B0
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q11348
    consulted_at: '2026-06-16'
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
# 椭圆曲线的 L-函数

## 题目

**(a)** 定义椭圆曲线的 L-函数 L(E,s) 并讨论其解析延拓。

**(b)** 陈述 BSD 猜想并解释其组成部分。

**(c)** 讨论 BSD 的已知情形（Coates-Wiles、Gross-Zagier、Kolyvagin）。

## 解答

### (a) L-函数

$$L(E,s) = \prod_{p \nmid N} (1 - a_p p^{-s} + p^{1-2s})^{-1} \prod_{p|N} (\cdots)$$

Hasse：|a_p| ≤ 2√p。Wiles 等：L(E,s) = L(f_E,s)，模形式对应，故全纯。

### (b) BSD 猜想

$$\text{ord}_{s=1} L(E,s) = \text{rank } E(\mathbb{Q})$$
$$L^*(E,1) = \frac{\Omega_E \cdot \text{Reg}_E \cdot \#Ш(E) \cdot \prod c_p}{\#E(\mathbb{Q})_{\text{tors}}^2}$$

### (c) 已知结果

Coates-Wiles：CM 曲线，rank=0 时 L(1,0)≠0。

Gross-Zagier：Heegner 点与导数。Kolyvagin：Euler 系统，rank ≤ 1 情形。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845