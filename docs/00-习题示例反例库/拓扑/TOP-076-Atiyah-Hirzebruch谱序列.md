---
msc_primary: 00A99
习题编号: TOP-076
学科: 拓扑
知识点: 同伦论-广义上同调谱序列
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
title: Atiyah Hirzebruch谱序列
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/spectral+sequence
  wikipedia_url: https://en.wikipedia.org/wiki/Spectral_sequence
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E8%B0%B1%E5%BA%8F%E5%88%97
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Atiyah/
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q3503315
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
# Atiyah-Hirzebruch谱序列

## 题目

设 $h^*$ 是广义上同调理论。

**(a)** 陈述Atiyah-Hirzebruch谱序列：对CW复形 $X$，
$$E_2^{p,q} = H^p(X; h^q(\text{pt})) \Rightarrow h^{p+q}(X)$$

**(b)** 计算 $K^*(\mathbb{C}P^n)$（复K理论）。

**(c)** 讨论AHSS的微分与Steenrod运算的关系。

## 解答

### (a) AHSS陈述

**构造：**

由 $X$ 的骨架滤过 $X^{(0)} \subset X^{(1)} \subset \cdots$。

正合对 $(D, E)$，$D = \bigoplus h^*(X^{(p)})$，$E = \bigoplus h^*(X^{(p)}, X^{(p-1)})$。

$E_1^{p,q} = h^{p+q}(X^{(p)}, X^{(p-1)}) \cong C^p(X; h^q(\text{pt}))$。

$d_1$ 是胞腔上边缘，故 $E_2^{p,q} = H^p(X; h^q(\text{pt}))$。

### (b) 复射影空间的K理论

**计算：**

$h^0(\text{pt}) = \mathbb{Z}$，$h^1(\text{pt}) = 0$（复K理论）。

$E_2^{p,q} = H^p(\mathbb{C}P^n; \mathbb{Z})$ 对 $q$ 偶，0对 $q$ 奇。

$H^*(\mathbb{C}P^n) = \mathbb{Z}[x]/(x^{n+1})$，$|x| = 2$。

微分 $d_{2r+1} = 0$（奇数页）。

$d_2$ 由Atiyah-Hirzebruch公式，此处为0。

故谱序列退化，$K^0(\mathbb{C}P^n) = \mathbb{Z}^{n+1}$。

实际上 $K^0(\mathbb{C}P^n) = \mathbb{Z}[\xi]/((\xi-1)^{n+1})$。

### (c) 微分与Steenrod运算

**关系：**

对通常上同调 $h^* = H^*$，AHSS退化。

对拓扑K理论，$d_3$ 与 $Sq^3$ 有关。

一般：微分由Postnikov塔的 $k$-不变量决定。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845