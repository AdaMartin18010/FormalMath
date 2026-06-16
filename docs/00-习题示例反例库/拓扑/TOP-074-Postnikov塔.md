---
msc_primary: 00A99
习题编号: TOP-074
学科: 拓扑
知识点: 同伦论-Postnikov塔
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
title: Postnikov塔
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
# Postnikov塔

## 题目

**(a)** 定义Postnikov塔：空间序列 $\cdots \to X_n \to X_{n-1} \to \cdots \to X_1$，其中
- $X_n \to X_{n-1}$ 是纤维化，纤维 $K(\pi_n(X), n)$
- $\pi_i(X_n) = 0$ 对 $i > n$
- $X \to X_n$ 诱导同构 $\pi_i(X) \cong \pi_i(X_n)$ 对 $i \leq n$

**(b)** 证明任意道路连通CW复形有Postnikov塔。

**(c)** 用Postnikov塔计算 $[X, K(\pi, n)]$。

## 解答

### (a) Postnikov塔定义

**构造：**

通过逐次附着高维胞腔杀死高阶同伦群。

$X_n$ 有万有性质：从 $X$ 到 $n$-截断空间的映射。

### (b) 存在性证明

**证明概要：**

对CW复形 $X$，归纳构造 $X_n$。

$X_1 = K(\pi_1(X), 1)$。

假设 $X_{n-1}$ 已构造，$k$-不变量 $k_n \in H^{n+1}(X_{n-1}; \pi_n(X))$。

$X_n$ 为 $k_n$ 的homotopy fiber。

### (c) Eilenberg-MacLane空间的映射

**解答：**

$$[X, K(\pi, n)] \cong H^n(X; \pi)$$

由Hurewicz定理和万有系数：

$K(\pi, n)$ 是 $(n-1)$-连通，$H_n(K(\pi, n)) = \pi$。

映射的同伦类由诱导的上同调类决定。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845