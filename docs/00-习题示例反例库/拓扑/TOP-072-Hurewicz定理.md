---
msc_primary: 00A99
习题编号: TOP-072
学科: 拓扑
知识点: 同伦论-Hurewicz定理
难度: ⭐⭐⭐⭐
预计时间: 40分钟
title: Hurewicz定理
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
# Hurewicz定理

## 题目

**(a)** 定义Hurewicz同态 $h: \pi_n(X) \to H_n(X)$，将同伦类映至其代表映射的诱导同调。

**(b)** 证明Hurewicz定理：设 $X$ 是 $(n-1)$-连通空间（$n \geq 2$），则 $h: \pi_n(X) \to H_n(X)$ 是同构。

**(c)** 用Hurewicz定理计算 $\pi_3(S^2)$ 的部分信息。

## 解答

### (a) Hurewicz同态

**定义：**

对 $[f] \in \pi_n(X)$，$f: S^n \to X$，诱导
$$f_*: H_n(S^n) \to H_n(X)$$

$H_n(S^n) = \mathbb{Z}$，设生成元为 $[S^n]$。

$$h([f]) = f_*([S^n]) \in H_n(X)$$

### (b) Hurewicz定理

**证明概要：**

**Step 1**：$n=1$ 情形是Abel化，需要调整。

**Step 2**：$n \geq 2$，$X$ $(n-1)$-连通。

用万有系数定理和Whitehead定理。

**Step 3**：构造 $K(\pi, n)$ 空间。

$X$ 有CW逼近，$n-1$ 骨架为点。

由胞腔同调，$H_n(X) \cong \pi_n(X)$。

### (c) $\pi_3(S^2)$ 计算

**解答：**

$S^2$ 是1-连通，但非2-连通（$\pi_2(S^2) = \mathbb{Z}$）。

对纤维化 $S^1 \to S^3 \to S^2$（Hopf纤维化），长正合列：
$$\cdots \to \pi_3(S^1) \to \pi_3(S^3) \to \pi_3(S^2) \to \pi_2(S^1) \to \cdots$$

$\pi_3(S^1) = \pi_2(S^1) = 0$，$\pi_3(S^3) = \mathbb{Z}$。

故 $\pi_3(S^2) = \mathbb{Z}$，由Hopf映射生成。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845