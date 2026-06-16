---
msc_primary: 00A99
习题编号: ANA-104
学科: 实分析
知识点: 调和分析-Fourier级数L^2理论
难度: ⭐⭐⭐⭐
预计时间: 25分钟
title: Fourier级数的L2收敛
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/convergence
  wikipedia_url: https://en.wikipedia.org/wiki/Convergence_(mathematics)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E6%94%B6%E6%95%9B
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Fourier/
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
# Fourier级数的L²收敛

## 题目

设 $f \in L^2[-\pi, \pi]$，Fourier系数：
$$\hat{f}(n) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) e^{-inx} dx$$

部分和：$S_N f(x) = \sum_{|n| \leq N} \hat{f}(n) e^{inx}$

(a) 证明 $\{e^{inx}/\sqrt{2\pi}\}_{n \in \mathbb{Z}}$ 是 $L^2[-\pi,\pi]$ 的标准正交基。

(b) 证明Parseval等式：
$$\frac{1}{2\pi}\int_{-\pi}^{\pi} |f(x)|^2 dx = \sum_{n=-\infty}^{\infty} |\hat{f}(n)|^2$$

(c) 证明 $S_N f \to f$ 于 $L^2$。

## 解答

### (a) 标准正交基

**证明：**

**正交性**：对 $m \neq n$：
$$\int_{-\pi}^{\pi} e^{imx} \overline{e^{inx}} dx = \int_{-\pi}^{\pi} e^{i(m-n)x} dx = 0$$

对 $m = n$：积分 $= 2\pi$。

**完备性**：

Stone-Weierstrass定理：三角多项式在 $C[-\pi,\pi]$ 中一致稠密。

$C[-\pi,\pi]$ 在 $L^2$ 中稠密。

因此三角多项式在 $L^2$ 中稠密，即 $\{e^{inx}\}$ 张成稠密子空间。$\square$

### (b) Parseval等式

**证明：**

由(a)，对标准正交基 $\{e_n\}$，任意 $f \in L^2$：
$$f = \sum_{n=-\infty}^{\infty} \langle f, e_n \rangle e_n$$

且：
$$\|f\|^2 = \sum_n |\langle f, e_n \rangle|^2$$

计算内积：
$$\langle f, \frac{e^{inx}}{\sqrt{2\pi}} \rangle = \frac{1}{\sqrt{2\pi}} \int_{-\pi}^{\pi} f(x) e^{-inx} dx = \sqrt{2\pi} \hat{f}(n)$$

因此：
$$\|f\|_2^2 = 2\pi \sum_n |\hat{f}(n)|^2$$

即Parseval等式。$\square$

### (c) L²收敛

**证明：**

$S_N f$ 是 $f$ 在 $\text{span}\{e^{inx}: |n| \leq N\}$ 上的正交投影。

由正交投影的性质：
$$\|f - S_N f\|_2^2 = \|f\|_2^2 - \|S_N f\|_2^2 = 2\pi \sum_{|n| > N} |\hat{f}(n)|^2$$

由 $\sum |\hat{f}(n)|^2 < \infty$（Parseval），余项趋于0。

故 $\|f - S_N f\|_2 \to 0$。$\square$

## 证明技巧

1. **正交基验证**：正交性+完备性
2. **稠密性传递**：$C \subset L^2$ 的稠密性
3. **投影性质**：最佳逼近的几何解释

## 常见错误

- ❌ 混淆点态收敛与 $L^2$ 收敛
- ❌ Parseval等式中归一化常数错误
- ❌ 忘记三角多项式在 $C$ 中稠密需周期性条件

## 变式练习

**变式1：** 设 $f(x) = x$ 于 $[-\pi, \pi]$，求Fourier级数并验证Parseval等式。

**变式2：** 证明 $\sum_{n=1}^\infty \frac{1}{n^2} = \frac{\pi^2}{6}$ 用Fourier级数。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845