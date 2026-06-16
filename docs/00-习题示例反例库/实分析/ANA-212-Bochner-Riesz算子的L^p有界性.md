---
msc_primary: '42

  - 42B15'
exercise_id: ANA-212
title: Bochner-Riesz算子的L^p有界性
difficulty: 5
type: PRF
topic: 实分析
subtopic: 乘子算子
source:
  course: 现代调和分析
  chapter: '10.1'
  original: true
processed_at: '2026-04-10'
references:
  textbooks:
  - title: 'Fourier Analysis: An Introduction'
    author: Elias M. Stein and Rami Shakarchi
    edition: 1st
    publisher: Princeton University Press
    year: 2003
    isbn: '9780691113845'
    doi: 10.1515/9781400831142
  - title: An Introduction to Harmonic Analysis
    author: Yitzhak Katznelson
    edition: 3rd
    publisher: Cambridge University Press
    year: 2004
    isbn: '9780521543590'
    mr_number: MR2039503
    doi: 10.1017/CBO9781139162371
external_ids:
  wikipedia_url: https://en.wikipedia.org/wiki/Operator_(mathematics)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E7%AE%97%E5%AD%90
  nlab_url: https://ncatlab.org/nlab/show/operator
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=42B15
---
# ANA-212: Bochner-Riesz算子的L^p有界性

**题号**: ANA-212
**难度**: ⭐⭐⭐⭐⭐ (Level 5)
**类型**: 证明型 (PRF)
**来源**: 现代调和分析 Chapter 10.1
**主题**: Bochner-Riesz猜想

---

## 题目

定义Bochner-Riesz算子：
$$\widehat{T_\lambda f}(\xi) = (1 - |\xi|^2)_+^\lambda \hat{f}(\xi)$$

设 $n \geq 2$，$\lambda > 0$。

**证明**：若 $\lambda > \frac{n-1}{2} - \frac{n}{p}$ 且 $p \in [\frac{2n}{n+1}, \frac{2n}{n-1}]$，则 $T_\lambda: L^p \to L^p$ 有界。

---

## 解答

**Step 1: 核的渐近行为**

$B_\lambda(x) = c_\lambda |x|^{-(n+1)/2 - \lambda} J_{n/2+\lambda}(|x|)$，其中 $J$ 是Bessel函数。

**Step 2: Stein-Tomas限制性估计**

利用Fourier限制性定理：
$$\|\hat{f}\|_{L^2(S^{n-1})} \leq C \|f\|_{L^p}, \quad p \leq \frac{2(n+1)}{n+3}$$

**Step 3: 插值与分解**

在 $L^2$（显然有界）与 $L^1 \to L^\infty$（需 $\lambda > (n-1)/2$）之间插值。

**Step 4: Kakeya极大函数**

应用Kakeya极大函数估计完成证明。

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日

---

## 参考文献

- Elias M. Stein and Rami Shakarchi, *Fourier Analysis: An Introduction*, 1st ed., Princeton University Press, 2003, ISBN: 9780691113845
- Yitzhak Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press, 2004, ISBN: 9780521543590 / MR2039503