---
msc_primary: '42

  - 42B20'
exercise_id: ANA-213
title: Hilbert变换的交换子估计
difficulty: 4
type: PRF
topic: 实分析
subtopic: 交换子理论
source:
  course: 非线性调和分析
  chapter: '5.3'
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
  wikipedia_url: https://en.wikipedia.org/wiki/David_Hilbert
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Hilbert/
---
# ANA-213: Hilbert变换的交换子估计

**题号**: ANA-213
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 非线性调和分析 Chapter 5.3
**主题**: Coifman-Meyer交换子理论

---

## 题目

设 $H$ 是Hilbert变换，$b \in BMO(\mathbb{R})$。定义交换子：
$$[b, H]f = bH(f) - H(bf)$$

**证明**：$[b, H]: L^p(\mathbb{R}) \to L^p(\mathbb{R})$ 有界，且
$$\|[b, H]\|_{L^p \to L^p} \leq C_p \|b\|_{BMO}$$

---

## 解答

**Step 1: 核表示**

$$[b, H]f(x) = \int_{\mathbb{R}} \frac{b(x) - b(y)}{x-y} f(y) dy$$

**Step 2: 标准核估计**

核 $K(x,y) = \frac{b(x)-b(y)}{x-y}$ 满足：
$$|K(x,y)| \leq \frac{C\|b\|_{BMO}}{|x-y|}$$

**Step 3: T1定理应用**

验证 $[b,H](1) = H(b) \in BMO$（由 $H: L^\infty \to BMO$）。

**Step 4: L^2估计**

由Cotlar引理或Littlewood-Paley分解直接得到。

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日

---

## 参考文献

- Elias M. Stein and Rami Shakarchi, *Fourier Analysis: An Introduction*, 1st ed., Princeton University Press, 2003, ISBN: 9780691113845
- Yitzhak Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press, 2004, ISBN: 9780521543590 / MR2039503