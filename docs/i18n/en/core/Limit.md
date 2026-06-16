---
msc_primary: '26

  - 26A99 - 26A03 - 40A05'
lang: en
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Limit of a Sequence
processed_at: '2026-04-05'
references:
  textbooks:
  - title: Principles of Mathematical Analysis
    author: Walter Rudin
    edition: 3rd
    publisher: McGraw-Hill
    year: 1976
    isbn: '9780070542358'
    mr_number: MR0385023
  - title: Understanding Analysis
    author: Stephen Abbott
    edition: 2nd
    publisher: Springer
    year: 2015
    isbn: '9781493927111'
    doi: 10.1007/978-1-4939-2712-8
  - title: Real Mathematical Analysis
    author: Charles C. Pugh
    edition: 1st
    publisher: Springer
    year: 2002
    isbn: '9780387952970'
    mr_number: MR1639930
    doi: 10.1007/978-0-387-21676-7
  - title: Analysis I
    author: Terence Tao
    edition: 3rd
    publisher: Springer
    year: 2016
    isbn: '9789811017896'
    mr_number: MR3728289
    doi: 10.1007/978-981-10-1789-6
---
# Limit of a Sequence

## Definition

A sequence $(a_n)_{n \in \mathbb{N}}$ converges to a **limit** $L \in \mathbb{R}$ if:

$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall n \geq N: |a_n - L| < \varepsilon$$

Notation: $\lim_{n \to \infty} a_n = L$ or $a_n \to L$ as $n \to \infty$

## Properties

### Uniqueness
The limit of a convergent sequence is unique.

### Boundedness
Every convergent sequence is bounded.

### Algebraic Operations
Let $\lim_{n \to \infty} a_n = a$ and $\lim_{n \to \infty} b_n = b$:

| Operation | Rule |
|-----------|------|
| Sum | $\lim_{n \to \infty} (a_n + b_n) = a + b$ |
| Product | $\lim_{n \to \infty} (a_n \cdot b_n) = a \cdot b$ |
| Quotient | $\lim_{n \to \infty} \frac{a_n}{b_n} = \frac{a}{b}$ (if $b \neq 0$) |

## Convergence Criteria

### Monotone Convergence Theorem
Every monotone and bounded sequence converges.

### Cauchy Criterion
A sequence converges if and only if it is a Cauchy sequence:
$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall m, n \geq N: |a_m - a_n| < \varepsilon$$

## Infinite Limits

- $\lim_{n \to \infty} a_n = +\infty$: For all $M > 0$, there exists $N$ such that $a_n > M$ for all $n \geq N$
- $\lim_{n \to \infty} a_n = -\infty$: For all $M > 0$, there exists $N$ such that $a_n < -M$ for all $n \geq N$

---

**Language Versions**: [Deutsch](./../../de/core/Grenzwert.md) | [Français](./../../fr/core/Limite.md) | [日本語](./../../ja/core/極限.md) | [中文](../../../01-基础数学/集合论/01-集合论基础-国际标准版.md)

---

## 参考文献

- Walter Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, ISBN: 9780070542358 / MR0385023
- Stephen Abbott, *Understanding Analysis*, 2nd ed., Springer, 2015, ISBN: 9781493927111
- Charles C. Pugh, *Real Mathematical Analysis*, 1st ed., Springer, 2002, ISBN: 9780387952970 / MR1639930
- Terence Tao, *Analysis I*, 3rd ed., Springer, 2016, ISBN: 9789811017896 / MR3728289