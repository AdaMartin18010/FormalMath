---
msc_primary: 26

  - 26A99
  - 26A03
  - 40A05
lang: en
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Limit of a Sequence
processed_at: '2026-04-05'
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
