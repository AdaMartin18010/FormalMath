---
msc_primary: 26A99
msc_secondary:
- 26A03
- 40A05
lang: de
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Grenzwert (Folge)
processed_at: '2026-04-05'
---
# Grenzwert (Folge)

## Definition

Eine Folge $(a_n)_{n \in \mathbb{N}}$ konvergiert gegen einen **Grenzwert** $L \in \mathbb{R}$, wenn gilt:

$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall n \geq N: |a_n - L| < \varepsilon$$

Schreibweise: $\lim_{n \to \infty} a_n = L$ oder $a_n \to L$ für $n \to \infty$

## Eigenschaften

### Eindeutigkeit
Der Grenzwert einer konvergenten Folge ist eindeutig bestimmt.

### Beschränktheit
Jede konvergente Folge ist beschränkt.

### Rechenregeln
Seien $\lim_{n \to \infty} a_n = a$ und $\lim_{n \to \infty} b_n = b$:

| Operation | Regel |
|-----------|-------|
| Summe | $\lim_{n \to \infty} (a_n + b_n) = a + b$ |
| Produkt | $\lim_{n \to \infty} (a_n \cdot b_n) = a \cdot b$ |
| Quotient | $\lim_{n \to \infty} \frac{a_n}{b_n} = \frac{a}{b}$ (falls $b \neq 0$) |

## Konvergenzkriterien

### Monotone Konvergenz
Jede monotone und beschränkte Folge konvergiert.

### Cauchy-Kriterium
Eine Folge konvergiert genau dann, wenn sie eine Cauchy-Folge ist:
$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall m, n \geq N: |a_m - a_n| < \varepsilon$$

## Uneigentliche Grenzwerte

- $\lim_{n \to \infty} a_n = +\infty$: Für alle $M > 0$ existiert $N$ mit $a_n > M$ für alle $n \geq N$
- $\lim_{n \to \infty} a_n = -\infty$: Für alle $M > 0$ existiert $N$ mit $a_n < -M$ für alle $n \geq N$

---

**Sprachversionen**: [English](./../../en/core/Limit.md) | [Français](./../../fr/core/Limite.md) | [日本語](./../../ja/core/極限.md) | [中文](../../../01-基础数学/集合论/01-集合论基础-国际标准版.md)
