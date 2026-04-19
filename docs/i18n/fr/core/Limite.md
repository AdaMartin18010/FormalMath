---
msc_primary: 26

  - 26A99
  - 26A03
  - 40A05
lang: fr
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Limite (suite)
processed_at: '2026-04-05'
---
# Limite (suite)

## Définition

Une suite $(a_n)_{n \in \mathbb{N}}$ converge vers une **limite** $L \in \mathbb{R}$ si:

$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall n \geq N: |a_n - L| < \varepsilon$$

Notation: $\lim_{n \to \infty} a_n = L$ ou $a_n \to L$ quand $n \to \infty$

## Propriétés

### Unicité
La limite d'une suite convergente est unique.

### Bornitude
Toute suite convergente est bornée.

### Règles de calcul
Soient $\lim_{n \to \infty} a_n = a$ et $\lim_{n \to \infty} b_n = b$:

| Opération | Règle |
|-----------|-------|
| Somme | $\lim_{n \to \infty} (a_n + b_n) = a + b$ |
| Produit | $\lim_{n \to \infty} (a_n \cdot b_n) = a \cdot b$ |
| Quotient | $\lim_{n \to \infty} \frac{a_n}{b_n} = \frac{a}{b}$ (si $b \neq 0$) |

## Critères de convergence

### Convergence monotone
Toute suite monotone et bornée converge.

### Critère de Cauchy
Une suite converge si et seulement si c'est une suite de Cauchy:
$$\forall \varepsilon > 0: \exists N \in \mathbb{N}: \forall m, n \geq N: |a_m - a_n| < \varepsilon$$

## Limites infinies

- $\lim_{n \to \infty} a_n = +\infty$: Pour tout $M > 0$, il existe $N$ tel que $a_n > M$ pour tout $n \geq N$
- $\lim_{n \to \infty} a_n = -\infty$: Pour tout $M > 0$, il existe $N$ tel que $a_n < -M$ pour tout $n \geq N$

---

**Versions linguistiques**: [English](./../../en/core/Limit.md) | [Deutsch](./../../de/core/Grenzwert.md) | [日本語](./../../ja/core/極限.md) | [中文](../../../01-基础数学/集合论/01-集合论基础-国际标准版.md)
