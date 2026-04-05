---
msc_primary: 16A99
msc_secondary:
- 16D10
- 16Z05
lang: en
original: docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Ring (Mathematics)
processed_at: '2026-04-05'
---
# Ring (Mathematics)

## Definition

A **ring** $(R, +, \cdot)$ is a set $R$ equipped with two binary operations (addition and multiplication) such that:

### (R1) $(R, +)$ is an Abelian Group
- Associativity of addition: $(a + b) + c = a + (b + c)$
- Commutativity of addition: $a + b = b + a$
- Additive identity: $0 \in R$ with $a + 0 = a$
- Additive inverses: $-a$ for each $a \in R$

### (R2) $(R, \cdot)$ is a Monoid
- Associativity of multiplication: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
- Multiplicative identity: $1 \in R$ with $a \cdot 1 = a$ (for rings with unity)

### (R3) Distributive Laws
For all $a, b, c \in R$:
$$a \cdot (b + c) = a \cdot b + a \cdot c$$
$$(a + b) \cdot c = a \cdot c + b \cdot c$$

## Ring Homomorphism

A map $\varphi: R \rightarrow S$ between rings is a **ring homomorphism** if for all $a, b \in R$:
1. $\varphi(a + b) = \varphi(a) + \varphi(b)$
2. $\varphi(a \cdot b) = \varphi(a) \cdot \varphi(b)$
3. $\varphi(1_R) = 1_S$ (if both rings have unity)

## Ideals

An **ideal** $I \subseteq R$ is an additive subgroup satisfying:
$$r \cdot i \in I \quad \text{for all } r \in R, i \in I$$

### Types of Ideals

| Ideal Type | Definition |
|------------|------------|
| Left Ideal | $r \cdot i \in I$ for all $r \in R, i \in I$ |
| Right Ideal | $i \cdot r \in I$ for all $r \in R, i \in I$ |
| Two-sided Ideal | Both left and right ideal |
| Prime Ideal | $ab \in I \Rightarrow a \in I$ or $b \in I$ |
| Maximal Ideal | Proper ideal not contained in any larger proper ideal |

## Quotient Ring

For an ideal $I \subseteq R$, the **quotient ring** is defined as:
$$R/I = \{r + I : r \in R\}$$

with operations:
- $(r + I) + (s + I) = (r + s) + I$
- $(r + I) \cdot (s + I) = (r \cdot s) + I$

## Special Types of Rings

| Ring Type | Definition |
|-----------|------------|
| Commutative Ring | $a \cdot b = b \cdot a$ |
| Integral Domain | Commutative ring with no zero divisors |
| Field | Commutative ring where every nonzero element is a unit |
| Principal Ideal Domain (PID) | Integral domain where every ideal is principal |
| Unique Factorization Domain (UFD) | Integral domain with unique factorization |

---

**Language Versions**: [Deutsch](./Ring.md) | [Français](./../../fr/core/Anneau.md) | [日本語](./../../ja/core/環.md) | [中文](../../../02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md)
