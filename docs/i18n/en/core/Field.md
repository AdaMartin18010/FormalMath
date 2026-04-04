---
msc_primary: 12-XX
msc_secondary: ['12F10', '12E05']
lang: en
original: docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
---

# Field (Mathematics)

## Definition

A **field** $(K, +, \cdot)$ is a commutative ring with unity in which every nonzero element has a multiplicative inverse:

$$\forall a \in K \setminus \{0\}: \exists a^{-1} \in K \text{ such that } a \cdot a^{-1} = 1$$

## Properties

### Characteristic
The **characteristic** of a field is the smallest positive integer $p$ such that:
$$\underbrace{1 + 1 + \cdots + 1}_{p \text{ times}} = 0$$

If no such integer exists, the field has characteristic 0.

| Characteristic | Examples |
|----------------|----------|
| 0 | $\mathbb{Q}, \mathbb{R}, \mathbb{C}$ |
| $p$ (prime) | $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ |

## Field Extensions

A **field extension** $L/K$ is a field inclusion $K \subseteq L$.

### Degree of Extension
The **degree** $[L : K]$ is the dimension of $L$ as a $K$-vector space:
$$[L : K] = \dim_K(L)$$

### Tower Law
For field extensions $K \subseteq L \subseteq M$:
$$[M : K] = [M : L] \cdot [L : K]$$

### Algebraic Elements
An element $\alpha \in L$ is **algebraic** over $K$ if there exists a nonzero polynomial $f \in K[X]$ such that $f(\alpha) = 0$.

### Transcendental Elements
An element $\alpha \in L$ is **transcendental** over $K$ if it is not algebraic.

## Algebraic Closure

A field $K$ is **algebraically closed** if every non-constant polynomial $f \in K[X]$ has a root in $K$.

The **algebraic closure** $\overline{K}$ is the smallest algebraically closed field containing $K$.

## Finite Fields

For every prime power $q = p^n$, there exists up to isomorphism exactly one finite field with $q$ elements, denoted $\mathbb{F}_q$ or $\operatorname{GF}(q)$ (Galois Field).

### Properties of Finite Fields
- $\mathbb{F}_q^\times$ is cyclic
- $\mathbb{F}_{p^m} \subseteq \mathbb{F}_{p^n}$ if and only if $m \mid n$
- Frobenius automorphism: $\varphi(x) = x^p$
- Galois group: $\operatorname{Gal}(\mathbb{F}_{p^n}/\mathbb{F}_p) \cong \mathbb{Z}/n\mathbb{Z}$

## Galois Theory

### Galois Extension
A field extension $L/K$ is **Galois** if it is normal and separable.

### Galois Group
The **Galois group** is defined as:
$$\operatorname{Gal}(L/K) = \{\sigma \in \operatorname{Aut}(L) : \sigma|_K = \operatorname{id}_K\}$$

### Fundamental Theorem of Galois Theory
There is a bijective correspondence between subgroups of $\operatorname{Gal}(L/K)$ and intermediate fields between $K$ and $L$.

---

**Language Versions**: [Deutsch](../de/core/Körper.md) | [Français](../fr/core/Corps.md) | [日本語](../ja/core/体.md) | [中文](../../../02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md)
