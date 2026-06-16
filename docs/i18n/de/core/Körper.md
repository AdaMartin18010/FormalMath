---
msc_primary: '12

  - 12F99 - 12F10 - 12E05'
lang: de
original: docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Körper (Algebra)
processed_at: '2026-04-05'
references:
  textbooks:
  - title: Abstract Algebra
    author: David S. Dummit and Richard M. Foote
    edition: 3rd
    publisher: Wiley
    year: 2003
    isbn: '9780471433347'
    mr_number: MR2286236
    doi: 10.1002/9781118214413
  - title: Algebra
    author: Michael Artin
    edition: 2nd
    publisher: Pearson
    year: 2010
    isbn: '9780132413770'
    doi: 10.1007/978-1-4613-0041-0
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=12F99
---
# Körper (Algebra)

## Definition

Ein **Körper** $(K, +, \cdot)$ ist ein kommutativer Ring mit Einselement, in dem jedes von Null verschiedene Element ein multiplikatives Inverses besitzt:

$$\forall a \in K \setminus \{0\}: \exists a^{-1} \in K \text{ mit } a \cdot a^{-1} = 1$$

## Eigenschaften

### Charakteristik
Die **Charakteristik** eines Körpers ist die kleinste positive Zahl $p$, sodass:
$$\underbrace{1 + 1 + \cdots + 1}_{p \text{ mal}} = 0$$

Falls keine solche Zahl existiert, hat der Körper Charakteristik 0.

| Charakteristik | Beispiel |
|----------------|----------|
| 0 | $\mathbb{Q}, \mathbb{R}, \mathbb{C}$ |
| $p$ (Primzahl) | $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ |

## Körpererweiterungen

Eine **Körpererweiterung** $L/K$ ist eine Körperinklusion $K \subseteq L$.

### Grad der Erweiterung
Der **Grad** $[L : K]$ ist die Dimension von $L$ als $K$-Vektorraum:
$$[L : K] = \dim_K(L)$$

### Algebraische Elemente
Ein Element $\alpha \in L$ heißt **algebraisch** über $K$, wenn es ein Polynom $f \in K[X] \setminus \{0\}$ gibt mit $f(\alpha) = 0$.

### Transzendente Elemente
Ein Element $\alpha \in L$ heißt **transzendent** über $K$, wenn es nicht algebraisch ist.

## Algebraischer Abschluss

Ein Körper $K$ heißt **algebraisch abgeschlossen**, wenn jedes nicht-konstante Polynom $f \in K[X]$ eine Nullstelle in $K$ besitzt.

Der **algebraische Abschluss** $\overline{K}$ ist der kleinste algebraisch abgeschlossene Körper, der $K$ enthält.

## Endliche Körper

Für jede Primzahlpotenz $q = p^n$ existiert bis auf Isomorphie genau ein endlicher Körper mit $q$ Elementen, bezeichnet mit $\mathbb{F}_q$ oder $\operatorname{GF}(q)$.

### Eigenschaften endlicher Körper
- $\mathbb{F}_q^\times$ ist zyklisch
- $\mathbb{F}_{p^m} \subseteq \mathbb{F}_{p^n}$ gdw. $m \mid n$
- Frobenius-Automorphismus: $\varphi(x) = x^p$

---

**Sprachversionen**: [English](./../../en/core/Field.md) | [Français](./../../fr/core/Corps.md) | [日本語](./../../ja/core/体.md) | [中文](../../../02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md)

---

## 参考文献

- David S. Dummit and Richard M. Foote, *Abstract Algebra*, 3rd ed., Wiley, 2003, ISBN: 9780471433347 / MR2286236
- Michael Artin, *Algebra*, 2nd ed., Pearson, 2010, ISBN: 9780132413770