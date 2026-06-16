---
msc_primary: '16

  - 16A99 - 16D10 - 16Z05'
lang: de
original: docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Ring (Algebra)
processed_at: '2026-04-05'
references:
  textbooks:
  - title: A First Course in Noncommutative Rings
    author: T. Y. Lam
    edition: 2nd
    publisher: Springer
    year: 2001
    isbn: '9780387951836'
    mr_number: MR1838439
    doi: 10.1007/978-1-4419-8616-0
  - title: Algebra
    author: Serge Lang
    edition: Revised 3rd
    publisher: Springer
    year: 2002
    isbn: '9780387953854'
    mr_number: MR1878556
    doi: 10.1007/978-1-4613-0041-0
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=16A99
---
# Ring (Algebra)

## Definition

Ein **Ring** $(R, +, \cdot)$ ist eine Menge $R$ mit zwei binären Operationen (Addition und Multiplikation), sodass gilt:

### (R1) $(R, +)$ ist eine abelsche Gruppe
- Assoziativität der Addition
- Kommutativität der Addition
- Neutrales Element $0$
- Inverse Elemente $-a$

### (R2) $(R, \cdot)$ ist ein Monoid
- Assoziativität der Multiplikation
- Neutrales Element $1$ (bei Ringen mit Eins)

### (R3) Distributivgesetze
Für alle $a, b, c \in R$ gilt:
$$a \cdot (b + c) = a \cdot b + a \cdot c$$
$$(a + b) \cdot c = a \cdot c + b \cdot c$$

## Ringhomomorphismus

Eine Abbildung $\varphi: R \rightarrow S$ zwischen Ringen heißt **Ringhomomorphismus**, wenn für alle $a, b \in R$ gilt:
1. $\varphi(a + b) = \varphi(a) + \varphi(b)$
2. $\varphi(a \cdot b) = \varphi(a) \cdot \varphi(b)$
3. $\varphi(1_R) = 1_S$ (falls beide Ringe Einselemente haben)

## Ideale

Ein **Ideal** $I \subseteq R$ ist eine additive Untergruppe mit der Eigenschaft:
$$r \cdot i \in I \quad \text{für alle } r \in R, i \in I$$

### Typen von Idealen

| Idealtyp | Definition |
|----------|------------|
| Linksideal | $r \cdot i \in I$ |
| Rechtsideal | $i \cdot r \in I$ |
| Zweiseitiges Ideal | Beides gilt |
| Primideal | $ab \in I \Rightarrow a \in I$ oder $b \in I$ |
| Maximalideal | Maximales echtes Ideal |

## Faktorring

Für ein Ideal $I \subseteq R$ ist der **Faktorring** definiert als:
$$R/I = \{r + I : r \in R\}$$

mit den Operationen:
- $(r + I) + (s + I) = (r + s) + I$
- $(r + I) \cdot (s + I) = (r \cdot s) + I$

---

**Sprachversionen**: [English](./Ring.md) | [Français](./../../fr/core/Anneau.md) | [日本語](./../../ja/core/環.md) | [中文](../../../02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md)

---

## 参考文献

- T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Springer, 2001, ISBN: 9780387951836 / MR1838439
- Serge Lang, *Algebra*, Revised 3rd ed., Springer, 2002, ISBN: 9780387953854 / MR1878556