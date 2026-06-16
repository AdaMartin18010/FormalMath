---
msc_primary: '20

  - 20A99 - 20A05 - 20B30'
lang: de
original: docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Gruppe (Mathematik)
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
  - title: An Introduction to the Theory of Groups
    author: Joseph J. Rotman
    edition: 4th
    publisher: Springer
    year: 1995
    isbn: '9780387942858'
    mr_number: MR1307623
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=20A99
---
# Gruppe (Mathematik)

## Definition

Eine **Gruppe** $(G, \cdot)$ ist eine Menge $G$ zusammen mit einer binären Operation $\cdot: G \times G \rightarrow G$, die folgende Axiome erfüllt:

### (G1) Assoziativität
Für alle $a, b, c \in G$ gilt:
$$(a \cdot b) \cdot c = a \cdot (b \cdot c)$$

### (G2) Neutrales Element
Es existiert ein Element $e \in G$, sodass für alle $a \in G$ gilt:
$$e \cdot a = a \cdot e = a$$

### (G3) Inverses Element
Für jedes $a \in G$ existiert ein Element $a^{-1} \in G$, sodass gilt:
$$a \cdot a^{-1} = a^{-1} \cdot a = e$$

## Spezielle Gruppenarten

| Begriff | Definition | Beispiel |
|---------|------------|----------|
| Abelsche Gruppe | Kommutative Gruppe: $a \cdot b = b \cdot a$ | $(\mathbb{Z}, +)$ |
| Endliche Gruppe | $|G| < \infty$ | Symmetrische Gruppe $S_n$ |
| Zyklische Gruppe | Von einem Element erzeugt | $\mathbb{Z}/n\mathbb{Z}$ |

## Wichtige Sätze

### Satz von Lagrange
Ist $H \leq G$ eine Untergruppe einer endlichen Gruppe $G$, so gilt:
$$|G| = |H| \cdot [G : H]$$

### Erster Isomorphiesatz
Für einen Gruppenhomomorphismus $\varphi: G \rightarrow H$ gilt:
$$G / \ker(\varphi) \cong \operatorname{im}(\varphi)$$

## Anwendungen

Gruppen finden Anwendung in:
- **Geometrie**: Symmetriegruppen
- **Physik**: Darstellungstheorie
- **Kryptographie**: Primzahlgruppen

## Verwandte Konzepte

- Untergruppe
- Normalteiler
- Faktorgruppe
- Gruppenhomomorphismus

---

**Sprachversionen**: [English](./../../en/core/Group.md) | [Français](./../../fr/core/Groupe.md) | [日本語](./../../ja/core/群.md) | [中文](../../../02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md)

---

## 参考文献

- David S. Dummit and Richard M. Foote, *Abstract Algebra*, 3rd ed., Wiley, 2003, ISBN: 9780471433347 / MR2286236
- Joseph J. Rotman, *An Introduction to the Theory of Groups*, 4th ed., Springer, 1995, ISBN: 9780387942858 / MR1307623