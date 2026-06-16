---
msc_primary: '20

  - 20A99 - 20A05 - 20B30'
lang: fr
original: docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Groupe (mathématiques)
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
# Groupe (mathématiques)

## Définition

Un **groupe** $(G, \cdot)$ est un ensemble $G$ muni d'une opération binaire $\cdot: G \times G \rightarrow G$ satisfaisant les axiomes suivants:

### (G1) Associativité
Pour tous $a, b, c \in G$:
$$(a \cdot b) \cdot c = a \cdot (b \cdot c)$$

### (G2) Élément neutre
Il existe un élément $e \in G$ tel que pour tout $a \in G$:
$$e \cdot a = a \cdot e = a$$

### (G3) Élément inverse
Pour tout $a \in G$, il existe un élément $a^{-1} \in G$ tel que:
$$a \cdot a^{-1} = a^{-1} \cdot a = e$$

## Types de groupes

| Terme | Définition | Exemple |
|-------|------------|---------|
| Groupe abélien | Groupe commutatif: $a \cdot b = b \cdot a$ | $(\mathbb{Z}, +)$ |
| Groupe fini | $|G| < \infty$ | Groupe symétrique $S_n$ |
| Groupe cyclique | Engendré par un seul élément | $\mathbb{Z}/n\mathbb{Z}$ |

## Théorèmes fondamentaux

### Théorème de Lagrange
Si $H \leq G$ est un sous-groupe d'un groupe fini $G$, alors:
$$|G| = |H| \cdot [G : H]$$

### Premier théorème d'isomorphisme
Pour un homomorphisme de groupes $\varphi: G \rightarrow H$:
$$G / \ker(\varphi) \cong \operatorname{im}(\varphi)$$

## Applications

Les groupes trouvent des applications en:
- **Géométrie**: Groupes de symétrie
- **Physique**: Théorie des représentations
- **Cryptographie**: Groupes de nombres premiers

## Concepts liés

- Sous-groupe
- Sous-groupe distingué
- Groupe quotient
- Homomorphisme de groupes

---

**Versions linguistiques**: [English](./../../en/core/Group.md) | [Deutsch](./../../de/core/Gruppe.md) | [日本語](./../../ja/core/群.md) | [中文](../../../02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md)

---

## 参考文献

- David S. Dummit and Richard M. Foote, *Abstract Algebra*, 3rd ed., Wiley, 2003, ISBN: 9780471433347 / MR2286236
- Joseph J. Rotman, *An Introduction to the Theory of Groups*, 4th ed., Springer, 1995, ISBN: 9780387942858 / MR1307623