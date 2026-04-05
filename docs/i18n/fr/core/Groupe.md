---
msc_primary: 20A99
msc_secondary:
- 20A05
- 20B30
lang: fr
original: docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Groupe (mathématiques)
processed_at: '2026-04-05'
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

- [Sous-groupe](./Sous-groupe.md)
- [Sous-groupe distingué](./Sous-groupe-distingué.md)
- [Groupe quotient](./Groupe-quotient.md)
- [Homomorphisme de groupes](./Homomorphisme.md)

---

**Versions linguistiques**: [English](./../../en/core/Group.md) | [Deutsch](./../../de/core/Gruppe.md) | [日本語](./../../ja/core/群.md) | [中文](../../../02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md)
