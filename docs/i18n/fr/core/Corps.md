---
msc_primary: 12

  - 12F99
  - 12F10
  - 12E05
lang: fr
original: docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
title: Corps (mathématiques)
processed_at: '2026-04-05'
---
# Corps (mathématiques)

## Définition

Un **corps** $(K, +, \cdot)$ est un anneau commutatif unitaire dans lequel tout élément non nul possède un inverse multiplicatif:

$$\forall a \in K \setminus \{0\}: \exists a^{-1} \in K \text{ tel que } a \cdot a^{-1} = 1$$

## Propriétés

### Caractéristique
La **caractéristique** d'un corps est le plus petit entier positif $p$ tel que:
$$\underbrace{1 + 1 + \cdots + 1}_{p \text{ fois}} = 0$$

Si un tel entier n'existe pas, le corps est de caractéristique 0.

| Caractéristique | Exemple |
|-----------------|---------|
| 0 | $\mathbb{Q}, \mathbb{R}, \mathbb{C}$ |
| $p$ (premier) | $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ |

## Extensions de corps

Une **extension de corps** $L/K$ est une inclusion de corps $K \subseteq L$.

### Degré de l'extension
Le **degré** $[L : K]$ est la dimension de $L$ comme $K$-espace vectoriel:
$$[L : K] = \dim_K(L)$$

### Éléments algébriques
Un élément $\alpha \in L$ est **algébrique** sur $K$ s'il existe un polynôme $f \in K[X] \setminus \{0\}$ tel que $f(\alpha) = 0$.

### Éléments transcendants
Un élément $\alpha \in L$ est **transcendant** sur $K$ s'il n'est pas algébrique.

## Clôture algébrique

Un corps $K$ est **algébriquement clos** si tout polynôme non constant $f \in K[X]$ possède une racine dans $K$.

La **clôture algébrique** $\overline{K}$ est le plus petit corps algébriquement clos contenant $K$.

## Corps finis

Pour toute puissance de nombre premier $q = p^n$, il existe à isomorphisme près un unique corps fini à $q$ éléments, noté $\mathbb{F}_q$ ou $\operatorname{GF}(q)$.

### Propriétés des corps finis
- $\mathbb{F}_q^\times$ est cyclique
- $\mathbb{F}_{p^m} \subseteq \mathbb{F}_{p^n}$ ssi $m \mid n$
- Automorphisme de Frobenius: $\varphi(x) = x^p$

---

**Versions linguistiques**: [English](./../../en/core/Field.md) | [Deutsch](./../../de/core/Körper.md) | [日本語](./../../ja/core/体.md) | [中文](../../../02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md)
