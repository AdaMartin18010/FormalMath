---
msc_primary: 16-XX
msc_secondary: ['16D10', '16Z05']
lang: fr
original: docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md
translation_status: completed
translator: FormalMath i18n System
date: 2026-04-04
---

# Anneau (mathématiques)

## Définition

Un **anneau** $(R, +, \cdot)$ est un ensemble $R$ muni de deux opérations binaires (addition et multiplication) telles que:

### (R1) $(R, +)$ est un groupe abélien
- Associativité de l'addition
- Commutativité de l'addition
- Élément neutre $0$
- Éléments inverses $-a$

### (R2) $(R, \cdot)$ est un monoïde
- Associativité de la multiplication
- Élément neutre $1$ (pour les anneaux unitaires)

### (R3) Lois de distributivité
Pour tous $a, b, c \in R$:
$$a \cdot (b + c) = a \cdot b + a \cdot c$$
$$(a + b) \cdot c = a \cdot c + b \cdot c$$

## Homomorphisme d'anneaux

Une application $\varphi: R \rightarrow S$ entre anneaux est un **homomorphisme d'anneaux** si pour tous $a, b \in R$:
1. $\varphi(a + b) = \varphi(a) + \varphi(b)$
2. $\varphi(a \cdot b) = \varphi(a) \cdot \varphi(b)$
3. $\varphi(1_R) = 1_S$ (si les deux anneaux ont un élément unité)

## Idéaux

Un **idéal** $I \subseteq R$ est un sous-groupe additif vérifiant:
$$r \cdot i \in I \quad \text{pour tous } r \in R, i \in I$$

### Types d'idéaux

| Type d'idéal | Définition |
|--------------|------------|
| Idéal à gauche | $r \cdot i \in I$ |
| Idéal à droite | $i \cdot r \in I$ |
| Idéal bilatère | Les deux conditions sont satisfaites |
| Idéal premier | $ab \in I \Rightarrow a \in I$ ou $b \in I$ |
| Idéal maximal | Idéal propre maximal |

## Anneau quotient

Pour un idéal $I \subseteq R$, l'**anneau quotient** est défini par:
$$R/I = \{r + I : r \in R\}$$

avec les opérations:
- $(r + I) + (s + I) = (r + s) + I$
- $(r + I) \cdot (s + I) = (r \cdot s) + I$

---

**Versions linguistiques**: [English](../en/core/Ring.md) | [Deutsch](../de/core/Ring.md) | [日本語](../ja/core/環.md) | [中文](../../../02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md)
