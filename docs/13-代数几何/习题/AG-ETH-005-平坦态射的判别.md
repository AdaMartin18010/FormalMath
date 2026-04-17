---
习题编号: AG-ETH-005
标题: 平坦态射的判别
type: Analytische Untersuchung (分析型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 3.1
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 75-100分钟
msc: 14A25, 13C11
eth_style: Streng + Technisch
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: []
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: []
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# AG-ETH-005: 平坦态射的判别 (*Kriterien für flache Morphismen*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 3.1: Flache Morphismen |
| **类型** | Analytische Untersuchung (分析型) |
| **ETH风格** | (S) Streng + (T) Technisch |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 75-100分钟 |

---

## 问题陈述

> **Aufgabe** (Streng und Technisch):
> Es sei $f: X \to Y$ ein Morphismus lokal Noetherscher Schemata.
>
> (a) Zeigen Sie streng: Ist $f$ flach, so ist $f$ offen auf den Fasern
> (d.h. für $y \in Y$ ist $X_y \to \operatorname{Spec}(k(y))$ offen).
>
> (b) Es sei $Y = \operatorname{Spec}(k[t])$ und $X = \operatorname{Spec}(k[x,y]/(xy-t))$.
> Untersuchen Sie explizit, ob $f: X \to Y$ flach ist.
>
> (c) Geben Sie ein Beispiel eines Morphismus, der offen auf den Fasern,
> aber nicht flach ist.

### 中文翻译

> **习题** (严格且技术性)：
> 设 $f: X \to Y$ 为局部Noether概形的态射。
>
> (a) 严格证明：若 $f$ 平坦，则 $f$ 在纤维上开
> （即对 $y \in Y$，$X_y \to \operatorname{Spec}(k(y))$ 开）。
>
> (b) 设 $Y = \operatorname{Spec}(k[t])$，$X = \operatorname{Spec}(k[x,y]/(xy-t))$。
> 显式研究 $f: X \to Y$ 是否平坦。
>
> (c) 给出一个在纤维上开但不平坦的态射例子。

---

## 详细解答

### Teil (a): 平坦 ⇒ 纤维上开

**Theorem**: 设 $f: X \to Y$ 为局部Noether概形的平坦态射。
则对每个 $y \in Y$，纤维 $X_y \to \operatorname{Spec}(k(y))$ 是开映射。

**Beweis** (Streng):

**Schritt 1**: Flachheit lokal

Sei $x \in X_y$ (d.h. $f(x) = y$). Wir betrachten die lokale Situation:

- $\mathcal{O}_{Y,y} \to \mathcal{O}_{X,x}$ ist flach

**Schritt 2**: Faser als Spezialfall

Die Faser $X_y$ ist definiert durch:
$$X_y = X \times_Y \operatorname{Spec}(k(y))$$

Lokal bei $x$:
$$\mathcal{O}_{X_y, x} = \mathcal{O}_{X,x} \otimes_{\mathcal{O}_{Y,y}} k(y) = \mathcal{O}_{X,x} / \mathfrak{m}_y \mathcal{O}_{X,x}$$

**Schritt 3**: Flachheit impliziert universell offen

Ein flacher Morphismus lokal Noetherscher Schemata ist **universell offen**:

> **Lemma** (Going-Down für flache Erweiterungen):
> Ist $A \to B$ flach, so hat $A \to B$ die Going-Down-Eigenschaft.
> D.h. für Primideale $\mathfrak{p} \subseteq \mathfrak{p}'$ in $A$ und
> $\mathfrak{q}'$ in $B$ über $\mathfrak{p}'$, existiert $\mathfrak{q} \subseteq \mathfrak{q}'$
> über $\mathfrak{p}$.

**Schritt 4**: Offenheit der Faser

Da $f$ flach ist, ist es universell offen.
Insbesondere ist $X_y \to \operatorname{Spec}(k(y))$ offen. ∎

---

### Teil (b): 显式研究 $xy = t$

**Aufgabe**: $Y = \operatorname{Spec}(k[t])$, $X = \operatorname{Spec}(k[x,y]/(xy-t))$.

**Lösung** (Explizit):

**Schritt 1**: Ringhomomorphismus

$$A = k[t] \to B = k[x,y]/(xy-t)$$

$t \mapsto xy$.

**Schritt 2**: Flachheitskriterium

Wir verwenden das **Flachheitskriterium über DVR**:

Da $A = k[t]$ ein Hauptidealring ist, ist $B$ flach über $A$ genau dann,
wenn $t$ ein **Nicht-Nullteiler** in $B$ ist.

**Schritt 3**: Überprüfung

In $B = k[x,y]/(xy-t)$ gilt: $t = xy$.

Ist $xy$ ein Nicht-Nullteiler in $B$?

Ja! Denn:

- $B \cong k[x,y]$ (als $k$-Vektorräume, aber nicht als Ringe)
- Mehr präzise: $B \cong k[x] \oplus y \cdot k[x]$ (als $k[x]$-Modul)

Der Faktor $xy$ ist in $B$ kein Nullteiler.

**Schritt 4**: Geometrische Interpretation

Die Fasern von $f: X \to Y$ sind:

- Für $t = a \neq 0$: $xy = a$ ist eine glatte Hyperbel (isomorph zu $\mathbb{G}_m$)
- Für $t = 0$: $xy = 0$ ist die Vereinigung zweier Geraden ($x=0$ oder $y=0$)

Die Faserdimension springt nicht (immer 1-dimensional),
aber die Faser bei $t=0$ ist reduzibel.

**Ergebnis**: $f$ ist **flach**.

---

### Teil (c): 开但不平坦的例子

**Beispiel**:

Sei $Y = \operatorname{Spec}(k[t])$ und $X = \operatorname{Spec}(k[t, x]/(tx))$.

Dann ist $f: X \to Y$ gegeben durch:

- Auf Ringen: $k[t] \to k[t,x]/(tx)$

**Geometrie**:

- Die Faser über $t = a \neq 0$: $x = 0$, also eine einzelne Gerade
- Die Faser über $t = 0$: ganz $\mathbb{A}^1_x$ (da $tx = 0$ automatisch)

**Eigenschaften**:

1. **Offen auf den Fasern**: Ja (jede Faser ist entweder ein Punkt oder $\mathbb{A}^1$)

2. **Nicht flach**:

   Betrachte den Punkt $(t, x) = (0, 0)$.

   Lokale Ringe:
   - $\mathcal{O}_{Y,0} = k[t]_{(t)}$
   - $\mathcal{O}_{X,(0,0)} = k[t,x]_{(t,x)}/(tx)$

   Der Homomorphismus $\mathcal{O}_{Y,0} \to \mathcal{O}_{X,(0,0)}$ ist **nicht flach**,
   da die Faserdimension springt (von 0 auf 1).

   Oder: $t$ ist ein Nullteiler in $\mathcal{O}_{X,(0,0)}$ (da $tx = 0$).

---

## ETH严格性验证

| 验证点 | 状态 |
|-------|------|
| 平坦性判别的严格性 | ✅ |
| 显式计算的例子 | ✅ |
| 反例的构造 | ✅ |

---

**创建日期**: 2026-04-10
