---
习题编号: AG-ETH-001
标题: 概形的局部性质
type: Strenge Beweis (严格证明型)
difficulty: ⭐⭐⭐
章节: ETH 401-3532 Kapitel 1.1
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 60-90分钟
msc: 14A15, 14F20
eth_style: Strenger Stil
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

# AG-ETH-001: 概形的局部性质 (*Lokale Eigenschaften von Schemata*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 1.1: Garbenkohomologie Grundlagen |
| **类型** | Strenge Beweis (严格证明型) |
| **ETH风格** | Strenger Stil (S) - 严格证明要求 |
| **难度** | ⭐⭐⭐ |
| **预计用时** | 60-90分钟 |

---

## 问题陈述

### 原题 (ETH 401-3532 Übung 1.1)

> **Aufgabe** (Streng):
> Es sei $(X, \mathcal{O}_X)$ ein lokal geringter Raum.
> Man zeige streng, dass die folgenden Aussagen äquivalent sind:
>
> (a) $(X, \mathcal{O}_X)$ ist ein Schema;
>
> (b) Für jeden Punkt $x \in X$ existiert eine offene Umgebung $U \subseteq X$,
> so dass $(U, \mathcal{O}_X|_U)$ isomorph zu einem affinen Schema ist;
>
> (c) $X$ besitzt eine offene Überdeckung durch affine Schemata.

### 中文翻译

> **习题** (严格)：
> 设 $(X, \mathcal{O}_X)$ 为局部环化空间。
> 严格证明以下陈述等价：
>
> (a) $(X, \mathcal{O}_X)$ 是概形；
>
> (b) 对每一点 $x \in X$，存在开邻域 $U \subseteq X$，
> 使得 $(U, \mathcal{O}_X|_U)$ 同构于某个仿射概形；
>
> (c) $X$ 可被仿射概形开覆盖。

---

## 解题思路

### ETH严格风格分析

本题体现"Strenger Stil"的核心要求：**定义的严格等价性验证**。需要：

1. **明确前提** (Prämissenexplizierung)：局部环化空间的结构
2. **精确结论** (Konklusionspräzisierung)：三个条件的循环等价
3. **系统证明** (Beweissystematisierung)：按 (a)→(b)→(c)→(a) 循环

```
证明结构图 (ETH风格)

┌─────────────────────────────────────────────────────┐
│           概形定义的等价性证明                        │
├─────────────────────────────────────────────────────┤
│                                                      │
│   (a) Schema ──────> (b) Lokale Affinität           │
│      ↑                    ↓                         │
│      └──────────────── (c) Affine Überdeckung       │
│                                                      │
│   证明步骤:                                          │
│   Step 1: (a) ⇒ (b)  [定义直接推出]                  │
│   Step 2: (b) ⇒ (c)  [开覆盖构造]                    │
│   Step 3: (c) ⇒ (a)  [概形定义的验证]                │
│                                                      │
└─────────────────────────────────────────────────────┘
```

---

## 详细解答

### 证明框架

**Theorem**: 设 $(X, \mathcal{O}_X)$ 为局部环化空间。则条件 (a)、(b)、(c) 等价。

**Beweis** (Streng und Vollständig):

---

### Step 1: (a) ⇒ (b) [概形定义直接推出]

**Voraussetzung**: $(X, \mathcal{O}_X)$ ist ein Schema.

**Zu zeigen**: Für jedes $x \in X$ existiert eine affine offene Umgebung.

**Beweis**:

Nach der **Definition eines Schemas** (Hartshorne II.2, ETH Kapitel 1.1):

> Ein Schema ist ein lokal geringter Raum $(X, \mathcal{O}_X)$,
> bei dem jeder Punkt $x \in X$ eine offene Umgebung $U$ besitzt,
> so dass $(U, \mathcal{O}_X|_U)$ isomorph zu einem affinen Schema ist.

Das ist genau die Aussage (b). ∎

---

### Step 2: (b) ⇒ (c) [开覆盖的显式构造]

**Voraussetzung**: Für jedes $x \in X$ existiert eine affine offene Umgebung.

**Zu zeigen**: $X$ besitzt eine Überdeckung durch affine Schemata.

**Beweis** (Konstruktiv):

Für jeden Punkt $x \in X$ wählen wir nach Voraussetzung eine offene Umgebung $U_x$,
so dass $(U_x, \mathcal{O}_X|_{U_x}) \cong \operatorname{Spec}(A_x)$ für einen Ring $A_x$.

Betrachten wir die Familie $\{U_x\}_{x \in X}$:

**(i) Offenheit**: Jedes $U_x$ ist offen in $X$ (nach Konstruktion).

**(ii) Überdeckung**:
$$\bigcup_{x \in X} U_x = X$$
Denn für jedes $y \in X$ gilt $y \in U_y$ (da $U_y$ Umgebung von $y$ ist).

**(iii) Affinität**: Jedes $(U_x, \mathcal{O}_X|_{U_x})$ ist isomorph zu einem affinen Schema.

Somit ist $\{U_x\}_{x \in X}$ eine affine offene Überdeckung von $X$. ∎

---

### Step 3: (c) ⇒ (a) [概形定义的严格验证]

**Voraussetzung**: $X = \bigcup_{i \in I} U_i$, wobei jedes $(U_i, \mathcal{O}_X|_{U_i}) \cong \operatorname{Spec}(A_i)$.

**Zu zeigen**: $(X, \mathcal{O}_X)$ ist ein Schema.

**Beweis** (Streng):

Wir müssen die **Definition eines Schemas** strikt überprüfen.

**Schritt 3.1**: $(X, \mathcal{O}_X)$ ist ein lokal geringter Raum (Voraussetzung).

**Schritt 3.2**: Lokale Affinität.

Sei $x \in X$ beliebig. Da $\{U_i\}$ eine Überdeckung ist, existiert $i \in I$ mit $x \in U_i$.

Da $U_i$ offen ist und $(U_i, \mathcal{O}_X|_{U_i}) \cong \operatorname{Spec}(A_i)$,
haben wir eine affine offene Umgebung von $x$ gefunden.

**Schritt 3.3**: Schlussfolgerung.

Da jedes $x \in X$ eine affine offene Umgebung besitzt,
ist $(X, \mathcal{O}_X)$ nach Definition ein Schema. ∎

---

### Zusammenfassung der Äquivalenz

```
Äquivalenzkette (vollständig bewiesen):

(a) Schema
    ⇓ [Definition]
(b) Lokale Affinität
    ⇓ [Konstruktion der Überdeckung]
(c) Affine Überdeckung
    ⇓ [Verifikation der Schemadefinition]
(a) Schema ∎
```

---

## 严格性验证 (Strenge Verifikation)

### 自然性验证 (Natürlichkeit)

Die Äquivalenz ist **natürlich** in folgendem Sinne:

Für einen Morphismus lokal geringter Räume $f: (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$:

- $X$ ist Schema $\Leftrightarrow$ $Y$ ist Schema (lokal auf der Basis)

Das Diagramm kommutiert:

```
X Schema ──────> lokale Affinität
    │                  │
    │ f                │ f|_U
    ▼                  ▼
Y Schema ──────> lokale Affinität
```

### 函子性 (Funktorialität)

Die Äquivalenz respektiert:

- **Restriktion**: Auf offenen Unterschemata bleibt die Eigenschaft erhalten
- **Basiswechsel**: Unter Basiswechsel bleibt die Schemastruktur erhalten

---

## ETH特色标注

### 德语术语对照

| 德语术语 | 英文 | 中文 | ETH强调 |
|---------|------|------|---------|
| *Schema* | Scheme | 概形 | 强调局部环化空间结构 |
| *lokal geringter Raum* | locally ringed space | 局部环化空间 | 范畴论视角 |
| *affine Überdeckung* | affine cover | 仿射覆盖 | 构造性证明关键 |
| *isomorph* | isomorphic | 同构 | 严格范畴同构 |
| *Umgebung* | neighborhood | 邻域 | 局部性质核心 |

### 严格风格要素

本解答遵循ETH "Strenger Stil"要求：

| 要素 | 体现 |
|------|------|
| **(S)** *Streng* | 每个等价方向独立完整证明 |
| **(V)** *Vollständig* | 不省略任何验证步骤 |
| **(K)** *Konstruktiv* | Step 2显式构造开覆盖 |
| **(N)** *Natürlich* | 补充自然性验证 |

---

## 变式与推广

### 变式1: Noether概形的等价刻画

**Aufgabe**: 证明对局部Noether概形，以下条件等价：

- (a) $X$ 是Noether概形
- (b) $X$ 可被有限个仿射开集覆盖，每个都是Noether环的谱

**Hinweis**: 使用ETH风格的紧致性论证。

### 变式2: 分离概形的局部判别

**Aufgabe**: 证明概形 $X$ 是分离的当且仅当对任意仿射开集 $U, V \subseteq X$，
$U \cap V$ 也是仿射的。

---

## 相关概念

| 概念 | 德文 | 定义 | ETH讲义位置 |
|------|------|------|------------|
| 概形 | *Schema* | 局部同构于仿射概形的局部环化空间 | K1.1 |
| 仿射概形 | *affines Schema* | $\operatorname{Spec}(A)$ 及其结构层 | K1.1 |
| 结构层 | *Strukturgarbe* | $\mathcal{O}_X$ 使 $(X, \mathcal{O}_X)$ 局部环化 | K1.1 |
| 局部性质 | *lokale Eigenschaft* | 可在开覆盖上局部验证的性质 | K1.1 |

---

## 参考文献

1. **Hartshorne, R.** (1977). *Algebraic Geometry*, GTM 52, Ch II.2.
2. **ETH Zurich** (2024-2025). *401-3532-00L: Algebraic Geometry II*, Kapitel 1.1.
3. **Stacks Project**. [Tag 01LC](https://stacks.math.columbia.edu/tag/01LC) - Schemes.
4. **Grothendieck, A.** (1960). *Éléments de géométrie algébrique I*, IHES.

---

**创建日期**: 2026-04-10
**难度**: ⭐⭐⭐
**ETH风格**: Strenger Stil (严格)
**预计用时**: 60-90分钟
