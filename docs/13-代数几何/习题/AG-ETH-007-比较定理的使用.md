---
习题编号: AG-ETH-007
标题: 比较定理的使用
type: Theoretische Verifikation (理论型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 2.2
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 60-90分钟
msc: 14F05, 18F20
eth_style: Streng + Natürlich
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

# AG-ETH-007: 比较定理的使用 (*Vergleichssätze*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 2.2: Čech-Kohomologie und derivierte Funktoren |
| **类型** | Theoretische Verifikation (理论型) |
| **ETH风格** | (S) Streng + (N) Natürlich |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 60-90分钟 |

---

## 问题陈述

> **Aufgabe** (Streng und Natürlich):
> Es sei $X$ ein topologischer Raum, $\mathcal{U} = \{U_i\}$ eine offene Überdeckung,
> und $\mathcal{F}$ eine abelsche Garbe auf $X$.
>
> (a) Konstruieren Sie streng den kanonischen Homomorphismus:
> $$\check{H}^i(\mathcal{U}, \mathcal{F}) \longrightarrow H^i(X, \mathcal{F})$$
>
> (b) Beweisen Sie: Ist $\mathcal{U}$ eine **Leray-Überdeckung** für $\mathcal{F}$
> (d.h. $H^j(U_{i_0} \cap \cdots \cap U_{i_p}, \mathcal{F}) = 0$ für alle $j > 0$ und alle $p$),
> so ist der Vergleichshomomorphismus ein Isomorphismus.
>
> (c) Zeigen Sie die Natürlichkeit: Für einen Morphismus $f: \mathcal{F} \to \mathcal{G}$
> kommutiert das Diagramm:
> ```
> Ĥ^i(U,F) → H^i(X,F)
>         ↓           ↓
>     Ĥ^i(U,G) → H^i(X,G)
>     ```

### 中文翻译

> **习题** (严格且自然)：
> 设 $X$ 为拓扑空间，$\mathcal{U} = \{U_i\}$ 为开覆盖，
> $\mathcal{F}$ 为 $X$ 上的阿贝尔群层。
>
> (a) 严格构造典范同态：
> $$\check{H}^i(\mathcal{U}, \mathcal{F}) \longrightarrow H^i(X, \mathcal{F})$$
>
> (b) 证明：若 $\mathcal{U}$ 是 $\mathcal{F}$ 的**Leray覆盖**
> （即对所有 $j > 0$ 和所有 $p$，$H^j(U_{i_0} \cap \cdots \cap U_{i_p}, \mathcal{F}) = 0$），
> 则比较同态是同构。
>
> (c) 证明自然性：对态射 $f: \mathcal{F} \to \mathcal{G}$，下图交换：
> ```
> Čech^i(U,F) → H^i(X,F)
>          ↓            ↓
>     Čech^i(U,G) → H^i(X,G)
>     ```

---

## 详细解答

### Teil (a): 比较同态的构造

**Konstruktion** (Streng):

**Schritt 1**: Čech-Auflösung

Für die Überdeckung $\mathcal{U}$ definieren wir die **Čech-Auflösung**:
$$0 \to \mathcal{F} \to \check{C}^0(\mathcal{U}, \mathcal{F}) \to \check{C}^1(\mathcal{U}, \mathcal{F}) \to \cdots$$

wobei:
$$\check{C}^p(\mathcal{U}, \mathcal{F}) = \prod_{i_0 < \cdots < i_p} (\iota_{i_0\cdots i_p})_* (\mathcal{F}|_{U_{i_0\cdots i_p}})$$

Dies ist eine Auflösung von $\mathcal{F}$ durch **azyklische** Garben.

**Schritt 2**: Auflösung injektiv?

Die Čech-Auflösung ist i.A. **nicht** injektiv (im Sinne von injektiven Objekten).

Aber: Sie ist eine Auflösung durch **flasque** Garben, wenn $\mathcal{F}$ flasque ist.

**Schritt 3**: Kanonischer Morphismus

Betrachte die Identität $\mathcal{F} \to \mathcal{F}$.

Diese induziert einen Morphismus der Auflösungen:

- Von der Čech-Auflösung zur injektiven Auflösung

Dies gibt einen Morphismus auf der Kohomologie:
$$\check{H}^i(\mathcal{U}, \mathcal{F}) = H^i(\Gamma(X, \check{C}^\bullet)) \to H^i(X, \mathcal{F})$$

---

### Teil (b): Leray覆盖定理

**Theorem** (Leray):

Ist $\mathcal{U}$ eine Leray-Überdeckung für $\mathcal{F}$, dann ist:
$$\check{H}^i(\mathcal{U}, \mathcal{F}) \xrightarrow{\sim} H^i(X, \mathcal{F})$$

**Beweis**:

**Schritt 1**: Spektralsequenz

Die Čech-Auflösung induziert eine Spektralsequenz:
$$E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$

wobei $\mathcal{H}^q(\mathcal{F})$ die Garbe assoziiert zu $U \mapsto H^q(U, \mathcal{F})$ ist.

**Schritt 2**: Leray-Bedingung

Die Leray-Bedingung besagt genau:
$$\mathcal{H}^q(\mathcal{F})|_{U_{i_0\cdots i_p}} = 0 \text{ für } q > 0$$

Also: $\mathcal{H}^q(\mathcal{F}) = 0$ für $q > 0$.

**Schritt 3**: Degeneration

Die Spektralsequenz degeneriert:
$$E_2^{p,q} = 0 \text{ für } q > 0$$

Also:
$$E_2^{p,0} = \check{H}^p(\mathcal{U}, \mathcal{F}) \cong H^p(X, \mathcal{F})$$ ∎

---

### Teil (c): 自然性

**Behauptung**: Für $f: \mathcal{F} \to \mathcal{G}$ kommutiert:

```
Ĥ^i(U,F) → H^i(X,F)
    ↓f*        ↓f*
Ĥ^i(U,G) → H^i(X,G)
```

**Beweis**:

Der Morphismus $f$ induziert:

1. Einen Morphismus der Čech-Komplexe: $\check{C}^\bullet(\mathcal{U}, \mathcal{F}) \to \check{C}^\bullet(\mathcal{U}, \mathcal{G})$
2. Einen Morphismus der injektiven Auflösungen (bis auf Homotopie eindeutig)

Diese sind verträglich mit den Vergleichsmorphismen.

Also kommutiert das Diagramm auf Kohomologie. ∎

---

**创建日期**: 2026-04-10
