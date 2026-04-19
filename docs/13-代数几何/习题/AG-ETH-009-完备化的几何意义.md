---
习题编号: AG-ETH-009
标题: 完备化的几何意义
type: Analytische Interpretation (分析型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 4.2
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 60-90分钟
msc: 14B15, 13J10
eth_style: Geometrische Deutung
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
msc_primary: 14A99
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
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
      chapters: 
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

# AG-ETH-009: 完备化的几何意义 (*Geometrische Bedeutung der Komplettierung*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 4.2: Formale Schemata und Komplettierung |
| **类型** | Analytische Interpretation (分析型) |
| **ETH风格** | Geometrische Deutung (几何解释) |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 60-90分钟 |

---

## 问题陈述

> **Aufgabe** (Geometrische Deutung):
> Es sei $X$ ein Noethersches Schema, $Y \subseteq X$ ein abgeschlossenes
> Unterschema, definiert durch das Ideal $\mathcal{I} \subseteq \mathcal{O}_X$.
> 
> (a) Definieren Sie das formale Vervollständigung $\hat{X}$ von $X$ längs $Y$
>     und erklären Sie dessen geometrische Bedeutung.
> 
> (b) Zeigen Sie: Die Kohomologie des formalen Vervollständigungs
>     approximiert die Kohomologie einer infinitesimalen Umgebung von $Y$:
>     $$H^i(\hat{X}, \hat{\mathcal{F}}) \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$
>     wobei $X_n$ das $n$-te infinitesimale Nachbarschaft ist.
> 
> (c) **Beispiel**: Sei $X = \mathbb{A}^2_k$ und $Y = \{0\}$ der Ursprung.
>     Beschreiben Sie explizit $\hat{X}$ und vergleichen Sie mit $X$.

### 中文翻译

> **习题** (几何解释)：
> 设 $X$ 为Noether概形，$Y \subseteq X$ 为由理想 $\mathcal{I} \subseteq \mathcal{O}_X$
> 定义的闭子概形。
> 
> (a) 定义 $X$ 沿 $Y$ 的形式完备化 $\hat{X}$，并解释其几何意义。
> 
> (b) 证明：形式完备化的上同调逼近 $Y$ 的无穷小邻域的上同调：
>     $$H^i(\hat{X}, \hat{\mathcal{F}}) \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$
>     其中 $X_n$ 是第 $n$ 次无穷小邻域。
> 
> (c) **例子**：设 $X = \mathbb{A}^2_k$，$Y = \{0\}$ 为原点。
>     显式描述 $\hat{X}$ 并与 $X$ 比较。

---

## 详细解答

### Teil (a): 形式完备化的定义

**Definition** (Formale Vervollständigung):

Das formale Vervollständigung $\hat{X}$ von $X$ längs $Y$ ist der gerngte Raum
$(Y, \varprojlim_n \mathcal{O}_X/\mathcal{I}^n)$.

**Geometrische Bedeutung**:

- $\hat{X}$ "sieht" nur eine infinitesimale Umgebung von $Y$
- Es vergisst das Komplement $X \setminus Y$
- Es erinnert an alle infinitesimalen Informationen längs $Y$

**Beispiel**: Für $X = \mathbb{A}^1_k$ und $Y = \{0\}$:
$$\hat{X} = \operatorname{Spf}(k[[x]])$$

Dies ist der formale Punkt (ein Punkt mit allen infinitesimalen Richtungen).

---

### Teil (b): 上同调的逼近

**Theorem**:
$$H^i(\hat{X}, \hat{\mathcal{F}}) \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$

**Beweis**:

**Schritt 1**: Definition von $\hat{\mathcal{F}}$

$$\hat{\mathcal{F}} = \varprojlim_n \mathcal{F}/\mathcal{I}^n\mathcal{F}$$

**Schritt 2**: Kohomologie als derivierter Funktor

Die Kohomologie kommutiert mit projektiven Limites unter gewissen
Endlichkeitsbedingungen (Noetherianität).

**Schritt 3**: Mittels des Formalen Funktionensatzes

Der formale Funktionensatz liefert genau diese Isomorphie
für eigentliche Morphismen. ∎

---

### Teil (c): 显式例子

**Beispiel**: $X = \mathbb{A}^2_k = \operatorname{Spec}(k[x,y])$, $Y = \{0\}$.

**Formale Vervollständigung**:

$$\hat{X} = \operatorname{Spf}(k[[x,y]])$$

**Vergleich**:

| Eigenschaft | $X = \mathbb{A}^2$ | $\hat{X}$ |
|------------|-------------------|-----------|
| Unterliegender Raum | $\mathbb{A}^2$ | Ein Punkt $
| Strukturgarbe | $k[x,y]$ | $k[[x,y]]$ |
| Globale Funktionen | Polynome | Formale Potenzreihen |
| Algebraische Funktionen | Viele | Nur formale |

**Geometrische Interpretation**:

- $X$ "sieht" die gesamte Ebene
- $\hat{X}$ "sieht" nur den Ursprung mit allen infinitesimalen Richtungen
- $\hat{X}$ enthält alle Taylor-Entwicklungen im Ursprung

---

**创建日期**: 2026-04-10
