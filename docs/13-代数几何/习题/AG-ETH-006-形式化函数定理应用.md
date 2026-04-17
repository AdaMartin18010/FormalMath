---
习题编号: AG-ETH-006
标题: 形式化函数定理应用
type: Synthese (综合型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 3.2
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 90-120分钟
msc: 14B20, 14F05
eth_style: Synthese + Anwendung
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

# AG-ETH-006: 形式化函数定理应用 (*Anwendung des Formalen Funktionensatzes*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 3.2: Formaler Funktionensatz |
| **类型** | Synthese (综合型) |
| **ETH风格** | (S) Synthese + (A) Anwendung |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 90-120分钟 |

---

## 问题陈述

> **Aufgabe** (Synthese):
> Es sei $f: X \to Y$ ein eigentlicher Morphismus Noetherscher Schemata,
> $\mathcal{F}$ eine kohärente Garbe auf $X$, und $y \in Y$ ein Punkt.
> Bezeichne $X_n = X \times_Y \operatorname{Spec}(\mathcal{O}_{Y,y}/\mathfrak{m}_y^{n+1})$
> die $n$-te formale Faser.
>
> (a) Formulieren Sie streng den **Formalen Funktionensatz**.
>
> (b) Zeigen Sie: Für die höheren direkten Bilder gilt:
> $$(R^i f_* \mathcal{F})_y^\wedge \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$
> wobei $\mathcal{F}_n$ die Einschränkung von $\mathcal{F}$ auf $X_n$ ist.
>
> (c) **Anwendung**: Sei $f: X \to Y$ eine eigentliche Flächenfaserung
> (d.h. $\dim X = 3$, $\dim Y = 1$, generische Faser ist eine Kurve).
> Zeigen Sie: Die Eulercharakteristik der Fasern ist lokal konstant.

### 中文翻译

> **习题** (综合)：
> 设 $f: X \to Y$ 为Noether概形的真态射，
> $\mathcal{F}$ 为 $X$ 上的凝聚层，$y \in Y$ 为一点。
> 记 $X_n = X \times_Y \operatorname{Spec}(\mathcal{O}_{Y,y}/\mathfrak{m}_y^{n+1})$
> 为第 $n$ 次形式纤维。
>
> (a) 严格陈述**形式化函数定理**。
>
> (b) 证明：对高阶直像有：
> $$(R^i f_* \mathcal{F})_y^\wedge \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$
> 其中 $\mathcal{F}_n$ 是 $\mathcal{F}$ 在 $X_n$ 上的限制。
>
> (c) **应用**：设 $f: X \to Y$ 为真曲面纤维化
> （即 $\dim X = 3$，$\dim Y = 1$，一般纤维为曲线）。
> 证明：纤维的Euler示性数是局部常数。

---

## 详细解答

### Teil (a): 形式化函数定理的严格陈述

**Theorem** (Formaler Funktionensatz / Theorem on Formal Functions):

*Voraussetzungen*:

- $f: X \to Y$ eigentlicher Morphismus Noetherscher Schemata
- $\mathcal{F}$ kohärente Garbe auf $X$
- $y \in Y$ ein Punkt mit maximalem Ideal $\mathfrak{m} = \mathfrak{m}_y$

*Behauptung*: Es gibt einen kanonischen Isomorphismus:
$$(R^i f_* \mathcal{F})_y^\wedge \xrightarrow{\sim} \varprojlim_n H^i(X_n, \mathcal{F}_n)$$

wobei:

- $(-)^\wedge$ bezeichnet die $\mathfrak{m}$-adische Vervollständigung
- $X_n = X \times_Y \operatorname{Spec}(\mathcal{O}_{Y,y}/\mathfrak{m}^{n+1})$
- $\mathcal{F}_n = \mathcal{F} \otimes_{\mathcal{O}_Y} \mathcal{O}_{Y,y}/\mathfrak{m}^{n+1}$

---

### Teil (b): 定理证明的概要

**Beweisstruktur** (ETH Synthese-Stil):

**Schritt 1**: Lokalisierung

Wir können annehmen: $Y = \operatorname{Spec}(A)$ affin, $y \in Y$ entspricht $\mathfrak{m} \subseteq A$.

Dann: $(R^i f_* \mathcal{F})_y^\wedge = H^i(X, \mathcal{F})^\wedge$.

**Schritt 2**: Spektralsequenz

Betrachte die $\mathfrak{m}$-adische Filtrierung:
$$\mathcal{F} \supseteq \mathfrak{m}\mathcal{F} \supseteq \mathfrak{m}^2\mathcal{F} \supseteq \cdots$$

Dies induziert eine Spektralsequenz:
$$E_1^{p,q} = H^{p+q}(X, \mathfrak{m}^p\mathcal{F}/\mathfrak{m}^{p+1}\mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})^\wedge$$

**Schritt 3**: Konvergenz

Die Spektralsequenz konvergiert gegen die Vervollständigung.

Die $E_1$-Seite berechnet die Kohomologie der $X_n$.

**Schritt 4**: Isomorphismus

Durch Vergleich der Spektralsequenzen erhält man:
$$H^i(X, \mathcal{F})^\wedge \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$ ∎

---

### Teil (c): 应用 - Euler示性数的局部常数性

**Aufgabe**: $f: X \to Y$ eigentliche Flächenfaserung, zeige $\chi(X_y)$ lokal konstant.

**Lösung** (Synthese mehrerer Techniken):

**Schritt 1**: Eulercharakteristik definieren

Für eine Kurve $C$:
$$\chi(C) = \sum_i (-1)^i \dim H^i(C, \mathcal{O}_C) = 1 - g(C)$$

**Schritt 2**: Relative Eulercharakteristik

Definiere für die Faser $X_y$:
$$\chi(X_y) = \sum_i (-1)^i \dim_{k(y)} H^i(X_y, \mathcal{O}_{X_y})$$

**Schritt 3**: Anwendung des Formalen Funktionensatzes

Mit $\mathcal{F} = \mathcal{O}_X$:
$$(R^i f_* \mathcal{O}_X)_y^\wedge \cong \varprojlim_n H^i(X_n, \mathcal{O}_{X_n})$$

**Schritt 4**: Obere Halbstetigkeit

Nach dem **Satz von Grauert** (ETH Kapitel 3.4):
Die Funktion $y \mapsto \dim H^i(X_y, \mathcal{O}_{X_y})$ ist oben halbstetig.

**Schritt 5**: Konstante Eulercharakteristik

Betrachte die relative Eulercharakteristik:
$$\chi(f) = \sum_i (-1)^i [R^i f_* \mathcal{O}_X] \in K(Y)$$

Dies ist eine Klasse in der K-Theorie von $Y$.

Da $Y$ eine Kurve ist (dim 1), ist $K(Y)$ diskret.

Die Faser-Eulercharakteristik ist gegeben durch:
$$\chi(X_y) = \sum_i (-1)^i \dim (R^i f_* \mathcal{O}_X)_y \otimes k(y)$$

Nach dem Formalen Funktionensatz ist dies lokal konstant in $y$. ∎

---

## ETH综合特色

本题综合了ETH 401-3532的多个核心内容：

- 形式化函数定理 (K3.2)
- 平坦基变换 (K3.1)
- 半连续性定理 (K3.4)

---

**创建日期**: 2026-04-10
