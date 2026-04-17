---
习题编号: AG-ETH-015
标题: 现代前沿问题探索
type: Forschungsorientiert (研究探索型)
difficulty: ⭐⭐⭐⭐⭐
章节: ETH 401-3532 Ergänzung E.2
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 120-180分钟
msc: 14-02, 14J33
eth_style: Forschungsfragen
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

# AG-ETH-015: 现代前沿问题探索 (*Moderne Forschungsfragen*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Ergänzung E.2: Aktuelle Forschungsthemen |
| **类型** | Forschungsorientiert (研究探索型) |
| **ETH风格** | Forschungsfragen (研究问题) |
| **难度** | ⭐⭐⭐⭐⭐ |
| **预计用时** | 120-180分钟 |

---

## 问题陈述

> **Aufgabe** (Forschungsorientiert):
> Diese Aufgabe führt in aktuelle Forschungsthemen der algebraischen Geometrie ein.
> 
> (a) **Mirror Symmetry**: Erklären Sie die grundlegende Aussage der Spiegelsymmetrie
>     für Calabi-Yau-Varietäten. Was bedeutet es, dass "Hodge-Zahlen gespiegelt werden"?
> 
> (b) **Derived Categories**: Formulieren Sie die äquivalente Aussage der
>     Spiegelsymmetrie in der Sprache der derivierten Kategorien (Kontsevich).
> 
> (c) **Offene Probleme**: Diskutieren Sie eines der folgenden offenen Probleme:
>     - Die Hodge-Vermutung
>     - Das Standard-Modell der konformen Feldtheorie
>     - Die Existenz von rationalen Punkten auf Varietäten

### 中文翻译

> **习题** (研究导向)：
> 本题介绍代数几何的当前研究主题。
> 
> (a) **镜像对称**：解释Calabi-Yau簇的镜像对称基本陈述。
>     "Hodge数镜像"是什么意思？
> 
> (b) **导出范畴**：用导出范畴的语言（Kontsevich）表述镜像对称的等价陈述。
> 
> (c) **开放问题**：讨论以下开放问题之一：
>     - Hodge猜想
>     - 共形场论的标准模型
>     - 簇上有理点的存在性

---

## 详细解答

### Teil (a): 镜像对称基础

**Mirror Symmetry** (Spiegelsymmetrie):

Für eine Calabi-Yau-Varietät $X$ der Dimension $n$ existiert eine "Spiegel-Varietät" $X^\vee$
mit der Eigenschaft:

$$H^{p,q}(X) \cong H^{n-p,q}(X^\vee)$$

**Hodge-Spiegelung**:

Die Hodge-Zahlen werden gespiegelt an der Mittellinie:

```
X:              X^∨:
h^{0,0}         h^{0,0}
h^{1,0} h^{0,1}    h^{n-1,0} h^{n,1}
...             ...
h^{n,0}         h^{0,0}
```

**Beispiel** (Quintic 3-fold):

Die Quintik in $\mathbb{P}^4$ hat Hodge-Zahlen:
- $h^{1,1} = 1$
- $h^{2,1} = 101$

Ihr Spiegel hat:
- $h^{1,1} = 101$
- $h^{2,1} = 1$

---

### Teil (b): 导出范畴的表述

**Kontsevich's Homological Mirror Symmetry**:

Die Spiegelsymmetrie ist äquivalent zu einer Äquivalenz von Kategorien:

$$D^b(\operatorname{Coh}(X)) \cong D^b(\operatorname{Fuk}(X^\vee))$$

wobei:
- $D^b(\operatorname{Coh}(X))$: Derivierte Kategorie der kohärenten Garben
- $D^b(\operatorname{Fuk}(X^\vee))$: Derivierte Fukaya-Kategorie

**Bedeutung**:
- **Algebraische Seite** ($D^b\operatorname{Coh}$): Garben, Kohomologie
- **Symplektische Seite** ($D^b\operatorname{Fuk}$): Lagrange-Untermannigfaltigkeiten

---

### Teil (c): 开放问题讨论

#### Die Hodge-Vermutung

**Aussage**: Auf einer glatten projektiven Varietät sind die rationalen
Hodge-Klassen ($H^{2k}(X, \mathbb{Q}) \cap H^{k,k}(X)$) Linearkombinationen
von algebraischen Zyklen.

**Status**: Eines der Millenium-Probleme. Nur für besondere Fälle bewiesen
(Hilbert-Schemata von Flächen, etc.).

#### Existenz rationaler Punkte

**Problem**: Gegeben eine Varietät $X$ über $\mathbb{Q}$, hat $X$ rationale Punkte?

**Methoden**:
- Lokal-globales Prinzip (Hasse)
- Descent-Theorie
- Brauer-Manin-Obstruktion

**ETH Tradition**: Die Züricher Schule (besonders durch Manin und spätere Forscher)
hat wesentliche Beiträge zur arithmetischen Geometrie geleistet.

---

## ETH研究前沿

ETH Zurich在代数几何研究中的 aktuelle Themen:

1. **Arithmetische Geometrie** (Gerd Faltings' Tradition)
2. **Algebraische Zyklen und Motive**
3. **Modulräume und ihre Kompaktifizierungen**
4. **Anwendungen der algebraischen Geometrie in der theoretischen Physik**

---

**创建日期**: 2026-04-10
