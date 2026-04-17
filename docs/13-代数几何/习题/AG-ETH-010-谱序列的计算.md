---
习题编号: AG-ETH-010
标题: 谱序列的计算
type: Technische Meisterung (技术掌握型)
difficulty: ⭐⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 5.1
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 120-150分钟
msc: 18G40, 55T05
eth_style: Explizit + Vollständig
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

# AG-ETH-010: 谱序列的计算 (*Berechnung mit Spektralsequenzen*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 5.1: Spektralsequenzen in der Algebraischen Geometrie |
| **类型** | Technische Meisterung (技术掌握型) |
| **ETH风格** | (E) Explizit + (V) Vollständig |
| **难度** | ⭐⭐⭐⭐⭐ |
| **预计用时** | 120-150分钟 |

---

## 问题陈述

> **Aufgabe** (Explizit und Vollständig):
> Es sei $X$ ein topologischer Raum, $\mathcal{U} = \{U_i\}_{i=0}^2$ eine offene
> Überdeckung mit drei Elementen, und $\mathcal{F}$ eine abelsche Garbe auf $X$.
> 
> (a) Konstruieren Sie vollständig die **Čech-derivierte Funktor**
>     Spektralsequenz:
>     $$E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$
> 
> (b) Berechnen Sie explizit die $E_2$-Seite für $X = \mathbb{P}^2_k$,
>     $\mathcal{F} = \mathcal{O}_X$, und die Standardüberdeckung $\mathcal{U} = \{U_0, U_1, U_2\}$.
> 
> (c) Zeigen Sie, dass diese Spektralsequenz bei $E_3$ degeneriert
>     und berechnen Sie $H^*(\mathbb{P}^2, \mathcal{O}_X)$.

### 中文翻译

> **习题** (显式且完整)：
> 设 $X$ 为拓扑空间，$\mathcal{U} = \{U_i\}_{i=0}^2$ 为三元开覆盖，
> $\mathcal{F}$ 为 $X$ 上的阿贝尔群层。
> 
> (a) 完整构造**Čech-导出函子**谱序列：
>     $$E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$
> 
> (b) 对 $X = \mathbb{P}^2_k$，$\mathcal{F} = \mathcal{O}_X$，
>     标准覆盖 $\mathcal{U} = \{U_0, U_1, U_2\}$，显式计算 $E_2$ 页。
> 
> (c) 证明该谱序列在 $E_3$ 退化，并计算 $H^*(\mathbb{P}^2, \mathcal{O}_X)$。

---

## 详细解答

### Teil (a): 谱序列的构造

**Konstruktion** (Vollständig):

**Schritt 1**: Doppelkomplex

Betrachte den Doppelkomplex:
$$K^{p,q} = \check{C}^p(\mathcal{U}, \mathcal{I}^q)$$

wobei $\mathcal{I}^\bullet$ eine injektive Auflösung von $\mathcal{F}$ ist.

**Schritt 2**: Differentiale

- Horizontal: $\delta: K^{p,q} \to K^{p+1,q}$ (Čech-Differential)
- Vertikal: $d: K^{p,q} \to K^{p,q+1}$ (von der injektiven Auflösung)

**Schritt 3**: Spektralsequenz

Filtration nach dem Čech-Grad:
$$F^p K^{*,*} = \bigoplus_{p' \geq p} K^{p',*}$$

Dies induziert eine Spektralsequenz mit:
- $E_0^{p,q} = K^{p,q}$
- $E_1^{p,q} = H^q(K^{p,*}) = \check{C}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F}))$
- $E_2^{p,q} = H^p(E_1^{*,q}) = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F}))$

**Konvergenz**: Gegen $H^{p+q}(X, \mathcal{F})$. ∎

---

### Teil (b): $E_2$-Seite的计算

**Setup**: $X = \mathbb{P}^2_k$, $\mathcal{F} = \mathcal{O}_X$, $\mathcal{U} = \{U_0, U_1, U_2\}$.

**Berechnung von $E_2^{p,q}$**:

**Fall $q = 0$**:
$$E_2^{p,0} = \check{H}^p(\mathcal{U}, \mathcal{H}^0(\mathcal{O}_X)) = \check{H}^p(\mathcal{U}, \mathcal{O}_X)$$

Da $\mathcal{U}$ eine affine Überdeckung ist:
- $E_2^{0,0} = H^0(X, \mathcal{O}_X) = k$
- $E_2^{1,0} = 0$
- $E_2^{2,0} = 0$

**Fall $q > 0$**:

Für affine $U_i$: $H^q(U_i, \mathcal{O}_X) = 0$ für $q > 0$.

Also:
$$\mathcal{H}^q(\mathcal{O}_X)|_{U_i} = 0 \text{ für } q > 0$$

Daraus folgt:
$$E_2^{p,q} = 0 \text{ für } q > 0$$

**$E_2$-Tabelle**:

| $q$ \\ $p$ | 0 | 1 | 2 |
|-----------|---|---|---|
| **0** | $k$ | 0 | 0 |
| **1** | 0 | 0 | 0 |
| **2** | 0 | 0 | 0 |

---

### Teil (c): 退化与上同调

**Degeneration**:

Da $E_2^{p,q} = 0$ für alle $(p,q) \neq (0,0)$, degeneriert die Spektralsequenz
sofort bei $E_2$ (also auch bei $E_3$).

**Kohomologie**:

$$H^i(X, \mathcal{O}_X) = \begin{cases} k & i = 0 \\ 0 & i > 0 \end{cases}$$

Dies ist konsistent mit dem allgemeinen Resultat für projektive Räume. ∎

---

**创建日期**: 2026-04-10
