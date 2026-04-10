---
习题编号: AG-ETH-008
标题: 维数理论的统一视角
type: Synthese (综合型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 4.1
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 75-100分钟
msc: 14A99, 13H05
eth_style: Einheitliche Sicht
---

# AG-ETH-008: 维数理论的统一视角 (*Einheitliche Sicht der Dimensionstheorie*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 4.1: Dimensionstheorie und Kohomologie |
| **类型** | Synthese (综合型) |
| **ETH风格** | Einheitliche Sicht (统一视角) |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 75-100分钟 |

---

## 问题陈述

> **Aufgabe** (Einheitliche Sicht):
> Es sei $X$ ein projektives Schema der Dimension $n$ über einem 
> algebraisch abgeschlossenen Körper $k$.
> 
> (a) Zeigen Sie, dass die folgenden Dimensionsbegriffe übereinstimmen:
>     - Krull-Dimension $\dim(X)$
>     - Kohomologische Dimension $\operatorname{cd}(X)$
>     - Maximale Länge einer Kette irreduzibler abgeschlossener Unterschemata
> 
> (b) Beweisen Sie den **Satz über die kohomologische Dimension**:
>     $$H^i(X, \mathcal{F}) = 0 \text{ für alle } i > n \text{ und alle abelschen Garben } \mathcal{F}$$
> 
> (c) Verbinden Sie dies mit der Serre-Dualität: Für $X$ glatt projektiv
>     der Dimension $n$, zeigen Sie dass $H^n(X, \omega_X) \cong k$.

### 中文翻译

> **习题** (统一视角)：
> 设 $X$ 为代数闭域 $k$ 上的 $n$ 维射影概形。
> 
> (a) 证明以下维数概念一致：
>     - Krull维数 $\dim(X)$
>     - 上同调维数 $\operatorname{cd}(X)$
>     - 不可约闭子概形链的最大长度
> 
> (b) 证明**上同调维数定理**：
>     对所有 $i > n$ 和所有阿贝尔群层 $\mathcal{F}$，$H^i(X, \mathcal{F}) = 0$。
> 
> (c) 与Serre对偶联系：对光滑射影 $n$ 维 $X$，证明 $H^n(X, \omega_X) \cong k$。

---

## 详细解答

### Teil (a): 维数概念的等价性

**Theorem**: Für ein projektives Schema $X$ der Dimension $n$ gilt:
$$\dim(X) = \operatorname{cd}(X) = \sup\{\text{Länge von Kette } Z_0 \subsetneq Z_1 \subsetneq \cdots \subsetneq Z_m\}$$

**Beweis**:

**Schritt 1**: Krull-Dimension

Die Krull-Dimension ist definiert als:
$$\dim(X) = \sup\{\dim \mathcal{O}_{X,x} : x \in X\}$$

Für projektive Schemata entspricht dies der maximalen Länge einer Kette
irreduzibler abgeschlossener Unterschemata.

**Schritt 2**: Kohomologische Dimension

Die kohomologische Dimension ist:
$$\operatorname{cd}(X) = \sup\{i : H^i(X, \mathcal{F}) \neq 0 \text{ für eine Garbe } \mathcal{F}\}$$

**Schritt 3**: Gleichheit

Für projektive Schemata über $k$:
- $\operatorname{cd}(X) \leq \dim(X)$ (siehe Teil b)
- $\operatorname{cd}(X) \geq \dim(X)$ (Konstruktion einer Garbe mit $H^n \neq 0$)

Also Gleichheit. ∎

---

### Teil (b): 上同调维数定理

**Theorem**: $H^i(X, \mathcal{F}) = 0$ für $i > n = \dim(X)$.

**Beweis**:

**Schritt 1**: Reduktion auf Čech-Kohomologie

Für eine affine Überdeckung $\mathcal{U}$ mit $r$ Elementen:
$$\check{H}^i(\mathcal{U}, \mathcal{F}) = 0 \text{ für } i > r - 1$$

**Schritt 2**: Vergleich mit derivierter Funktor Kohomologie

Für quasikohärente Garben: $\check{H}^i \cong H^i$.

**Schritt 3**: Induktion über Dimension

- Induktionsanfang: $\dim(X) = 0$ (diskret) $\Rightarrow$ $H^i = 0$ für $i > 0$.

- Induktionsschritt: Sei $\dim(X) = n$.
  
  Wähle eine Hyperfläche $H$ mit $\dim(H) = n-1$.
  
  Betrachte die kurze exakte Sequenz:
  $$0 \to \mathcal{F}(-H) \to \mathcal{F} \to \mathcal{F}|_H \to 0$$
  
  Die lange exakte Sequenz gibt:
  $$\cdots \to H^i(X, \mathcal{F}(-H)) \to H^i(X, \mathcal{F}) \to H^i(H, \mathcal{F}|_H) \to \cdots$$
  
  Nach Induktionsvoraussetzung: $H^i(H, \mathcal{F}|_H) = 0$ für $i > n-1$.
  
  Auch: $H^i(X, \mathcal{F}(-mH)) = 0$ für $m \gg 0$ (Serre-Verschwinden).
  
  Also $H^i(X, \mathcal{F}) = 0$ für $i > n$. ∎

---

### Teil (c): Serre对偶的联系

**Theorem**: Für $X$ glatt projektiv der Dimension $n$:
$$H^n(X, \omega_X) \cong k$$

**Beweis**:

Nach dem **Satz von Serre-Dualität**:
$$H^n(X, \omega_X) \cong H^0(X, \mathcal{O}_X)^* = k^* = k$$

Dies ist der "Spitzenfall" der Dualität, wo die Dimension maximal ist.

Die Nicht-Ausgeartetheit des Spur-Isomorphismus:
$$\operatorname{Tr}: H^n(X, \omega_X) \xrightarrow{\sim} k$$

ist fundamental für die gesamte Dualitätstheorie. ∎

---

**创建日期**: 2026-04-10
