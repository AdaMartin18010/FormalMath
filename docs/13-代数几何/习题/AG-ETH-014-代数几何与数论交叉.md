---
习题编号: AG-ETH-014
标题: 代数几何与数论交叉
type: Interdisziplinär (跨学科型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Ergänzung E.1
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 90-120分钟
msc: 14G10, 11G30
eth_style: AG-Zahlentheorie Interface
---

# AG-ETH-014: 代数几何与数论交叉 (*Algebraische Geometrie und Zahlentheorie*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Ergänzung E.1: Arithmetische Geometrie |
| **类型** | Interdisziplinär (跨学科型) |
| **ETH风格** | AG-Zahlentheorie Schnittstelle |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 90-120分钟 |

---

## 问题陈述

> **Aufgabe** (Interdisziplinär):
> Es sei $K$ ein Zahlkörper mit Ganzheitsring $\mathcal{O}_K$,
> und $X \to \operatorname{Spec}(\mathcal{O}_K)$ ein reguläres projektives Schema
> mit generischer Faser $X_K$ glatt.
> 
> (a) Erklären Sie, wie die geometrischen Methoden der algebraischen Geometrie
>     auf arithmetische Probleme angewendet werden können.
> 
> (b) Diskutieren Sie die Reduktion modulo Primzahlen:
>     Was ist die Faser $X_{\mathfrak{p}}$ über einem Primideal $\mathfrak{p} \subseteq \mathcal{O}_K$?
> 
> (c) **Beispiel**: Betrachten Sie die elliptische Kurve
>     $E: y^2 = x^3 - x$ über $\mathbb{Q}$.
>     Untersuchen Sie die Reduktion modulo verschiedener Primzahlen.

### 中文翻译

> **习题** (跨学科)：
> 设 $K$ 为数域，$\mathcal{O}_K$ 为其整数环，
> $X \to \operatorname{Spec}(\mathcal{O}_K)$ 为正则射影概形，
> 一般纤维 $X_K$ 光滑。
> 
> (a) 解释如何将代数几何的几何方法应用于算术问题。
> 
> (b) 讨论素数模约化：素理想 $\mathfrak{p} \subseteq \mathcal{O}_K$ 上的纤维 $X_{\mathfrak{p}}$ 是什么？
> 
> (c) **例子**：考虑 $\mathbb{Q}$ 上的椭圆曲线 $E: y^2 = x^3 - x$。
>     研究模不同素数的约化。

---

## 详细解答

### Teil (a): 几何方法在算术中的应用

**Grundprinzip der Arithmetischen Geometrie**:

Arithmetische Probleme werden durch geometrische Methoden angegangen:

1. **Geometrisierung**: Ersetze $\mathbb{Z}$ durch $\operatorname{Spec}(\mathbb{Z})$
2. **Schematheorie**: Arbeite mit Schemata über $\operatorname{Spec}(\mathbb{Z})$
3. **Geometrische Intuition**: Nutze geometrische Konzepte (Kurven, Fasern, Singularitäten)

**Beispiele**:

| Arithmetisches Problem | Geometrische Methode |
|----------------------|---------------------|
| Lösungen von Gleichungen | Punkte auf Varietäten |
| Primzahlverteilung | Fasern über $\operatorname{Spec}(\mathbb{Z})$ |
| Galois-Theorie | Étale Fundamentalgruppe |
| L-Funktionen | Zeta-Funktionen von Schemata |

---

### Teil (b): 素数模约化

**Definition**: Die Faser über $\mathfrak{p}$ ist:
$$X_{\mathfrak{p}} = X \times_{\operatorname{Spec}(\mathcal{O}_K)} \operatorname{Spec}(k(\mathfrak{p}))$$

wobei $k(\mathfrak{p}) = \mathcal{O}_K/\mathfrak{p}$ der endliche Restklassenkörper ist.

**Typen von Reduktion**:

| Typ | Bedingung | Beispiel |
|-----|-----------|----------|
| Gute Reduktion | $X_{\mathfrak{p}}$ glatt | $E$ hat gute Reduktion |
| Multiplikative Reduktion | Knoten-Singularität | Semistabil |
| Additive Reduktion | Spitzen-Singularität | Instabil |

---

### Teil (c): 椭圆曲线的例子

**Beispiel**: $E: y^2 = x^3 - x$ über $\mathbb{Q}$.

**Diskriminante**: $\Delta = 64$ (Kurven ist $y^2 = x^3 - x$, Diskriminante $-64$)

**Reduktionsanalyse**:

**$p = 2$**: Schlechte Reduktion
- $\Delta \equiv 0 \pmod{2}$
- Die Kurve hat additive Reduktion

**$p$ ungerade**:

- **$p \equiv 3 \pmod{4}$**: 
  $|E(\mathbb{F}_p)| = p + 1$ (Supersingular)
  
- **$p \equiv 1 \pmod{4}$**:
  $|E(\mathbb{F}_p)| = p + 1 - 2a$, wobei $p = a^2 + b^2$

**Verifikation für $p = 3$**:

$E: y^2 = x^3 - x$ über $\mathbb{F}_3$

Punkte:
- $x = 0$: $y^2 = 0$ $\Rightarrow$ $y = 0$ (1 Punkt: $(0,0)$)
- $x = 1$: $y^2 = 0$ $\Rightarrow$ $y = 0$ (1 Punkt: $(1,0)$)
- $x = 2$: $y^2 = 8 - 2 = 6 \equiv 0$ $\Rightarrow$ $y = 0$ (1 Punkt: $(2,0)$)

Plus Punkt im Unendlichen: $|E(\mathbb{F}_3)| = 4 = 3 + 1$ ✓

---

**创建日期**: 2026-04-10
