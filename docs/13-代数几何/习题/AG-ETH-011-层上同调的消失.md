---
习题编号: AG-ETH-011
标题: 层上同调的消失
type: Theoretische Verifikation (理论型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 4.4
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 60-90分钟
msc: 14F17, 14E15
eth_style: Streng + Systematisch
---

# AG-ETH-011: 层上同调的消失 (*Verschwindungssätze*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 4.4: Verschwindungssätze in der Kohomologie |
| **类型** | Theoretische Verifikation (理论型) |
| **ETH风格** | (S) Streng + Systematisch |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 60-90分钟 |

---

## 问题陈述

> **Aufgabe** (Streng und Systematisch):
> Es sei $X$ ein projektives Schema über einem algebraisch abgeschlossenen
> Körper $k$, und $\mathcal{L}$ eine ample Geradenbündel auf $X$.
> 
> (a) Beweisen Sie streng den **Verschwindungssatz von Serre**:
>     Für jede kohärente Garbe $\mathcal{F}$ auf $X$ existiert $n_0$,
>     so dass $H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0$ 
>     für alle $i > 0$ und $n \geq n_0$.
> 
> (b) Zeigen Sie: Ist $X$ glatt projektiv der Dimension $n$, so gilt
>     für die kanonische Garbe $\omega_X$:
>     $$H^i(X, \omega_X \otimes \mathcal{L}) = 0 \text{ für } i < n$$
>     (Kodaira-Verschwinden).
> 
> (c) Verbinden Sie diese Sätze mit der effektiven Berechnung von Kohomologie.

### 中文翻译

> **习题** (严格且系统化)：
> 设 $X$ 为代数闭域 $k$ 上的射影概形，$\mathcal{L}$ 为 $X$ 上的丰富线丛。
> 
> (a) 严格证明**Serre消失定理**：
>     对 $X$ 上的每个凝聚层 $\mathcal{F}$，存在 $n_0$，
>     使得对所有 $i > 0$ 和 $n \geq n_0$，
>     $H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0$。
> 
> (b) 证明：若 $X$ 为光滑射影 $n$ 维，则对典范层 $\omega_X$：
>     $$H^i(X, \omega_X \otimes \mathcal{L}) = 0 \text{ für } i < n$$
>     (Kodaira消失)。
> 
> (c) 将这些定理与上同调的有效计算联系起来。

---

## 详细解答

### Teil (a): Serre消失定理

**Theorem** (Serre-Verschwinden):

Sei $\mathcal{L}$ ample auf projektivem $X$. Für kohärentes $\mathcal{F}$:
$$\exists n_0: H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0 \text{ für } i > 0, n \geq n_0$$

**Beweis** (Streng):

**Schritt 1**: Reduktion auf $\mathcal{L} = \mathcal{O}(1)$ auf $\mathbb{P}^N$

Da $\mathcal{L}$ ample, existiert eine Einbettung $\phi_{\mathcal{L}^m}: X \hookrightarrow \mathbb{P}^N$
mit $\mathcal{L}^m = \phi^*\mathcal{O}(1)$.

**Schritt 2**: Projektiver Fall

Für $X = \mathbb{P}^N$ und $\mathcal{F} = \mathcal{O}(d)$:
$$H^i(\mathbb{P}^N, \mathcal{O}(d)) = 0 \text{ für } 0 < i < N \text{ und alle } d$$
$$H^N(\mathbb{P}^N, \mathcal{O}(d)) = 0 \text{ für } d > -N-1$$

**Schritt 3**: Allgemeiner Fall

Mittels Projektionsformel:
$$H^i(X, \mathcal{F} \otimes \mathcal{L}^{mk}) = H^i(\mathbb{P}^N, \phi_*\mathcal{F} \otimes \mathcal{O}(k))$$

Für $k \gg 0$ verschwindet dies nach dem projektiven Fall. ∎

---

### Teil (b): Kodaira消失

**Theorem** (Kodaira-Verschwinden):

Für $X$ glatt projektiv, $\mathcal{L}$ ample:
$$H^i(X, \omega_X \otimes \mathcal{L}) = 0 \text{ für } i < \dim(X)$$

**Beweis**:

Nach Serre-Dualität:
$$H^i(X, \omega_X \otimes \mathcal{L}) \cong H^{n-i}(X, \mathcal{L}^{-1})^*$$

Da $\mathcal{L}^{-1}$ anti-ample, verschwindet $H^j(X, \mathcal{L}^{-1})$ für $j < n$
nach dem Serre-Verschwinden (für negative Twist). ∎

---

### Teil (c): 有效计算

**Anwendung**:

Verschwindungssätze erlauben die effektive Berechnung von Kohomologie:

1. **Für $H^0$**: Berechne direkt die globalen Schnitte
2. **Für $H^n$**: Verwende Serre-Dualität
3. **Für andere $H^i$**: Verwende Verschwinden, um auf Fälle zu reduzieren,
   wo explizite Berechnung möglich ist

---

**创建日期**: 2026-04-10
