---
习题编号: AG-ETH-012
标题: Serre对偶的验证
type: Technische Verifikation (技术验证型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 4.5
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 90-120分钟
msc: 14F25, 14H99
eth_style: Streng + Explizit
---

# AG-ETH-012: Serre对偶的验证 (*Verifikation der Serre-Dualität*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 4.5: Serre-Dualität |
| **类型** | Technische Verifikation (技术验证型) |
| **ETH风格** | (S) Streng + (E) Explizit |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 90-120分钟 |

---

## 问题陈述

> **Aufgabe** (Streng und Explizit):
> Es sei $X$ eine glatte projektive Kurve der genus $g$ über einem
> algebraisch abgeschlossenen Körper $k$.
> 
> (a) Formulieren Sie streng den **Satz von Serre-Dualität** für Kurven.
> 
> (b) Verifizieren Sie explizit die Serre-Dualität für $X = \mathbb{P}^1_k$:
>     Berechnen Sie beide Seiten der Dualität für $\mathcal{F} = \mathcal{O}(n)$
>     und zeigen Sie die kanonische Isomorphie.
> 
> (c) Zeigen Sie für eine beliebige Kurve $X$: 
>     $\dim H^0(X, \omega_X) = \dim H^1(X, \mathcal{O}_X) = g$.

### 中文翻译

> **习题** (严格且显式)：
> 设 $X$ 为代数闭域 $k$ 上的亏格 $g$ 的光滑射影曲线。
> 
> (a) 严格陈述曲线情形的**Serre对偶定理**。
> 
> (b) 对 $X = \mathbb{P}^1_k$ 显式验证Serre对偶：
>     对 $\mathcal{F} = \mathcal{O}(n)$ 计算等式两边，并证明典范同构。
> 
> (c) 对任意曲线 $X$ 证明：
>     $\dim H^0(X, \omega_X) = \dim H^1(X, \mathcal{O}_X) = g$。

---

## 详细解答

### Teil (a): Serre对偶的严格陈述

**Theorem** (Serre-Dualität für Kurven):

Sei $X$ eine glatte projektive Kurve, $\mathcal{F}$ eine kohärente Garbe auf $X$.

Es existiert ein kanonischer Isomorphismus:
$$H^i(X, \mathcal{F}) \cong H^{1-i}(X, \omega_X \otimes \mathcal{F}^\vee)^*$$

für $i = 0, 1$.

Äquivalent: Es gibt eine perfekte Paarung:
$$H^0(X, \mathcal{F}) \times H^1(X, \omega_X \otimes \mathcal{F}^\vee) \to k$$

**Kanonizität**: Der Isomorphismus wird durch den Spur-Isomorphismus
$$\operatorname{Tr}: H^1(X, \omega_X) \xrightarrow{\sim} k$$
induziert.

---

### Teil (b): $\mathbb{P}^1$ 的显式验证

**Setup**: $X = \mathbb{P}^1$, $\mathcal{F} = \mathcal{O}(n)$.

**Berechnung für $i = 0$**:

Linke Seite: 
$$H^0(\mathbb{P}^1, \mathcal{O}(n)) = \begin{cases} k^{n+1} & n \geq 0 \\ 0 & n < 0 \end{cases}$$

Rechte Seite:
$$H^1(\mathbb{P}^1, \omega_{\mathbb{P}^1} \otimes \mathcal{O}(-n))^*$$

Wir wissen: $\omega_{\mathbb{P}^1} = \mathcal{O}(-2)$.

Also:
$$H^1(\mathbb{P}^1, \mathcal{O}(-n-2))^* = \begin{cases} 0 & n \geq 0 \\ k^{|n|-1} & n < 0 \end{cases}^*$$

Dies ist konsistent mit dem Serre-Dualität (Dimensionen stimmen überein).

**Verifikation der Paarung**:

Für $n \geq 0$:
- Ein Element von $H^0(\mathbb{P}^1, \mathcal{O}(n))$ ist ein homogenes Polynom $P(x_0, x_1)$ vom Grad $n$
- Ein Element von $H^1(\mathbb{P}^1, \mathcal{O}(-n-2))$ ist durch einen Hauptteil gegeben

Die Paarung ist gegeben durch das Residuum:
$$\langle P, \eta \rangle = \operatorname{Res}(P \cdot \eta)$$

---

### Teil (c): 亏格的计算

**Behauptung**: $\dim H^0(X, \omega_X) = \dim H^1(X, \mathcal{O}_X) = g$.

**Beweis**:

Mit $\mathcal{F} = \mathcal{O}_X$ in Serre-Dualität:
$$H^0(X, \mathcal{O}_X) \cong H^1(X, \omega_X)^*$$
$$H^1(X, \mathcal{O}_X) \cong H^0(X, \omega_X)^*$$

Also:
$$\dim H^1(X, \mathcal{O}_X) = \dim H^0(X, \omega_X)$$

Die Definition des Genus:
$$g = \dim H^1(X, \mathcal{O}_X) = \dim H^0(X, \omega_X)$$ ∎

---

**创建日期**: 2026-04-10
