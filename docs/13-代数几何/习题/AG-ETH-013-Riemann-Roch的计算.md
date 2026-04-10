---
习题编号: AG-ETH-013
标题: Riemann-Roch的计算
type: Explizite Berechnung (计算型)
difficulty: ⭐⭐⭐⭐
章节: ETH 401-3532 Kapitel 4.6
course: ETH Zurich 401-3532-00L
对应课程: ETH Algebraic Geometry II
预计用时: 60-90分钟
msc: 14H99, 14C40
eth_style: Explizit + Anwendung
---

# AG-ETH-013: Riemann-Roch的计算 (*Riemann-Roch Berechnung*)

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | ETH Zurich 401-3532-00L |
| **ETH章节** | Kapitel 4.6: Der Satz von Riemann-Roch |
| **类型** | Explizite Berechnung (计算型) |
| **ETH风格** | (E) Explizit + (A) Anwendung |
| **难度** | ⭐⭐⭐⭐ |
| **预计用时** | 60-90分钟 |

---

## 问题陈述

> **Aufgabe** (Explizit und Anwendung):
> Es sei $X$ eine glatte projektive Kurve der genus $g$ über einem
> algebraisch abgeschlossenen Körper $k$.
> 
> (a) Formulieren Sie den **Satz von Riemann-Roch**.
> 
> (b) Berechnen Sie explizit für $X = \mathbb{P}^1$ und einen Divisor
>     $D = n \cdot [\infty]$ mit $n \geq 0$:
>     - $\ell(D) = \dim H^0(X, \mathcal{O}_X(D))$
>     - $\ell(K - D) = \dim H^0(X, \omega_X(-D))$
>     - Verifizieren Sie die Riemann-Roch-Formel.
> 
> (c) Es sei $X$ eine elliptische Kurve ($g = 1$) und $P \in X$ ein Punkt.
>     Berechnen Sie $\ell(nP)$ für $n \geq 1$.

### 中文翻译

> **习题** (显式且应用)：
> 设 $X$ 为代数闭域 $k$ 上的亏格 $g$ 的光滑射影曲线。
> 
> (a) 陈述**Riemann-Roch定理**。
> 
> (b) 对 $X = \mathbb{P}^1$ 和除子 $D = n \cdot [\infty]$（$n \geq 0$）显式计算：
>     - $\ell(D) = \dim H^0(X, \mathcal{O}_X(D))$
>     - $\ell(K - D) = \dim H^0(X, \omega_X(-D))$
>     - 验证Riemann-Roch公式。
> 
> (c) 设 $X$ 为椭圆曲线（$g = 1$），$P \in X$ 为一点。
>     计算 $n \geq 1$ 时的 $\ell(nP)$。

---

## 详细解答

### Teil (a): Riemann-Roch定理

**Theorem** (Riemann-Roch):

Sei $X$ eine glatte projektive Kurve der genus $g$, $D$ ein Divisor auf $X$.

Dann:
$$\ell(D) - \ell(K - D) = \deg(D) + 1 - g$$

wobei:
- $\ell(D) = \dim_k H^0(X, \mathcal{O}_X(D))$
- $K$ ein kanonischer Divisor
- $\deg(D)$ der Grad des Divisors

---

### Teil (b): $\mathbb{P}^1$ 的显式计算

**Setup**: $X = \mathbb{P}^1$, $D = n \cdot [\infty]$, $n \geq 0$.

**Berechnung**:

**Schritt 1**: $\ell(D)$

$\mathcal{O}_{\mathbb{P}^1}(D) = \mathcal{O}(n)$.

$$\ell(D) = \dim H^0(\mathbb{P}^1, \mathcal{O}(n)) = n + 1$$

**Schritt 2**: $\ell(K - D)$

Für $\mathbb{P}^1$: $K = -2[\infty]$ (da $\omega_{\mathbb{P}^1} = \mathcal{O}(-2)$).

Also:
$$K - D = -2[\infty] - n[\infty] = -(n+2)[\infty]$$

$$\ell(K - D) = \dim H^0(\mathbb{P}^1, \mathcal{O}(-n-2)) = 0$$

(da negativer Grad).

**Schritt 3**: Riemann-Roch verifizieren

Für $\mathbb{P}^1$: $g = 0$.

Linke Seite:
$$\ell(D) - \ell(K - D) = (n + 1) - 0 = n + 1$$

Rechte Seite:
$$\deg(D) + 1 - g = n + 1 - 0 = n + 1$$

**Übereinstimmung**: ✓ ∎

---

### Teil (c): 椭圆曲线上的计算

**Setup**: $X$ elliptische Kurve ($g = 1$), $P \in X$.

**Behauptung**:
$$\ell(nP) = \begin{cases} 1 & n = 0 \\ n & n \geq 1 \end{cases}$$

**Beweis**:

**Fall $n = 0$**: $\ell(0) = 1$ (nur Konstanten).

**Fall $n = 1$**: 

Riemann-Roch:
$$\ell(P) - \ell(K - P) = 1 + 1 - 1 = 1$$

Da $g = 1$, ist $K$ linear äquivalent zu $0$.
Also $\ell(K - P) = \ell(-P) = 0$.

Daraus: $\ell(P) = 1$.

**Fall $n \geq 2$**:

Riemann-Roch:
$$\ell(nP) - \ell(K - nP) = n + 1 - 1 = n$$

Für $n \geq 2$: $\deg(K - nP) = -n < 0$, also $\ell(K - nP) = 0$.

Daraus: $\ell(nP) = n$. ∎

---

**创建日期**: 2026-04-10
