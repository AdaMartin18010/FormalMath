---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Gauss引理 (Gauss's Lemma)
---
# Gauss引理 (Gauss's Lemma)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Content

namespace GaussLemma

variable {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]

/-- Gauss引理：本原多项式的乘积仍本原 -/
theorem gauss_lemma_primitive {p q : Polynomial R} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  -- 反证法：假设有素因子
  sorry

/-- 多项式可约性在分式域和原环的关系 -/
theorem irreducible_of_fraction_field {p : Polynomial R} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (map (algebraMap R (FractionRing R)) p) := by
  sorry

end GaussLemma
```

## 数学背景

Gauss引理由德国数学家Carl Friedrich Gauss在其1801年的巨著《算术研究》（Disquisitiones Arithmeticae）中首次系统阐述，是多项式理论和环论中最基本的结果之一。这个引理建立了整环上多项式的本原性与可约性之间的深刻联系，为Eisenstein判别法等重要工具的证明奠定了基础，也是证明唯一分解整环上多项式环仍是唯一分解整环的核心步骤。

### 本原多项式

**定义（内容与本原多项式）**：设 $R$ 是唯一分解整环（UFD），$f(x) = a_n x^n + a_{n-1}x^{n-1} + \cdots + a_1 x + a_0 \in R[x]$ 是非常数多项式。$f$ 的**内容**（content），记作 $c(f)$ 或 $\text{cont}(f)$，定义为系数 $a_n, a_{n-1}, \ldots, a_0$ 的最大公因子（在相伴意义下唯一）：

$$c(f) = \gcd(a_n, a_{n-1}, \ldots, a_0)$$

若 $c(f)$ 是 $R$ 中的单位（即可逆元），则称 $f$ 是**本原多项式**（primitive polynomial）。

等价地，$f$ 是本原的当且仅当它的系数在 $R$ 中没有共同的非常数因子。

### 分式域上的多项式

若 $R$ 是整环，其**分式域**（field of fractions）$K = \text{Frac}(R)$ 由所有形式分数 $a/b$（$a, b \in R$，$b \neq 0$）在等价关系 $a/b \sim c/d \iff ad = bc$ 下构成。$R[x]$ 可以自然嵌入到 $K[x]$ 中。

## Gauss引理的陈述

Gauss引理包含两个密切相关的结论：

**引理（Gauss引理，第一部分）**：设 $R$ 是唯一分解整环，$f, g \in R[x]$ 是本原多项式，则它们的乘积 $fg$ 也是本原多项式。

**引理（Gauss引理，第二部分）**：设 $R$ 是唯一分解整环，$K = \text{Frac}(R)$ 是其分式域。若 $f \in R[x]$ 是本原多项式，则 $f$ 在 $R[x]$ 中不可约当且仅当 $f$ 在 $K[x]$ 中不可约。

## 证明

### 第一部分的证明

**证明**：设 $f, g \in R[x]$ 是本原多项式。假设 $fg$ 不是本原的，则存在 $R$ 中的素元（不可约元）$p$ 整除 $fg$ 的所有系数。

由于 $f$ 是本原的，$p$ 不整除 $f$ 的所有系数。设 $a_i$ 是 $f$ 的系数中**第一个**不被 $p$ 整除的（即下标最小者）。类似地，设 $b_j$ 是 $g$ 的系数中第一个不被 $p$ 整除的。

考虑 $fg$ 中 $x^{i+j}$ 的系数：

$$c_{i+j} = a_0 b_{i+j} + a_1 b_{i+j-1} + \cdots + a_i b_j + \cdots + a_{i+j} b_0$$

对于 $k < i$，$p | a_k$（由 $a_i$ 的选取）；对于 $l < j$，$p | b_l$（由 $b_j$ 的选取）。

因此，在求和式中，除了 $a_i b_j$ 项外，所有其他项要么含因子 $a_k$（$k < i$，被 $p$ 整除），要么含因子 $b_l$（$l < j$，被 $p$ 整除）。所以：

$$p \mid (c_{i+j} - a_i b_j)$$

但我们假设 $p \mid c_{i+j}$（因为 $p$ 整除 $fg$ 的所有系数），因此 $p \mid a_i b_j$。

由于 $R$ 是UFD，$p$ 是素元，故 $p \mid a_i$ 或 $p \mid b_j$。这与 $a_i$ 和 $b_j$ 的选取矛盾。因此 $fg$ 必须是本原的。 $\square$

### 第二部分的证明

**证明**：$(\Rightarrow)$ 设 $f$ 在 $R[x]$ 中不可约。假设 $f$ 在 $K[x]$ 中可约，则存在分解 $f = gh$，其中 $g, h \in K[x]$ 都是非常数的。

将 $g$ 和 $h$ 通分，可以写成 $g = g_1 / a$，$h = h_1 / b$，其中 $g_1, h_1 \in R[x]$，$a, b \in R \setminus \{0\}$。于是：

$$abf = g_1 h_1$$

设 $c(g_1)$ 和 $c(h_1)$ 分别是 $g_1$ 和 $h_1$ 的内容。提取内容，设 $g_1 = c(g_1) g_2$，$h_1 = c(h_1) h_2$，其中 $g_2, h_2$ 是本原的。则：

$$abf = c(g_1)c(h_1) \cdot g_2 h_2$$

由Gauss引理第一部分，$g_2 h_2$ 是本原的。比较两边的内容：

$$ab \cdot c(f) = c(g_1)c(h_1) \cdot c(g_2 h_2) = c(g_1)c(h_1) \cdot 1$$

由于 $f$ 是本原的，$c(f) = 1$，故 $ab = c(g_1)c(h_1)$。

因此 $f = g_2 h_2$（在 $R[x]$ 中），其中 $g_2, h_2$ 都是非常数的（因为它们在 $K[x]$ 中对应于 $g$ 和 $h$ 的非零常数倍）。这与 $f$ 在 $R[x]$ 中不可约矛盾。

$(\Leftarrow)$ 设 $f$ 在 $K[x]$ 中不可约。假设 $f$ 在 $R[x]$ 中可约，$f = gh$，其中 $g, h \in R[x]$ 都是非常数的。由于 $R[x] \subseteq K[x]$，这也是 $K[x]$ 中的分解，与 $f$ 在 $K[x]$ 中不可约矛盾。 $\square$

## 例子

### 例子1：整数环上的本原多项式

设 $f(x) = 2x^2 + 3x + 5$，$g(x) = 3x + 7$。$\gcd(2, 3, 5) = 1$，$\gcd(3, 7) = 1$，所以 $f$ 和 $g$ 都是 $\mathbb{Z}[x]$ 中的本原多项式。

$$fg = 6x^3 + 23x^2 + 44x + 35$$

$\gcd(6, 23, 44, 35) = \gcd(6, 23) = 1$（因为 $23$ 是素数且不整除 $6$），所以 $fg$ 是本原的，验证了Gauss引理。

### 例子2：非本原多项式的乘积

设 $f(x) = 2x + 4 = 2(x + 2)$，$g(x) = 3x + 6 = 3(x + 2)$。两者都不是本原的（内容分别为 $2$ 和 $3$）。

$$fg = 6x^2 + 24x + 24 = 6(x^2 + 4x + 4) = 6(x+2)^2$$

内容为 $6$，不是本原的。注意本原部分 $(x+2)^2$ 的乘积仍是本原的。

### 例子3：不可约性的保持

考虑 $f(x) = x^2 + 1 \in \mathbb{Z}[x]$。它是本原的（系数 $\gcd(1, 0, 1) = 1$）。在 $\mathbb{Q}[x]$ 中，$x^2 + 1$ 不可约（没有有理根，且二次）。由Gauss引理，$x^2 + 1$ 在 $\mathbb{Z}[x]$ 中也不可约。

若考虑 $g(x) = 2x^2 + 2 = 2(x^2 + 1)$，它不是本原的（内容为 $2$）。$g$ 在 $\mathbb{Z}[x]$ 中可约（$2 \cdot (x^2 + 1)$），但在 $\mathbb{Q}[x]$ 中对应于 $x^2 + 1$，是不可约的。这说明了本原性假设的必要性。

### 例子4：多变量情形

Gauss引理可以迭代应用。由于 $\mathbb{Z}[x, y] = \mathbb{Z}[x][y]$，且 $\mathbb{Z}[x]$ 是UFD（由Gauss引理），$\mathbb{Z}[x, y]$ 也是UFD。类似地，任何UFD上的有限元多项式环仍是UFD。

## 应用

### 1. Eisenstein判别法的证明

**Eisenstein判别法**：设 $R$ 是UFD，$f(x) = a_n x^n + \cdots + a_0 \in R[x]$。若存在 $R$ 中的素元 $p$，使得：
- $p \nmid a_n$
- $p \mid a_i$ 对所有 $i = 0, 1, \ldots, n-1$
- $p^2 \nmid a_0$

则 $f$ 在 $R[x]$ 中不可约（若在 $K[x]$ 中本原）。

证明的关键步骤是利用Gauss引理将 $R[x]$ 中的不可约性转化为 $K[x]$ 中的不可约性。

### 2. UFD上多项式环仍是UFD

**定理**：若 $R$ 是UFD，则 $R[x]$ 也是UFD。

**证明概要**：$K[x]$ 是主理想整环（PID），从而是UFD。利用Gauss引理，$R[x]$ 中的分解可以"提升"自 $K[x]$ 中的分解，且本原多项式的分解在相伴意义下唯一。结合内容的唯一分解性（$R$ 是UFD），得到 $R[x]$ 中分解的唯一性。 $\square$

### 3. 代数数论中的整性判定

在代数数论中，Gauss引理用于证明代数整数的极小多项式可以取为 $\mathbb{Z}[x]$ 中的首一多项式。若 $\alpha$ 是代数整数，其极小多项式 $m_\alpha(x) \in \mathbb{Q}[x]$ 可以乘以适当整数使其成为本原的整系数多项式，由Gauss引理这个多项式在 $\mathbb{Z}[x]$ 中不可约。

### 4. 形式幂级数与p进数

Gauss引理的思想可以推广到更一般的赋值环和完备离散赋值环上。在p进数域 $\mathbb{Q}_p$ 中，整数环 $\mathbb{Z}_p$ 上多项式的本原性和可约性之间也有类似关系，这在p进分析中很重要。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
