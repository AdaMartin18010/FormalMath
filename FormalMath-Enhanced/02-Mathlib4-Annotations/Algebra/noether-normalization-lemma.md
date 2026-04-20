---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Noether正规化引理 (Noether Normalization Lemma)
---
# Noether正规化引理 (Noether Normalization Lemma)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Localization.Basic

namespace NoetherNormalizationLemma

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Noether正规化引理 -/
theorem noether_normalization [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (y : Fin n → A),
      Algebra.Independent k y ∧ Algebra.IsIntegral (MvPolynomial (Fin n) k) A := by
  -- 对生成元个数归纳
  sorry

/-- 几何解释：仿射代数的有限映射 -/
theorem geometric_interpretation [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (φ : Spec A → AffineSpace k n),
      IsFinite φ ∧ IsSurjective φ := by
  -- 对应Noether正规化
  sorry

end NoetherNormalizationLemma
```

## 数学背景

Noether正规化引理由德国数学家Emmy Noether于1926年证明，是交换代数和代数几何中最基本、最重要的结构定理之一。它揭示了有限生成代数与多项式代数之间的深刻关系，表明任何有限生成的交换代数在适当坐标变换后，都可以表示为多项式环上的整扩张。这一结果在证明Hilbert零点定理、建立维数理论、理解代数簇的结构等方面发挥着核心作用。

### 整扩张与有限生成代数

**定义（整元素）**：设 $R \subseteq S$ 是环的扩张。元素 $s \in S$ 称为在 $R$ 上**整的**（integral over $R$），如果存在首一多项式 $f(x) = x^n + a_{n-1}x^{n-1} + \cdots + a_0 \in R[x]$，使得 $f(s) = 0$。

**定义（整扩张）**：若 $S$ 中每个元素都在 $R$ 上整，则称 $S$ 是 $R$ 的**整扩张**（integral extension）。

**定义（有限生成代数）**：设 $k$ 是域，$A$ 是 $k$-代数。称 $A$ 是**有限生成**的（finitely generated），如果存在有限个元素 $x_1, \ldots, x_m \in A$，使得 $A = k[x_1, \ldots, x_m]$（作为 $k$-代数的生成）。

## Noether正规化引理的陈述

**定理（Noether正规化引理）**：设 $k$ 是域，$A$ 是有限生成的交换 $k$-代数。则存在代数无关的元素 $y_1, \ldots, y_n \in A$（$n \geq 0$），使得 $A$ 在子代数 $k[y_1, \ldots, y_n]$ 上是整的。

形式化地，存在 $n \in \mathbb{N}$ 和 $y_1, \ldots, y_n \in A$，满足：
1. $y_1, \ldots, y_n$ 在 $k$ 上代数无关（即 $k[y_1, \ldots, y_n] \cong k[x_1, \ldots, x_n]$ 是 $n$ 元多项式环）；
2. 包含映射 $k[y_1, \ldots, y_n] \hookrightarrow A$ 是整扩张。

**注**：若 $k$ 是无限域，则 $y_i$ 可以取为原生成元的 $k$-线性组合。若 $k$ 是有限域，证明需要稍作修改，但结论仍然成立。

## 证明

### 证明（对无限域 $k$，使用线性变换）

**证明**：设 $A = k[x_1, \ldots, x_m]$ 由 $m$ 个元素生成。我们对 $m$ 进行归纳。

若 $x_1, \ldots, x_m$ 在 $k$ 上代数无关，则 $A \cong k[x_1, \ldots, x_m]$ 本身就是多项式环，取 $n = m$，$y_i = x_i$ 即可。

否则，存在非零多项式关系 $f(x_1, \ldots, x_m) = 0$。设 $f$ 的总次数为 $d > 0$。对变量做线性变换：

$$x_i = y_i + \lambda_i y_m \quad (i = 1, \ldots, m-1)$$
$$x_m = y_m$$

其中 $\lambda_1, \ldots, \lambda_{m-1} \in k$ 待定。代入 $f$：

$$f(y_1 + \lambda_1 y_m, \ldots, y_{m-1} + \lambda_{m-1} y_m, y_m) = 0$$

展开后，$y_m^d$ 的系数是 $f_d(\lambda_1, \ldots, \lambda_{m-1}, 1)$，其中 $f_d$ 是 $f$ 的 $d$ 次齐次部分。由于 $k$ 是无限域，可以选取 $\lambda_i$ 使得 $f_d(\lambda_1, \ldots, \lambda_{m-1}, 1) \neq 0$（非零多项式在无限域上不处处为零）。

于是 $y_m$ 满足一个关于 $k[y_1, \ldots, y_{m-1}]$ 的首一方程，即 $y_m$ 在 $k[y_1, \ldots, y_{m-1}]$ 上整。

因此 $A = k[x_1, \ldots, x_m] = k[y_1, \ldots, y_{m-1}, y_m]$ 在 $k[y_1, \ldots, y_{m-1}]$ 上整（因为 $y_m$ 整，而 $y_1, \ldots, y_{m-1}$ 显然整）。

令 $A' = k[y_1, \ldots, y_{m-1}]$。由归纳假设，$A'$ 中存在代数无关的元 $z_1, \ldots, z_n$，使得 $A'$ 在 $k[z_1, \ldots, z_n]$ 上整。

由整扩张的传递性，$A$ 在 $k[z_1, \ldots, z_n]$ 上整。证毕。 $\square$

### 对有限域的证明思路

若 $k$ 是有限域，线性变换可能不足以消除所有代数关系。此时可以使用**Nagata变换**：对某个充分大的整数 $r$，令：

$$x_i = y_i + y_m^{r^i} \quad (i = 1, \ldots, m-1)$$

选择 $r$ 大于 $f$ 中任何单项式的指数。这样在新的变量中，$y_m$ 的最高次项将唯一确定，从而保证 $y_m$ 满足首一方程。

## 几何解释

Noether正规化引理在代数几何中有极为直观的几何解释。

### 有限态射与投影

设 $A = k[x_1, \ldots, x_m]/I$ 是仿射簇 $X = V(I) \subseteq \mathbb{A}^m$ 的坐标环。Noether正规化引理给出的元素 $y_1, \ldots, y_n \in A$ 对应于一个线性投影：

$$\pi: X \to \mathbb{A}^n$$

使得 $\pi$ 是**有限态射**（finite morphism）。这意味着：
- $\pi$ 是满射；
- $\pi$ 的纤维是有限集；
- 坐标环的对应同态 $k[y_1, \ldots, y_n] \hookrightarrow A$ 使 $A$ 成为有限生成模。

**定理（几何Noether正规化）**：任何仿射簇 $X$ 都存在到某个仿射空间 $\mathbb{A}^n$ 的有限满射 $\pi: X \to \mathbb{A}^n$，其中 $n = \dim X$。

### 维数的几何意义

Noether正规化引理中的整数 $n$ 实际上就是代数 $A$ 的Krull维数。几何上，$n$ 是仿射簇 $X$ 的维数。引理表明：任何 $n$ 维仿射簇都可以被"有限地"参数化为 $n$ 维仿射空间。

## 例子

### 例子1：平面曲线

考虑 $A = k[x, y]/(xy - 1)$，对应双曲线 $xy = 1$。变量 $x$ 和 $y$ 在 $k$ 上不是代数无关的（因为 $xy = 1$）。

做变换 $x = u + v$，$y = u - v$。则：

$$(u+v)(u-v) = u^2 - v^2 = 1$$

于是 $v^2 = u^2 - 1$，即 $v$ 在 $k[u]$ 上整（满足首一方程 $t^2 - (u^2 - 1) = 0$）。而 $u$ 本身在 $k$ 上超越（代数无关）。

因此 $A$ 在 $k[u]$ 上整，Noether正规化给出的参数化对应于投影 $(x, y) \mapsto u = (x+y)/2$。

### 例子2：抛物线

设 $A = k[x, y]/(y - x^2)$。这里 $x$ 在 $k$ 上超越，$y$ 在 $k[x]$ 上整（因为 $y = x^2$）。取 $y_1 = x$，则 $A = k[x]$ 本身已经是多项式环，$n = 1$。

对应的投影 $\pi: V(y - x^2) \to \mathbb{A}^1$，$(x, y) \mapsto x$ 是同构（因为 $y = x^2$ 可以唯一解出）。

### 例子3：尖点曲线

设 $A = k[x, y]/(y^2 - x^3)$，对应尖点曲线 $y^2 = x^3$。取 $y_1 = y/x$（这不是 $k$-线性组合，需要更一般的变换）。

实际上，令 $t = y/x$（在分式域中），则 $t^2 = x$，$y = tx = t^3$。所以 $A \subseteq k[t]$，且 $k[t]$ 在 $A$ 上整（$t$ 满足 $t^2 - x = 0$，而 $x \in A$）。

由Noether正规化，$A$ 中存在代数无关元使得 $A$ 在其上整。这里 $A$ 的维数为 $1$。

### 例子4：乘积簇

设 $A = k[x_1, \ldots, x_n]$ 本身已是多项式环，则无需变换，$y_i = x_i$，$A$ 在自身上整（平凡地）。

## 应用

### 1. Hilbert零点定理的证明

Noether正规化引理是证明弱Hilbert零点定理的关键工具。

**弱Hilbert零点定理**：设 $k$ 是代数闭域，$I \subsetneq k[x_1, \ldots, x_m]$ 是真理想，则 $V(I) \neq \emptyset$（即存在公共零点）。

**证明思路**：假设 $V(I) = \emptyset$，则 $A = k[x_1, \ldots, x_m]/I$ 是Jacobson环。由Noether正规化，存在 $y_1, \ldots, y_n \in A$ 代数无关，使得 $A$ 在 $k[y_1, \ldots, y_n]$ 上整。

若 $n > 0$，则 $k[y_1, \ldots, y_n]$ 是无限环，$A$ 作为有限生成模也是无限维 $k$-向量空间。但由于 $V(I) = \emptyset$，可以证明 $A$ 实际上是有限维 $k$-向量空间（利用 $1 \in I$ 在某种意义下），矛盾。

若 $n = 0$，则 $A$ 在 $k$ 上整，即 $A$ 是有限维 $k$-代数，且由于是整环（在适当假设下），$A = k$。这意味着 $I$ 是极大理想，也有零点。

### 2. 维数理论

Noether正规化引理提供了计算Krull维数的标准方法：

**定理**：设 $A$ 是有限生成 $k$-代数，$y_1, \ldots, y_n$ 是Noether正规化给出的代数无关元。则：

$$\dim A = n$$

即 $A$ 的Krull维数等于Noether正规化中多项式环的变量个数。

### 3. 参数化与消解

在代数几何中，Noether正规化提供了将任意仿射簇"有限参数化"为仿射空间的方法。这类似于Riemann曲面理论中将代数曲线表示为复平面的有限覆叠。

在计算代数几何中，Noether正规化可以用来将高维问题约化为低维问题，或用于计算簇的维数和次数。

### 4. 交换代数中的下降与上升

利用Noether正规化将 $A$ 表示为 $k[y_1, \ldots, y_n]$ 的整扩张，可以结合整扩张的上升和下降定理（going-up and going-down theorems）来研究 $A$ 中素理想的结构。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
