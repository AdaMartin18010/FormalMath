---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Hilbert零点定理 (Hilbert's Nullstellensatz)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Nullstellensatz

namespace Nullstellensatz

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {n : ℕ} {I : Ideal (MvPolynomial (Fin n) k)}

/-- Hilbert零点定理：弱形式 -/
theorem weak_nullstellensatz (hI : I ≠ ⊤) :
    ∃ x : Fin n → k, ∀ p ∈ I, MvPolynomial.eval x p = 0 := by
  -- 利用Noether正规化和Zariski引理
  sorry

/-- Hilbert零点定理：强形式 -/
theorem strong_nullstellensatz {p : MvPolynomial (Fin n) k}
    (hp : ∀ x : Fin n → k, (∀ q ∈ I, MvPolynomial.eval x q = 0) → MvPolynomial.eval x p = 0) :
    ∃ m : ℕ, p ^ m ∈ I := by
  -- Rabinowitsch技巧
  sorry

/-- 零点理想与根理想的对应 -/
theorem ideal_variety_correspondence :
    GaloisConnection (fun I => variety I) (fun V => ideal V) := by
  -- 强零点定理的直接推论
  sorry

end Nullstellensatz
```

## 数学背景

Hilbert零点定理由David Hilbert在1893年证明，是代数几何的奠基性结果。该定理建立了代数（多项式理想的根）与几何（仿射簇）之间的基本对应，被称为"零点定理"（德语：Nullstellensatz，即"位置定理"）。这是经典代数几何的基石，表明在代数闭域上，多项式方程组的几何解集与代数结构有完美的对应关系。

## 直观解释

零点定理告诉我们：**在代数闭域上，多项式方程的解完全由理想决定**。

想象多项式方程组 $f_1 = f_2 = \cdots = f_m = 0$。零点定理说，如果一个多项式 $g$ 在所有这些方程的解上为零，那么 $g$ 的某个幂可以表示为 $f_i$ 的组合。这就像说，解集的几何信息完全编码在代数理想中，反之亦然。

## 形式化表述

设 $k$ 是代数闭域，$I \subseteq k[x_1, \ldots, x_n]$ 是理想。

**零点集**：$V(I) = \{x \in k^n : f(x) = 0, \forall f \in I\}$

**理想**：$I(V) = \{f \in k[x_1, \ldots, x_n] : f(x) = 0, \forall x \in V\}$

**弱零点定理**：若 $I \neq (1)$，则 $V(I) \neq \emptyset$（非空解集）

**强零点定理**：$I(V(I)) = \sqrt{I}$（根理想）

**Galois对应**：根理想 $\leftrightarrow$ 仿射簇

## 证明思路

1. **Noether正规化**：
   - 将 $k[x_1, \ldots, x_n]/I$ 整扩张到多项式环

2. **Zariski引理**：
   - 域的有限生成代数是有限扩张
   - 代数闭域上，$k[x_1, \ldots, x_n]/\mathfrak{m} \cong k$

3. **弱形式推出强形式**（Rabinowitsch技巧）：
   - 引入新变量 $y$，考虑 $I' = I + (1 - yp)$
   - 应用弱形式，推导 $p \in \sqrt{I}$

核心洞察是代数闭域上极大理想的"点"结构。

## 示例

### 示例 1：单变量

$k[x]$，$I = (x^2)$。

$V(I) = \{0\}$，$I(V(I)) = (x) = \sqrt{(x^2)}$。

### 示例 2：双曲线

$I = (xy - 1) \subseteq \mathbb{C}[x,y]$。

$V(I) = \{(t, 1/t) : t \neq 0\}$。

$I(V(I)) = (xy - 1) = \sqrt{I}$（素理想）。

### 示例 3：非代数闭域的反例

$k = \mathbb{R}$，$I = (x^2 + 1) \subseteq \mathbb{R}[x]$。

$I \neq (1)$ 但 $V(I) = \emptyset$（在 $\mathbb{R}$ 中）。

需要代数闭域条件。

## 应用

- **代数几何**：仿射簇与代数的基本对应
- **交换代数**：Krull维数理论
- **数论**：Diophantine几何
- **计算代数**：Gröbner基的消去理论
- **量子信息**：量子态的代数描述

## 相关概念

- [仿射簇 (Affine Variety)](./affine-variety.md)：多项式方程的解集
- [根理想 (Radical Ideal)](./radical-ideal.md)：等于其根的理想
- [代数闭域 (Algebraically Closed Field)](./algebraically-closed-field.md)：所有多项式有根
- [Noether正规化 (Noether Normalization)](./noether-normalization.md)：代数的结构定理
- [Zariski拓扑 (Zariski Topology)](./zariski-topology.md)：代数几何的拓扑

## 参考

### 教材

- [Atiyah & Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 7]
- [Eisenbud. Commutative Algebra. Springer, 1995. Chapter 4]

### 历史文献

- [Hilbert. Über die vollen Invariantensysteme. 1893]

### 在线资源

- [Mathlib4 文档 - Nullstellensatz](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nullstellensatz.html)
- [Stacks Project - 00FV](https://stacks.math.columbia.edu/tag/00FV)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
