---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Artin-Wedderburn 定理 (Artin-Wedderburn Theorem)
---
# Artin-Wedderburn 定理 (Artin-Wedderburn Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

namespace ArtinWedderburn

variable (R : Type*) [Ring R]

/-- Wedderburn-Artin 定理：半单环同构于矩阵环的有限直积 -/
theorem isSemisimpleRing_exists_algEquiv_pi_matrix_end_mulOpposite
    [IsSemisimpleRing R] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (D : ι → Type*)
      (_ : ∀ i, DivisionRing (D i)),
      Nonempty (R ≃+* ⨁ i, Matrix (Fin (n i)) (Fin (n i)) (D i)) := by
  -- 参见 Mathlib4 RingTheory.SimpleModule.WedderburnArtin
  sorry

end ArtinWedderburn
```

## 数学背景

Artin-Wedderburn 定理是环论与表示论中最深刻的结构定理之一，由 Joseph Wedderburn（1908）和 Emil Artin（1927）分别证明和推广。该定理对半单环给出了完全分类：任何半单环都同构于有限个除环上矩阵环的直积。这一定理不仅奠定了有限维代数的理论基础，也是研究群表示、李代数、量子群和 noncommutative 几何的核心工具。简单 Artin 环的特例（单矩阵环）更是现代线性代数的基石。

## 直观解释

Artin-Wedderburn 定理告诉我们：**半单环就像乐高积木一样，只能由一种基本积木块——“除环上的矩阵环”——拼装而成**。想象一个半单环是一座建筑，它可以拆成若干独立的塔楼（直积），每座塔楼内部又是一格格相同大小的房间按矩阵方式排列（矩阵环），而每个房间的值来自某个除环（类似于数域的推广）。

这与线性代数中的矩阵分解异曲同工：复杂线性变换可以约化为标准型，而半单环的结构约化则是代数层面的“标准型定理”。

## 形式化表述

**Artin-Wedderburn 定理**：设 $R$ 为半单环，则存在：

- 有限指标集 $I$
- 正整数 $n_i$（$i \in I$）
- 除环 $D_i$（$i \in I$）

使得：

$$R \cong \prod_{i \in I} M_{n_i}(D_i)$$

其中 $M_{n_i}(D_i)$ 表示除环 $D_i$ 上的 $n_i \times n_i$ 矩阵环。

**推论（简单 Artin 环）**：若 $R$ 为单 Artin 环，则 $R \cong M_n(D)$ 对某个除环 $D$ 和正整数 $n$ 成立。

## 证明思路

1. **半单性分解**：由半单性，$R$ 作为左 $R$-模可分解为有限个单模的直和
2. **同构单模归类**：将同构的单模归为一类，得到 $R \cong \bigoplus_{i} S_i^{\oplus n_i}$
3. **自同态环**：利用模范畴中的自同态环：$R^{op} \cong \prod_i \text{End}_R(S_i^{\oplus n_i}) \cong \prod_i M_{n_i}(\text{End}_R(S_i))$
4. **Schur 引理**：单模的自同态环 $\text{End}_R(S_i)$ 是除环
5. **取反环**：通过取反环（opposite ring）得到 $R$ 本身的矩阵分解

核心洞察在于半单环的模结构完全由其单模的分类和重数决定。

## 示例

### 示例 1：复数域上的矩阵代数

$M_n(\mathbb{C})$ 是单 Artin 环，对应 Artin-Wedderburn 分解中仅有一项。

### 示例 2：群代数的半单性

设 $G$ 为有限群，$k$ 为特征不整除 $|G|$ 的域。Maschke 定理断言群代数 $k[G]$ 半单，因此：

$$k[G] \cong \prod_{i} M_{n_i}(D_i)$$

这对应于 $G$ 的不可约表示的完全可约性。当 $k$ 代数闭时，所有 $D_i = k$。

### 示例 3：实数域上的四元数矩阵

$M_2(\mathbb{H})$（四元数上的 $2 \times 2$ 矩阵环）是单 Artin 环，其中 $\mathbb{H}$ 为 Hamilton 四元数除环。

## 应用

- **有限群表示论**：Maschke 定理后完全可约表示的结构
- **李代数**：半单李代数的包络代数与最高权理论
- **量子群与非交换几何**：$C^*$-代数与 von Neumann 代数的结构研究
- **同调代数**：半单环的整体维数为零（所有模皆投射）
- **数论**：中心单代数与 Brauer 群的分类

## 相关概念

- 半单环 (Semisimple Ring)：每个左模都是半单的环
- 单模 (Simple Module)：没有非平凡子模的模
- 除环 (Division Ring)：非零元皆可逆的环（未必交换）
- Schur 引理 (Schur's Lemma)：单模间同态要么为零要么为同构
- 矩阵环 (Matrix Ring)：除环上的全矩阵代数

## 参考

### 教材

- [Lam. A First Course in Noncommutative Rings. Springer, 2nd edition, 2001. Chapter 3]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 18.2]

### 历史文献

- [Wedderburn. On hypercomplex numbers. Proc. London Math. Soc., 1908]
- [Artin. Zur Theorie der hyperkomplexen Zahlen. Abh. Math. Sem. Univ. Hamburg, 1927]

### 在线资源

- [Mathlib4 文档 - WedderburnArtin][https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/SimpleModule/WedderburnArtin.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
