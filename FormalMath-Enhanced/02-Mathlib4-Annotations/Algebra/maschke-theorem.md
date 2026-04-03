# Maschke定理 (Maschke's Theorem)

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace MaschkeTheorem

variable {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
variable [IsScalarTower k (MonoidAlgebra k G) V]

/-- Maschke定理：特征不整除|G|时，表示完全可约 -/
theorem maschke_theorem (hk : (Fintype.card G : k) ≠ 0)
    [Module.Finite k V] :
    IsSemisimpleModule (MonoidAlgebra k G) V := by
  rw [isSemisimpleModule_iff_supplementedLattice]
  intro W hW
  -- 构造G-等变投影
  let π : V →ₗ[k] W := LinearMap.id.codRestrict W (fun v => by simp)
  let πG : V →ₗ[MonoidAlgebra k G] W := ∑ g : G, g • π
  -- 平均化构造
  have havg : (Fintype.card G : k)⁻¹ • πG = LinearMap.id.codRestrict W _ := by
    sorry
  -- 证明补子模存在
  sorry

/-- Maschke定理（子模版本）-/
theorem maschke_theorem_submodule (hk : (Fintype.card G : k) ≠ 0)
    {W : Submodule (MonoidAlgebra k G) V} [Module.Finite k V] :
    ∃ W' : Submodule (MonoidAlgebra k G) V, IsCompl W W' := by
  exact (maschke_theorem hk).1 W

end MaschkeTheorem
```

## 数学背景

Maschke定理由Heinrich Maschke在1899年证明，是有限群表示论的基本定理。它表明在"好"的特征条件下，有限群的每个表示都是完全可约的——即可以分解为不可约表示的直和。这一定理极大地简化了对有限群表示的研究，因为理解所有表示约化为理解不可约表示，而前者通常更容易处理。

## 直观解释

Maschke定理告诉我们：**在特征不整除群阶的条件下，有限群表示没有"病态"的不可约子结构**。

想象一个群作用在向量空间上。一般来说，可能存在"扭曲"的子表示，使得商表示无法分解回直和。Maschke定理说，当域的特征与群的阶互素时，这种扭曲不会发生——任何子表示都有不变的补空间。这就像说，在"好"条件下，我们可以干净利落地将整个空间切成不变的碎片。

## 形式化表述

设 $G$ 是有限群，$k$ 是域，$|G|$ 在 $k$ 中非零（即 $\text{char } k \nmid |G|$）。

**Maschke定理**：群代数 $k[G]$ 是半单的。等价表述：
1. 每个 $k[G]$-模是完全可约的（半单模）
2. 每个子模都有补子模
3. $k[G]$ 同构于矩阵代数的直积（Wedderburn-Artin定理）

**关键构造**：对任意投影 $\pi: V \to W$，通过"平均化"构造G-等变投影：
$$\pi_G(v) = \frac{1}{|G|} \sum_{g \in G} g \cdot \pi(g^{-1} \cdot v)$$

## 证明思路

1. **设置**：设 $W \subseteq V$ 是 $k[G]$-子模，需找补子模
2. **投影存在**：作为 $k$-向量空间，存在投影 $\pi: V \to W$
3. **平均化**：构造 $\pi_G(v) = \frac{1}{|G|} \sum_{g} g \pi(g^{-1}v)$
4. **G-等变性**：验证 $\pi_G(hv) = h\pi_G(v)$（通过变量替换）
5. **补子模**：$\ker \pi_G$ 是 $W$ 的 $G$-不变补

核心洞察是平均化过程保持了投影性质同时获得等变性。

## 示例

### 示例 1：$S_3$ 的表示

$|S_3| = 6$，在特征不整除6的域上，$k[S_3]$ 半单。

不可约表示：
- 平凡表示（1维）
- 符号表示（1维）
- 标准表示（2维）

维数关系：$6 = 1^2 + 1^2 + 2^2$。

### 示例 2：特征整除群阶的情形

设 $G = \mathbb{Z}/p\mathbb{Z}$，$k = \mathbb{F}_p$。

考虑 $V = k^2$，$G$ 通过平移作用：$g \cdot (x, y) = (x + g, y)$。

子模 $W = \{(0, y)\}$ 没有 $G$-不变补，$V$ 不是半单的。

### 示例 3：正则表示

$k[G]$ 作为左 $k[G]$-模是正则表示。

Maschke定理说：$k[G] \cong \bigoplus_i (S_i)^{\dim S_i}$，其中 $S_i$ 是不可约表示。

## 应用

- **表示分类**：约化问题到不可约表示
- **特征标理论**：正交关系的建立
- **傅里叶分析**：有限群上的调和分析
- **量子力学**：对称性导致的能级简并
- **编码理论**：群码的构造

## 相关概念

- [半单代数 (Semisimple Algebra)](./semisimple-algebra.md)：半单模上的代数
- [完全可约表示 (Completely Reducible Representation)](./completely-reducible.md)：直和分解
- [群代数 (Group Algebra)](./group-algebra.md)：群的代数化
- [Wedderburn-Artin定理 (Wedderburn-Artin Theorem)](./wedderburn-artin.md)：半单代数结构
- [特征标表 (Character Table)](./character-table.md)：表示的数值不变量

## 参考

### 教材

- [Serre. Linear Representations of Finite Groups. Springer, 1977. Chapter 1]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 18.1]

### 历史文献

- [Maschke. Über den arithmetischen Charakter der Coefficienten der Substitutionen endlicher linearer Substitutionsgruppen. 1899]

### 在线资源

- [Mathlib4 文档 - Maschke](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Maschke.html)
- [Groupprops - Maschke's theorem](https://groupprops.subwiki.org/wiki/Maschke%27s_theorem_for_finite_groups)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
