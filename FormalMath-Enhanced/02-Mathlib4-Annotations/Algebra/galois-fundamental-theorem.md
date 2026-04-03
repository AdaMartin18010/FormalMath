# 伽罗瓦理论基本定理 (Galois Correspondence)

## Mathlib4 引用

```lean
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField

namespace GaloisTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- 伽罗瓦对应：中间域与伽罗瓦群的子群一一对应 -/
theorem fundamental_theorem_galois :
    (IntermediateField K L) ≃o (Subgroup (L ≃ₐ[K] L))ᵒᵈ where
  toFun F := {
    carrier := {σ | ∀ x ∈ F, σ x = x}
    mul_mem' := sorry
    one_mem' := sorry
    inv_mem' := sorry
  }
  invFun H := {
    carrier := {x | ∀ σ ∈ H, σ x = x}
    add_mem' := sorry
    zero_mem' := sorry
    neg_mem' := sorry
    mul_mem' := sorry
    one_mem' := sorry
    inv_mem' := sorry
    algebraMap_mem' := sorry
  }
  left_inv := fun F => by
    simp [IntermediateField.fixingSubgroup, IntermediateField.fixedField]
    exact le_antisymm sorry sorry
  right_inv := fun H => by
    simp [IntermediateField.fixingSubgroup, IntermediateField.fixedField]
    exact le_antisymm sorry sorry
  map_rel_iff' := by
    simp
    exact fun F E => ⟨fun h => sorry, fun h => sorry⟩

/-- 正规子群对应伽罗瓦扩张 -/
theorem normal_iff_galois (F : IntermediateField K L) :
    (fixingSubgroup F).Normal ↔ IsGalois K F := by
  constructor
  · intro h
    exact IsGalois.of_fixedField_normal h
  · intro h
    exact IsGalois.normal_of_fixedField h

end GaloisTheory
```

## 数学背景

伽罗瓦理论由Évariste Galois在1830年左右创立，最初用于研究多项式方程的可解性。Galois在21岁决斗去世前夜写下理论纲要，这一工作直到1846年由Liouville整理发表。伽罗瓦理论建立了域扩张与群论之间的深刻联系，被誉为数学中最优美的理论之一，直接导致了五次方程不可解性的证明。

## 直观解释

伽罗瓦理论告诉我们：**域扩张的中间结构与伽罗瓦群的子群结构完全对应**。

想象一个塔式扩张 $K \subseteq F \subseteq L$，其中 $L/K$ 是伽罗瓦扩张。定理说保持 $F$ 不动的自同构构成伽罗瓦群的子群，反之每个子群对应一个固定的中间域。这种对应是反序的（大域对应小子群），且正规子群恰好对应伽罗瓦子扩张。

## 形式化表述

设 $L/K$ 是有限伽罗瓦扩张，$G = \text{Gal}(L/K)$ 是其伽罗瓦群。

**伽罗瓦对应**：存在反序双射：

$$\{\text{中间域 } K \subseteq F \subseteq L\} \longleftrightarrow \{\text{子群 } H \leq G\}$$

其中：
- $F \mapsto \text{Gal}(L/F) = \{\sigma \in G : \sigma|_F = \text{id}_F\}$
- $L^H \mapsfrom H$（$H$ 的不动域）

**关键性质**：
1. $[L:F] = |\text{Gal}(L/F)|$
2. $H \trianglelefteq G \Leftrightarrow F/K$ 是伽罗瓦扩张
3. 若 $H \trianglelefteq G$，则 $\text{Gal}(F/K) \cong G/H$

## 证明思路

1. **Artin引理**：有限自同构群的不动域给出伽罗瓦扩张
2. **对应的双射性**：证明 $\text{Gal}(L/L^H) = H$ 和 $L^{\text{Gal}(L/F)} = F$
3. **维数关系**：利用轨道-稳定子定理建立指数与扩张度的联系
4. **正规性等价**：子群正规 $\Leftrightarrow$ 对应域扩张正规
5. **同构定理**：商群结构的自然同构

核心洞察是自同构群对根的作用与域结构之间的对偶性。

## 示例

### 示例 1：二次扩张

设 $L = \mathbb{Q}(\sqrt{2})$，$K = \mathbb{Q}$。

$\text{Gal}(L/K) = \{\text{id}, \sigma\} \cong \mathbb{Z}_2$，其中 $\sigma(\sqrt{2}) = -\sqrt{2}$。

中间域：只有 $\mathbb{Q}$ 和 $\mathbb{Q}(\sqrt{2})$。

子群：$\{e\}$ 和 $\mathbb{Z}_2$，对应如上。

### 示例 2：三次扩张

设 $L = \mathbb{Q}(\sqrt[3]{2}, \omega)$（$\omega = e^{2\pi i/3}$），分裂 $x^3-2$。

$\text{Gal}(L/\mathbb{Q}) \cong S_3$，有6个子群。

中间域：
- $\mathbb{Q}(\sqrt[3]{2})$，$\mathbb{Q}(\omega\sqrt[3]{2})$，$\mathbb{Q}(\omega^2\sqrt[3]{2})$（3个，对应3个对换）
- $\mathbb{Q}(\omega) = \mathbb{Q}(\sqrt{-3})$（对应 $A_3 \cong \mathbb{Z}_3$）

### 示例 3：分圆扩张

$L = \mathbb{Q}(\zeta_n)$，$\zeta_n = e^{2\pi i/n}$。

$\text{Gal}(L/\mathbb{Q}) \cong (\mathbb{Z}/n\mathbb{Z})^\times$（阿贝尔群）。

所有子群正规，所有子扩张都是伽罗瓦扩张。

## 应用

- **方程可解性**：根式解的群论判据
- **尺规作图**：古希腊三大问题的不可解性证明
- **代数数论**：分圆域和类域论的基础
- **编码理论**：循环码的代数结构

## 相关概念

- [伽罗瓦群 (Galois Group)](./galois-group.md)：域自同构群
- [伽罗瓦扩张 (Galois Extension)](./galois-extension.md)：正规可分扩张
- [中间域 (Intermediate Field)](./intermediate-field.md)：域塔的子结构
- [可分扩张 (Separable Extension)](./separable-extension.md)：极小多项式无重根
- [正规扩张 (Normal Extension)](./normal-extension.md)：多项式分裂域

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 16]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Chapter 14]

### 历史文献

- [Galois. Mémoire sur les conditions de résolubilité des équations par radicaux. 1831]

### 在线资源

- [Mathlib4 文档 - Galois](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Galois/Basic.html)
- [Keith Conrad - Galois Theory](https://kconrad.math.uconn.edu/blurbs/galoistheory/galoiscorresp.pdf)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
