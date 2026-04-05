---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 诺特正规化引理 (Noether Normalization Lemma)
---
# 诺特正规化引理 (Noether Normalization Lemma)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Localization.Basic

namespace NoetherNormalization

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- 诺特正规化引理：有限生成代数中存在代数无关元 -/
theorem noetherNormalization [hfg : Algebra.FiniteType k A] :
    ∃ (n : ℕ) (y : Fin n → A),
      Algebra.Independent k y ∧
      Algebra.IsIntegral (MvPolynomial (Fin n) k) A := by
  -- 对生成元个数进行归纳
  induction' hfg using Algebra.FiniteType.induction_subsingleton with n A hA
  · -- 平凡情形
    use 0, fun _ => 0
    constructor
    · -- 空集代数无关
      simp [Algebra.Independent]
    · -- 整性
      sorry
  · -- 归纳步骤
    sorry

end NoetherNormalization
```

## 数学背景

诺特正规化引理由Emmy Noether在1926年证明（尽管Hilbert和Lasker之前已有特殊情况）。这是交换代数中最重要的结构定理之一，它表明有限生成代数在适当坐标变换后，可表示为多项式环上的整扩张。该引理为研究仿射代数的维数理论奠定了基础。

## 直观解释

诺特正规化引理告诉我们：**任何有限生成的代数都包含一个多项式子代数，使得原代数在这个子代数上是整的**。

想象一个曲面 $z^2 = x^3 + y^2$。诺特正规化说存在"好"的坐标，使得曲面在某种意义下是这些坐标的"有限覆盖"。更一般地，它说明仿射代数簇在适当投影下可表示为仿射空间的有限覆盖。

## 形式化表述

设 $k$ 是域，$A$ 是有限生成的 $k$-代数。

**诺特正规化引理**：存在代数无关元 $y_1, \ldots, y_n \in A$ 使得：
1. $k[y_1, \ldots, y_n] \subseteq A$ 是多项式子代数
2. $A$ 在 $k[y_1, \ldots, y_n]$ 上是整扩张

等价表述：存在满射 $k[X_1, \ldots, X_n] \hookrightarrow A$ 使 $A$ 成为有限生成模。

**维数推论**：$\dim(A) = n$（Krull维数）。

## 证明思路

1. **归纳基础**：单生成元情形显然成立
2. **非代数情形**：若生成元代数无关，则已得到多项式子代数
3. **关键构造**：若生成元代数相关，找到代数关系并做变量替换
4. **标准化形式**：通过坐标变换 $x_i \mapsto x_i + x_n^{k_i}$ 得到首一多项式
5. **归纳完成**：由首一性得到整性，对剩余变量归纳

核心洞察是巧妙的坐标变换可消除交叉项，得到首一关系。

## 示例

### 示例 1：超曲面

设 $A = k[x,y]/(xy-1)$（双曲线）。

取 $y_1 = x + y$，则 $y_1$ 在 $A$ 上代数无关（$A$ 在其上整）。

验证：$xy = 1$ 给出 $t^2 - y_1 t + 1 = 0$，其中 $t = x$。

### 示例 2：椭圆曲线

设 $A = k[x,y]/(y^2 - x^3 + x)$。

取 $y_1 = x$，则 $y$ 在 $k[x]$ 上满足整方程 $y^2 = x^3 - x$。

### 示例 3：二次锥面

设 $A = k[x,y,z]/(xy - z^2)$。

取 $y_1 = x + y, y_2 = x - y$ 不能立即正规化。

改用 $y_1 = x, y_2 = y + z$：
$(y_2 - z)^2 = x y$ 给出 $z$ 的二次整方程。

## 应用

- **维数理论**：定义环的Krull维数
- **希尔伯特零点定理**：证明的关键步骤
- **有限性结果**：整扩张的有限性传递
- **参数化方法**：代数簇的投影约化

## 相关概念

- 整扩张 (Integral Extension)：满足首一多项式的扩张
- Krull维数 (Krull Dimension)：素理想链的最大长度
- 代数无关 (Algebraic Independence)：超越基的概念
- 希尔伯特零点定理 (Nullstellensatz)：代数几何基本定理
- 仿射代数 (Affine Algebra)：有限生成代数

## 参考

### 教材

- [Atiyah & Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 5]
- [Eisenbud. Commutative Algebra. Springer, 1995. Section 8.2]

### 历史文献

- [Noether. Der Endlichkeitssatz der Invarianten endlicher linearer Gruppen der Charakteristik p. 1926]

### 在线资源

- [Mathlib4 文档 - Algebra Finiteness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness.html)[需更新]
- [Stacks Project - 00OW](https://stacks.math.columbia.edu/tag/00OW)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
