# 可分扩张性质 (Separable Extension Properties)

## Mathlib4 引用

```lean
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Polynomial

namespace SeparableExtension

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 可分扩张的传递性 -/
theorem separable_transitive [Algebra.IsSeparable K L] {E : Type*} [Field E]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] :
    Algebra.IsSeparable K E := by
  rw [Algebra.isSeparable_iff]
  intro x
  -- 利用可分元的性质
  have hL : IsSeparable K (minpoly K x) := by
    have h1 : IsSeparable L (minpoly L x) := Algebra.IsSeparable.isSeparable L x
    have h2 : IsSeparable K (minpoly K (minpoly L x)) :=
      Algebra.IsSeparable.isSeparable K (minpoly L x)
    sorry
  exact hL

/-- 可分扩张的原始元定理 -/
theorem primitive_element_theorem [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ α : L, L = K⟮α⟯ := by
  cases isEmpty_or_nonempty K with
  | inl hK =>
    -- 有限域情形
    sorry
  | inr hK =>
    -- 无限域情形
    rcases Algebra.IsSeparable.separable K L with hsep
    -- 构造原始元
    sorry

/-- 可分闭包的性质 -/
theorem separableClosure_is_separable :
    Algebra.IsSeparable K (separableClosure K L) := by
  rw [Algebra.isSeparable_iff]
  intro x
  rw [mem_separableClosure_iff]
  exact fun h => h

end SeparableExtension
```

## 数学背景

可分扩张的概念源于对多项式根的性质研究。在特征零的域上，所有代数扩张都是可分的；但在正特征域上，不可分扩张可能出现。Emil Artin和Otto Schreier在1920年代系统发展了可分扩张理论，为现代伽罗瓦理论奠定了基础。可分性是代数扩张中"好"的性质，保证了伽罗瓦对应的存在。

## 直观解释

可分扩张描述的是**代数元在其极小多项式中没有重根**的扩张。

想象多项式 $f(x)$ 的根就像多个球落在地面上。如果某些球完全重叠（重根），这种扩张就是不可分的。可分性要求所有球都分开——每个根都是"孤立"的。在特征零的域上，这自动成立；但在特征 $p$ 上，多项式如 $x^p - a$ 可能有 $p$ 重根，产生不可分扩张。

## 形式化表述

设 $K$ 是域，$f \in K[x]$ 是不可约多项式。

**可分性**：$f$ **可分**当 $f$ 在其分裂域中没有重根。

等价条件：$\gcd(f, f') = 1$（与形式导数互素）。

**可分扩张**：代数扩张 $L/K$ **可分**，如果所有 $\alpha \in L$ 的极小多项式都可分。

**关键性质**：
1. **传递性**：$K \subseteq L \subseteq E$ 可分 $\Rightarrow$ $E/K$ 可分
2. **本原元定理**：有限可分扩张是单扩张 $L = K(\alpha)$
3. **完美域**：所有代数扩张都可分的域

## 证明思路

1. **判别准则**：$f$ 可分 $\Leftrightarrow$ $\gcd(f, f') = 1$
2. **特征依赖性**：
   - 特征0：所有不可约多项式可分
   - 特征 $p$：$f(x) = g(x^{p^n})$ 对某个可分 $g$
3. **传递性证明**：利用极小多项式的整除性质
4. **本原元定理**：
   - 无限域：线性组合 $a\alpha + b\beta$ 的构造
   - 有限域：乘法子群的循环性

核心洞察是导数判据和特征对多项式结构的影响。

## 示例

### 示例 1：特征零域

$\mathbb{Q}(\sqrt{2})/\mathbb{Q}$ 是可分扩张。

$\sqrt{2}$ 的极小多项式 $x^2 - 2$ 的导数为 $2x$，$\gcd(x^2-2, 2x) = 1$。

### 示例 2：有限域

$\mathbb{F}_{p^n}/\mathbb{F}_p$ 是可分扩张。

所有有限域都是完美的，因为其Frobenius自同态 $x \mapsto x^p$ 是双射。

### 示例 3：不可分扩张（特征 $p$）

设 $K = \mathbb{F}_p(t)$（有理函数域），$L = K(\sqrt[p]{t})$。

$\alpha = \sqrt[p]{t}$ 满足 $x^p - t = 0$，但 $x^p - t = (x - \alpha)^p$ 有 $p$ 重根。

导数为 $px^{p-1} = 0$，故 $\gcd(x^p-t, 0) = x^p-t \neq 1$，不可分。

## 应用

- **伽罗瓦理论**：伽罗瓦扩张必须可分且正规
- **代数几何**：étale态射和光滑簇的定义
- **代数数论**：数域扩张的判别式计算
- **编码理论**：有限域上的循环码构造

## 相关概念

- [伽罗瓦扩张 (Galois Extension)](./galois-extension.md)：正规可分扩张
- [形式导数 (Formal Derivative)](./formal-derivative.md)：多项式的代数导数
- [本原元定理 (Primitive Element Theorem)](./primitive-element-theorem.md)：单生成元存在性
- [完美域 (Perfect Field)](./perfect-field.md)：所有扩张可分的域
- [不可分次数 (Inseparable Degree)](./inseparable-degree.md)：扩张的不可分程度

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 15]
- [Lang. Algebra. Springer, 3rd edition, 2002. Chapter V]

### 历史文献

- [Artin & Schreier. Eine Kennzeichnung der reell abgeschlossenen Körper. 1927]

### 在线资源

- [Mathlib4 文档 - Separable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Separable.html)
- [Keith Conrad - Separability](https://kconrad.math.uconn.edu/blurbs/galoistheory/separable.pdf)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
