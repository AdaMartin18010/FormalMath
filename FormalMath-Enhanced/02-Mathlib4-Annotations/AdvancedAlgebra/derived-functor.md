# 导出函子

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.DerivedFunctor

namespace HomologicalAlgebra

/-- 右导出函子的定义 -/
theorem right_derived_functor
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [Functor.IsLeftExact F]
    (n : ℕ) (X : C) [HasInjectiveResolution X] :
    ∃ (RF^n : D),
      RF^n = (F ⋙ HomologyFunctor D n).obj (InjectiveResolution.X X) := by
  -- 构造导出函子作为同调
  use (F.rightDerived n).obj X
  rfl

/-- 长正合列 -/
theorem long_exact_sequence
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [Functor.IsLeftExact F]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : ShortExact f g) :
    ExactSequence (F.derivedSequence f g h) := by
  -- 导出函子保持短正合列的长正合列
  apply derived_functor_exact

end HomologicalAlgebra
```

## 数学背景

导出函子理论由Cartan和Eilenberg在1956年的经典著作《Homological Algebra》中系统建立。这一理论提供了一种系统的方法来度量一个函子"不保持正合性"的程度。右导出函子度量左正合函子的缺陷，左导出函子度量右正合函子的缺陷。这是同调代数的核心工具，在代数几何、代数拓扑和表示论中有广泛应用。

## 直观解释

导出函子如同数学中的"误差分析"。考虑一个左正合函子 $F$，它只保持正合列的左半部分。右导出函子 $R^n F$ 量化了这种"信息损失"。$R^0 F = F$ 给出正确部分，$R^1 F$ 度量第一层偏差，$R^2 F$ 度量第二层，依此类推。这些"修正项"构成长正合列，使我们能够追踪信息在函子作用下的传播。

## 形式化表述

设 $F: \mathcal{A} \to \mathcal{B}$ 是Abel范畴间的左正合函子。

**右导出函子**：对 $n \geq 0$，$R^n F: \mathcal{A} \to \mathcal{B}$ 定义为
$$R^n F(X) = H^n(F(I^\bullet))$$
其中 $X \to I^\bullet$ 是内射分解。

**长正合列**：对短正合列 $0 \to X \to Y \to Z \to 0$，有自然的长正合列：
$$0 \to FX \to FY \to FZ \to R^1 FX \to R^1 FY \to R^1 FZ \to R^2 FX \to \cdots$$

## 证明思路

1. **选择分解**：为每个对象选择内射分解（需要足够的内射对象）
2. **函子作用**：将 $F$ 作用于分解的每个对象
3. **计算同调**：取所得复形的第 $n$ 阶同调
4. **验证独立性**：证明结果不依赖于分解的选择

## 示例

### 示例 1：Ext函子

**问题**：$\text{Ext}^n_\Lambda(M, -)$ 是 $Hom_\Lambda(M, -)$ 的右导出函子。

**解答**：

验证 $\text{Hom}_\Lambda(M, -)$ 是左正合的：给定正合列 $0 \to A \to B \to C$，有
$$0 \to \text{Hom}(M,A) \to \text{Hom}(M,B) \to \text{Hom}(M,C)$$
正合。因此 $\text{Ext}^n_\Lambda(M, N) = R^n \text{Hom}_\Lambda(M, -)(N)$。

### 示例 2：层上同调

**问题**：设 $(X, \mathcal{O}_X)$ 是拓扑空间，$\Gamma(X, -)$ 是整体截面函子。

**解答**：

$\Gamma(X, -)$ 是左正合的。其右导出函子 $H^n(X, \mathcal{F}) = R^n \Gamma(X, \mathcal{F})$ 称为层 $\mathcal{F}$ 的上同调。

例如，对常值层 $\underline{\mathbb{Z}}$，$H^n(X, \underline{\mathbb{Z}}) \cong H^n_{\text{sing}}(X, \mathbb{Z})$（奇异上同调）。

## 应用

- **代数几何**：层上同调理论（Serre、Grothendieck）
- **代数拓扑**：Ext和Tor的计算
- **群上同调**：$H^n(G, M)$ 的定义
- **复几何**：Dolbeault上同调
- **代数数论**：Galois上同调

## 相关概念

- [Ext函子](./ext-functor.md)：Hom的导出函子
- [Tor函子](./tor-functor.md)：张量积的导出函子
- [群上同调](./group-cohomology.md)：导出函子的特例
- [谱序列](./spectral-sequence.md)：计算导出函子的工具
- [Yoneda Ext](./yoneda-ext.md)：Ext的公理化描述

## 参考

### 教材

- Weibel, C.A. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 2
- Gelfand, S.I. & Manin, Y.I. Methods of Homological Algebra. Springer, 2003. Chapter 3

### 论文

- Cartan, H. & Eilenberg, S. Homological Algebra. Princeton University Press, 1956.
- Grothendieck, A. Sur quelques points d'algèbre homologique. Tôhoku Math. J., 9: 119-221, 1957.

### 在线资源

- [Stacks Project - Derived Functors](https://stacks.math.columbia.edu/tag/010N)
- [nLab - Derived Functor](https://ncatlab.org/nlab/show/derived+functor)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
