# 可表示函子

## Mathlib4 引用

```lean
import Mathlib.CategoryTheory.Representable

namespace CategoryTheory

/-- 可表示函子的定义 -/
theorem representable_functor 
    {C : Type*} [Category C] 
    {F : Cᵒᵖ ⥤ Type*} :
    F.IsRepresentable ↔ ∃ (X : C), 
      yoneda.obj X ≅ F := by
  -- 函子可表示当且仅当与Hom函子同构
  rfl

/-- 表示对象的唯一性 -/
theorem representing_object_unique 
    {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*}
    {X Y : C} (hX : yoneda.obj X ≅ F) 
    (hY : yoneda.obj Y ≅ F) :
    X ≅ Y := by
  -- 由Yoneda嵌入的完全忠实性
  apply yoneda.mapIso
  exact hX.symm ≪≫ hY

end CategoryTheory
```

## 数学背景

可表示函子是范畴论中通过Hom函子"表示"其他函子的概念。这一思想源于Yoneda的工作，由Grothendieck在代数几何中系统应用。可表示函子将抽象构造具体化为某个对象——这一对象"表示"了该函子。模空间理论、分类空间和许多代数构造都可以用可表示性描述。可表示函子是连接具体构造与抽象泛性质的桥梁。

## 直观解释

可表示函子如同数学中的"分类器"。想象一个函子 $F$ 对每个对象 $X$ 给出某种"结构"的集合（如向量丛、群作用等）。如果 $F$ 可表示，意味着存在一个"万有对象" $U$，使得 $X$ 上的任何结构都唯一对应于从 $X$ 到 $U$ 的映射。这个 $U$ 就像一个"蓝图"或"原型"——所有其他对象上的结构都是它的"拷贝"。

## 形式化表述

设 $\mathcal{C}$ 是范畴，$F: \mathcal{C}^{op} \to \mathbf{Set}$ 是（反变）函子。

**定义**：$F$ 是**可表示的**，若存在对象 $X \in \mathcal{C}$（**表示对象**）和自然同构：
$$\eta: \text{Hom}(-, X) \cong F$$

**泛元素**：等价于存在**泛元素** $u \in F(X)$，使得对任意 $y \in F(Y)$，存在唯一 $f: Y \to X$ 使 $F(f)(u) = y$。

**唯一性**：表示对象在同构意义下唯一。

## 证明思路

1. **Yoneda引理**：应用Yoneda引理建立同构
2. **泛元素存在性**：从自然同构提取泛元素
3. **唯一性证明**：利用Yoneda嵌入的完全忠实性
4. **自然性验证**：确保同构关于对象的函子性

## 示例

### 示例 1：分类空间

**问题**：描述主 $G$-丛的分类函子。

**解答**：

函子 $B: \mathbf{Top}^{op} \to \mathbf{Set}$，$B(X) = \{\text{主$G$-丛在$X$上}\}$

是可表示的。表示对象是分类空间 $BG$，满足：
$$\text{Hom}(X, BG) \cong \{\text{主$G$-丛在$X$上}\}$$

### 示例 2：张量代数

**问题**：证明自由结合代数函子可表示。

**解答**：

遗忘函子 $U: \mathbf{Alg}_k \to \mathbf{Vect}_k$ 有左伴随 $T$，即张量代数。

对向量空间 $V$：
$$\text{Hom}_{\mathbf{Alg}}(T(V), A) \cong \text{Hom}_{\mathbf{Vect}}(V, U(A))$$

因此张量代数函子（作为反变函子）可表示。

## 应用

- **代数几何**：模空间作为可表示函子
- **代数拓扑**：分类空间与示性类
- **泛代数**：自由构造的表示
- **逻辑**：命题作为类型
- **计算机科学**：参数多态的类型论

## 相关概念

- [Yoneda引理](./yoneda-lemma.md)：可表示性的理论基础
- [伴随函子](./adjoint-functor.md)：可表示性的推广
- [泛性质](./universal-property.md)：表示对象的刻画
- [模空间](./moduli-space.md)：几何中的可表示函子
- [分类空间](./classifying-space.md)：拓扑中的表示对象

## 参考

### 教材

- Mac Lane, S. Categories for the Working Mathematician. Springer, 1998. Chapter 3
- Riehl, E. Category Theory in Context. Dover, 2016. Chapter 2

### 论文

- Grothendieck, A. Technique de descente et théorèmes d'existence en géométrie algébrique. Séminaire Bourbaki, 190, 1959-1960.

### 在线资源

- [Representable Functor Wikipedia](https://en.wikipedia.org/wiki/Representable_functor)
- [nLab - Representable Functor](https://ncatlab.org/nlab/show/representable+functor)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
