---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 伴随函子
---
# 伴随函子

## Mathlib4 引用

```lean
import Mathlib.CategoryTheory.Adjunction.Basic

namespace CategoryTheory

/-- 伴随函子的定义 -/
structure Adjunction {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) where
  unit : 𝟭 C ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭 D
  left_triangle :
    (whiskerRight unit F) ≫ (whiskerLeft F counit) = 𝟙 (F ⋙ 𝟭 C)
  right_triangle :
    (whiskerLeft G unit) ≫ (whiskerRight counit G) = 𝟙 (𝟭 D ⋙ G)

/-- Hom集的自然同构定义 -/
theorem adjunction_hom_equiv
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} :
    F ⊣ G ↔ ∀ (X : C) (Y : D),
      (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) := by
  -- 两种定义的等价性
  constructor
  · intro adj
    exact fun X Y => adj.homEquiv X Y
  · intro he
    exact Adjunction.mkOfHomEquiv {
      homEquiv := he
      .. /- 验证自然性 -/
    }

end CategoryTheory
```

## 数学背景

伴随函子由Daniel Kan在1958年系统引入，是范畴论中最核心且广泛应用的概念之一。伴随关系 "$F \dashv G$" 表达了一种"最优近似"：$F$ 是 $G$ 的最佳左近似，$G$ 是 $F$ 的最佳右近似。伴随无处不在：自由构造与遗忘函子、张量积与Hom、扩张与限制表示、像与原像层等。伴随函子统一了数学中大量看似不同的构造。

## 直观解释

伴随函子描述了一对函子之间的"和谐关系"。想象 $F$ 和 $G$ 是连接两个世界的门户——$F$ 从世界 $C$ 到世界 $D$，$G$ 则返回。伴随关系意味着：通过 $F$ 再到 $D$ 的任何旅程，都可以最优地对应于直接从 $C$ 出发再经 $G$ 到达的旅程。这种"最优性"由单位（unit）和余单位（counit）精确刻画，它们如同转换说明书，告诉我们在每个世界如何往返。

## 形式化表述

设 $F: \mathcal{C} \to \mathcal{D}$，$G: \mathcal{D} \to \mathcal{C}$ 是函子。

**伴随定义**：$F$ 是 $G$ 的**左伴随**（$F \dashv G$），若存在自然同构：
$$\text{Hom}_{\mathcal{D}}(F(X), Y) \cong \text{Hom}_{\mathcal{C}}(X, G(Y))$$

**单位-余单位定义**：

- **单位** $\eta: 1_{\mathcal{C}} \Rightarrow GF$（$X$ 到 $GF(X)$ 的"最优"映射）
- **余单位** $\varepsilon: FG \Rightarrow 1_{mathcal{D}}$（$FG(Y)$ 到 $Y$ 的"最优"映射）

满足三角恒等式。

## 证明思路

1. **Hom集同构定义**：建立 $\text{Hom}(FX, Y) \cong \text{Hom}(X, GY)$ 的自然同构
2. **单位构造**：$\eta_X = \phi(1_{FX})$，其中 $\phi$ 是同构
3. **余单位构造**：$\varepsilon_Y = \phi^{-1}(1_{GY})$
4. **验证三角恒等式**：确保两种定义等价

## 示例

### 示例 1：自由群

**问题**：证明遗忘函子 $U: \mathbf{Grp} \to \mathbf{Set}$ 有左伴随。

**解答**：

自由群函子 $F: \mathbf{Set} \to \mathbf{Grp}$ 是 $U$ 的左伴随：
$$\text{Hom}_{\mathbf{Grp}}(F(S), G) \cong \text{Hom}_{\mathbf{Set}}(S, U(G))$$

即从 $S$ 到 $G$ 的映射唯一扩张为群同态 $F(S) \to G$。

### 示例 2：张量-Hom伴随

**问题**：设 $R$ 是交换环，$M$ 是 $R$-模，证明 $-\otimes_R M$ 和 $\text{Hom}_R(M, -)$ 伴随。

**解答**：

对 $R$-模 $N, P$：
$$\text{Hom}_R(N \otimes_R M, P) \cong \text{Hom}_R(N, \text{Hom}_R(M, P))$$

这是交换代数中的基本伴随关系。

## 应用

- **泛性质**：自由对象、极限、余极限的伴随描述
- **代数几何**：像函子与原像函子的伴随
- **拓扑学**：悬垂与回路空间的伴随
- **逻辑**：量词作为伴随（Lawvere）
- **计算机科学**：单子与余单子的构造

## 相关概念

- [Yoneda引理](./yoneda-lemma.md)：伴随的理论基础
- [可表示函子](./representable-functor.md)：伴随的特例
- [单子](./monad.md)：伴随诱导的代数结构
- [极限](./limit.md)：对角函子的右伴随
- [余极限](./colimit.md)：对角函子的左伴随

## 参考

### 教材

- Mac Lane, S. Categories for the Working Mathematician. Springer, 1998. Chapter 4
- Riehl, E. Category Theory in Context. Dover, 2016. Chapter 4

### 论文

- Kan, D.M. Adjoint functors. Trans. Amer. Math. Soc., 87: 294-329, 1958.
- Lawvere, F.W. Adjointness in foundations. Dialectica, 23: 281-296, 1969.

### 在线资源

- [Adjoint Functor Wikipedia](https://en.wikipedia.org/wiki/Adjoint_functors)
- [nLab - Adjunction](https://ncatlab.org/nlab/show/adjoint+functor)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
