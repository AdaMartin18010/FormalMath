# Ext函子

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.Ext

namespace HomologicalAlgebra

/-- Ext函子的定义 -/
theorem ext_functor
    {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (n : ℕ) :
    Ext R n M N ≃ AddCommGroup.of
      (ModuleCat.of R M ⟶ ModuleCat.of R N)⟦n⟧ := by
  -- Ext是Hom的导出函子
  apply ext_iso_shifted_hom

/-- Ext的长正合列 -/
theorem ext_long_exact
    {R : Type*} [Ring R]
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : N ⟶ P) (g : P ⟶ Q)
    (h : ShortExact f g) (n : ℕ) :
    ExactSequence (
      Ext R n M N ⟶ Ext R n M P ⟶ Ext R n M Q ⟶
      Ext R (n+1) M N ⟶ Ext R (n+1) M P) := by
  -- Hom(_, M)的右导出性质
  apply ext_exact_sequence

end HomologicalAlgebra
```

## 数学背景

Ext函子是同调代数中最基本的导出函子之一，首次系统出现在Cartan和Eilenberg 1956年的著作中。Ext得名于"extension"（扩张），因为它分类了模的扩张。$\text{Ext}^1$ 分类短正合列的等价类，而高阶Ext函子则与更复杂的同调信息相关。Ext函子在代数拓扑、代数几何和表示论中无处不在。

## 直观解释

Ext函子度量了两个模之间"关系"的复杂性。$\text{Ext}^0_R(M, N) = \text{Hom}_R(M, N)$ 是直接可定义的映射；$\text{Ext}^1_R(M, N)$ 度量从 $N$ "扩展" 到 $M$ 的不同方式（短正合列 $0 \to N \to E \to M \to 0$ 的分类）；更高阶的Ext则度量迭代扩张的复杂性。这种层次化的信息使Ext成为研究模结构的强大工具。

## 形式化表述

设 $R$ 是环，$M, N$ 是左 $R$-模。

**定义**：$\text{Ext}^n_R(M, N) = R^n \text{Hom}_R(M, -)(N)$

等价地，使用 $M$ 的投射分解 $P_\bullet \to M$：
$$\text{Ext}^n_R(M, N) = H^n(\text{Hom}_R(P_\bullet, N))$$

**基本性质**：

- $\text{Ext}^0_R(M, N) = \text{Hom}_R(M, N)$
- 若 $M$ 投射，则 $\text{Ext}^n_R(M, N) = 0$（$n \geq 1$）
- 若 $N$ 内射，则 $\text{Ext}^n_R(M, N) = 0$（$n \geq 1$）

## 证明思路

1. **选择分解**：为 $N$ 选择内射分解（或 $M$ 选择投射分解）
2. **应用Hom**：计算 $\text{Hom}_R(M, I^\bullet)$ 的同调
3. **平衡性**：证明两种定义方式给出同构结果
4. **长正合列**：从导出函子的一般理论继承

## 示例

### 示例 1：Abel群的Ext

**问题**：计算 $\text{Ext}^1_\mathbb{Z}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z})$。

**解答**：

使用 $\mathbb{Z}/m\mathbb{Z}$ 的投射分解：
$$0 \to \mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \to 0$$

应用 $\text{Hom}(-, \mathbb{Z}/n\mathbb{Z})$ 并计算同调：
$$\text{Ext}^1_\mathbb{Z}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$$

### 示例 2：扩张的分类

**问题**：描述 $\text{Ext}^1_R(M, N)$ 与短正合列的关系。

**解答**：

存在自然双射：
$$\text{Ext}^1_R(M, N) \cong \{\text{短正合列 } 0 \to N \to E \to M \to 0\} / \sim$$

其中等价关系 $\sim$ 由交换图给出。零元素对应分裂扩张 $E = M \oplus N$。

## 应用

- **Universal Coefficient Theorem**：同调与上同调的关系
- **Künneth公式**：积空间的同调计算
- **模的扩张构造**：用Ext构造新的模
- **Obstruction理论**：几何结构的障碍类
- **导出范畴**：三角范畴的Hom空间

## 相关概念

- [Tor函子](./tor-functor.md)：张量积的导出函子
- [导出函子](./derived-functor.md)：Ext的一般框架
- [Yoneda Ext](./yoneda-ext.md)：Ext的公理化定义
- [投射分解](./projective-resolution.md)：计算Ext的方法
- [内射分解](./injective-resolution.md)：另一种计算方法

## 参考

### 教材

- Hilton, P.J. & Stammbach, U. A Course in Homological Algebra. Springer, 1997. Chapter 3
- Rotman, J.J. An Introduction to Homological Algebra. Springer, 2009. Chapter 7

### 论文

- Yoneda, N. On Ext and exact sequences. J. Fac. Sci. Univ. Tokyo Sect. I, 8: 507-576, 1960.

### 在线资源

- [Ext Functor Wikipedia](https://en.wikipedia.org/wiki/Ext_functor)
- [Stacks Project - Ext](https://stacks.math.columbia.edu/tag/00HR)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
