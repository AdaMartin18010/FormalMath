---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 模空间基础
---
# 模空间基础

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.ModuliSpace

namespace AlgebraicGeometry

/-- 模函子 -/
theorem moduli_functor
    {S : Scheme} {F : Schemeᵒᵖ ⥤ Type*} :
    IsModuliFunctor F ↔
      RepresentableBy F M ∧
      ∀ (k : Field),
        F(Spec k) ≅ {几何对象/k}/≅ := by
  -- 模函子在几何对象同构类上可表示
  sorry

/-- 精细模空间 -/
theorem fine_moduli_space
    {S : Scheme} {F : Schemeᵒᵖ ⥤ Groupoid}
    {M : Scheme} (hM : FineModuliSpace F M) :
    ∃ (u : UniversalFamily F M),
      ∀ (T : Scheme) (x : F T),
        ∃! (f : T → M),
          x ≅ f^* u := by
  -- 精细模空间存在万有族
  sorry

end AlgebraicGeometry
```

## 数学背景

模空间理论是代数几何的核心领域，研究几何对象的分类空间。从椭圆曲线的模空间 $\mathcal{M}_{1,1}$ 到曲线的模空间 $\mathcal{M}_g$，再到向量丛的模空间，这一理论连接了代数几何、数论、数学物理和弦理论。Mumford在1960年代发展的几何不变量理论（GIT）为构造模空间提供了系统方法。模空间本身具有丰富的几何结构，往往也是有趣的几何对象。

## 直观解释

模空间如同一个"分类仓库"，为每类几何对象指定一个"地址"。想象所有椭圆曲线——它们可以用一个复参数（j-不变量）来标记。所有可能的椭圆曲线就构成了模空间，每个点对应一条椭圆曲线的同构类。更复杂的模空间（如曲线的模空间 $\mathcal{M}_g$）是高维的，甚至不是概形而是叠（stack）。模空间不仅记录"有哪些对象"，还记录这些对象如何"变化"（形变理论）。

## 形式化表述

设 $\mathcal{M}$ 是分类某类几何对象（如曲线、向量丛）的模空间。

**粗糙模空间**：概形 $M$ 配备双射
$$\{\text{几何对象在 } k \text{ 上}\}/\cong \xrightarrow{\sim} M(k)$$
满足万有性质。

**精细模空间**：存在万有族 $\mathcal{U} \to M$ 使得对任意族 $\mathcal{X} \to T$，存在唯一 $f: T \to M$ 使得 $\mathcal{X} \cong f^*\mathcal{U}$。

**模叠**（DM stack）：当对象有非平凡自同构时，需要叠来构造模空间。

## 证明思路

1. **模函子**：定义分类几何对象的函子
2. **可表示性**：证明函子可表示（或使用叠）
3. **GIT构造**：用几何不变量理论构造商
4. **稳定性条件**：选择适当稳定性以确保好性质
5. **紧化**：研究模空间的边界和紧化

## 示例

### 示例 1：椭圆曲线的模空间

**问题**：描述椭圆曲线的（粗）模空间。

**解答**：

$\mathcal{M}_{1,1} = \mathbb{A}^1_j$（j-直线）。

每个椭圆曲线 $E$ 有j-不变量 $j(E) \in \mathbb{C}$。

$j(E) = j(E')$ 当且仅当 $E \cong E'$（在代数闭域上）。

这是粗糙模空间，因为存在自同构（$\text{Aut}(E) \supseteq \mathbb{Z}/2$）。

### 示例 2：射影直线的映射空间

**问题**：描述 $\text{Mor}(\mathbb{P}^1, \mathbb{P}^n)$ 的模空间。

**解答**：

d次映射由齐次坐标中的 $n+1$ 个d次形式给出。

模空间是 $((n+1)(d+1)-1)$ 维射影空间的一个开子集。

Kontsevich的稳定映射紧化给出了 $
      \overline{\mathcal{M}}_{0,0}(\mathbb{P}^n, d)$。

## 应用

- **弦理论**：Calabi-Yau模空间和镜像对称
- **枚举几何**：Gromov-Witten不变量
- **数论**：Shimura簇和Langlands纲领
- **数学物理**：规范理论模空间
- **代数拓扑**：曲线的同调理论

## 相关概念

- [几何不变量理论](./geometric-invariant-theory.md)：模空间构造方法
- [代数叠](./algebraic-stack.md)：带自同构的模空间
- [形变理论](./deformation-theory.md)：模空间的切空间
- [稳定曲线](./stable-curve.md)：模空间紧化
- [相交理论](./intersection-theory.md)：模空间上的计算

## 参考

### 教材

- Harris, J. & Morrison, I. Moduli of Curves. Springer, 1998.
- Mukai, S. An Introduction to Invariants and Moduli. Cambridge, 2003.

### 论文

- Mumford, D. Geometric Invariant Theory. Springer, 1965.
- Deligne, P. & Mumford, D. The irreducibility of the space of curves of given genus. Publ. Math. IHÉS, 36: 75-109, 1969.

### 在线资源

- [Moduli Space Wikipedia](https://en.wikipedia.org/wiki/Moduli_space)
- [nLab - Moduli Space](https://ncatlab.org/nlab/show/moduli+space)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
