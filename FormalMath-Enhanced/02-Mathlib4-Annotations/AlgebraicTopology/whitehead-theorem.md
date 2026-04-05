---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Whitehead定理
---
# Whitehead定理

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Homotopy.Whitehead

namespace AlgebraicTopology

/-- Whitehead定理 -/
theorem whitehead_theorem 
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CWComplex X] [CWComplex Y]
    (f : X → Y) [Continuous f]
    (hf : ∀ (n : ℕ), 
      π_n f : π_n X → π_n Y ≃* π_n Y) :
    IsHomotopyEquivalence f := by
  -- 诱导同伦群同构的映射是同伦等价
  sorry

/-- 同调版本的Whitehead定理 -/
theorem whitehead_homology 
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CWComplex X] [CWComplex Y]
    (f : X → Y) [Continuous f]
    (hf : ∀ (n : ℕ),
      H_n f : H_n X → H_n Y ≃ H_n Y)
    (hπ₁ : π₁ f : π₁ X → π₁ Y ≃* π₁ Y) :
    IsHomotopyEquivalence f := by
  -- 同调同构加基本群同构蕴含同伦等价
  sorry

end AlgebraicTopology
```

## 数学背景

Whitehead定理由J.H.C. Whitehead在1949年证明，是代数拓扑中最重要的结果之一。定理表明：对于CW复形，如果一个连续映射在所有同伦群上诱导同构，则它是同伦等价。这为判断两个空间是否"相同"（同伦等价）提供了代数标准。Whitehead定理也说明了同伦群作为空间不变量的完备性——至少对于CW复形，同伦群完全决定了同伦型。

## 直观解释

Whitehead定理如同一个"识别系统"：通过代数指纹（同伦群）来确认几何对象的身份。想象两个复杂的拓扑空间——直接判断它们是否"形状相同"（同伦等价）非常困难。Whitehead定理说：只需检查它们"所有的洞"是否一一对应（同伦群同构），就能断定它们可以连续地相互变形。这是代数拓扑的核心哲学——用代数解决几何问题。

## 形式化表述

设 $X, Y$ 是CW复形，$f: X \to Y$ 是连续映射。

**Whitehead定理**：若 $f_*: \pi_n(X) \to \pi_n(Y)$ 对所有 $n \geq 0$ 是同构，则 $f$ 是同伦等价。

**等价表述**：
- 存在 $g: Y \to X$ 使得 $g \circ f \simeq 1_X$，$f \circ g \simeq 1_Y$
- $f$ 是弱同伦等价且 $X, Y$ 是CW复形

**同调版本**：若 $X, Y$ 单连通，且 $f_*: H_n(X) \to H_n(Y)$ 对所有 $n$ 是同构，则 $f$ 是同伦等价。

## 证明思路

1. **映射柱**：将 $f$ 替换为包含映射
2. **同伦群消失**：证明映射柱的同伦群平凡
3. **胞腔逼近**：逐维扩展同伦
4. **同伦延拓**：利用CW复形的性质
5. **构造逆映射**：从平凡同伦群构造同伦逆

## 示例

### 示例 1：球面与 Moore空间

**问题**：比较 $S^n$ 与 $K(\mathbb{Z}, n)$。

**解答**：

$K(\mathbb{Z}, n)$（Eilenberg-MacLane空间）满足 $\pi_n = \mathbb{Z}$，其他同伦群平凡。

$S^n$ 的同伦群更复杂，但 $n > 1$ 时 $\pi_n(S^n) = \mathbb{Z}$。

包含映射 $S^n \hookrightarrow K(\mathbb{Z}, n)$ 在同伦群上诱导同构仅当 $n = 1$。

### 示例 2：透镜空间

**问题**：判断两个透镜空间是否同伦等价。

**解答**：

透镜空间 $L(p, q)$ 和 $L(p, q')$ 有相同的基本群 $\mathbb{Z}/p$。

它们有相同的同伦群当且仅当有相同的Reidemeister挠率。

Whitehead定理说明它们同伦等价当且仅当 $qq' \equiv \pm m^2 \pmod{p}$ 对某个 $m$。

## 应用

- **同伦型分类**：CW复形的代数判定
- ** surgery理论**：流形改造的同伦条件
- **有理同伦论**：Quillen和Sullivan理论
- **模型范畴**：弱等价的公理化
- **∞-范畴**：同伦理论的现代框架

## 相关概念

- [同伦群](./homotopy-group.md)：Whitehead定理的核心不变量
- [Hurewicz定理](./hurewicz-theorem.md)：同伦群与同调群的联系
- [CW复形](./cw-complex.md)：Whitehead定理的适用空间
- [弱同伦等价](./weak-homotopy-equivalence.md)：诱导同伦群同构的映射
- [胞腔逼近定理](./cellular-approximation.md)：证明的关键工具

## 参考

### 教材

- Hatcher, A. Algebraic Topology. Cambridge, 2002. Chapter 4
- Spanier, E.H. Algebraic Topology. Springer, 1966. Chapter 7

### 论文

- Whitehead, J.H.C. Combinatorial homotopy I. Bull. Amer. Math. Soc., 55: 213-245, 1949.
- Whitehead, J.H.C. Combinatorial homotopy II. Bull. Amer. Math. Soc., 55: 453-496, 1949.

### 在线资源

- [Whitehead Theorem Wikipedia](https://en.wikipedia.org/wiki/Whitehead_theorem)
- [nLab - Whitehead Theorem](https://ncatlab.org/nlab/show/Whitehead+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
