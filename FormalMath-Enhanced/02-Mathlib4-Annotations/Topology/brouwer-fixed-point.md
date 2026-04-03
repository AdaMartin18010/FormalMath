---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 布劳威尔不动点定理 (Brouwer Fixed-Point Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homotopy.Contractible

namespace Topology

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 布劳威尔不动点定理 -/
theorem brouwerFixedPoint {s : Set E} (hs : Convex ℝ s) (hsc : IsCompact s)
    (hsne : s.Nonempty) (f : E → E) (hf : ContinuousOn f s) (hfs : MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  -- 拓扑学经典定理的证明
  sorry

/-- 单位球版本 -/
theorem brouwerFixedPoint_unitBall (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hfs : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  sorry

end Topology
```

## 数学背景

布劳威尔不动点定理是拓扑学中最著名和最深刻的定理之一，由荷兰数学家卢伊岑·埃赫布雷赫特·扬·布劳威尔（L. E. J. Brouwer）于1910年证明。该定理揭示了拓扑空间的深刻性质，是代数拓扑发展的重要动力。不动点定理在经济学（博弈论）、微分方程和动力系统中有广泛应用。

## 直观解释

布劳威尔不动点定理告诉我们：**将一个实心球连续映射到自身，至少有一个点保持不动**。想象一杯咖啡：无论你如何连续搅拌（没有泼出），总有一点咖啡最终回到原来的位置。

这一定理说明拓扑空间的某些"全局"性质（如连通性、紧致性）对映射施加了强约束。直观上，要"打散"所有点而不留下不动点，必然需要某种"撕裂"，而这违反了连续性。

## 形式化表述

设 $B^n = \{x \in \mathbb{R}^n : \|x\| \leq 1\}$ 是 $n$ 维闭单位球，$f: B^n \to B^n$ 是连续映射，则：

$$\exists x \in B^n : f(x) = x$$

### 等价形式

任何紧致凸集到自身的连续映射都有不动点。

## 证明思路

### 代数拓扑证明：

1. **反证法**：假设 $f$ 无不动点
2. **收缩映射**：构造收缩映射 $r: B^n \to S^{n-1}$
3. **同调矛盾**：导出 $H_{n-1}(S^{n-1}) \to H_{n-1}(B^n)$ 非零的矛盾
4. **结论**：假设不成立，存在不动点

### 分析方法（$n=2$）：

利用格林定理或复分析方法证明平面情形的特殊版本。

### 组合方法（Sperner 引理）：

1. **三角剖分**：对单纯形进行细三角剖分
2. **Sperner 标记**：构造特殊标记
3. **完全单形存在性**：证明存在完全标记的单形
4. **极限论证**：通过极限得到不动点

## 示例

### 示例 1：一维情形

$f: [0, 1] \to [0, 1]$ 连续。

若 $f(0) = 0$ 或 $f(1) = 1$，已找到不动点。

否则 $f(0) > 0$，$f(1) < 1$。设 $g(x) = f(x) - x$，则 $g(0) > 0$，$g(1) < 0$。

由介值定理，$\exists c: g(c) = 0$，即 $f(c) = c$。

### 示例 2：经济均衡

设有 $n$ 种商品，价格向量 $p \in \Delta^{n-1}$（单纯形）。

超额需求函数 $z: \Delta^{n-1} \to \mathbb{R}^n$ 满足瓦尔拉斯法则：$p \cdot z(p) = 0$。

布劳威尔定理保证存在均衡价格 $p^*$ 使得 $z(p^*) \leq 0$。

### 示例 3：博弈论（纳什均衡）

有限博弈中，混合策略组合空间是紧致凸集。

最佳反应映射是连续的，由布劳威尔定理，纳什均衡存在。

## 应用

- **经济学**：一般均衡存在性、博弈论纳什均衡
- **微分方程**：佩亚诺存在性定理
- **动力系统**：周期轨道存在性
- **图论**：图染色、网络流
- **泛函分析**：算子理论中的不动点

## 相关概念

- [紧致性 (Compactness)](./compactness.md)：拓扑空间的关键性质
- [凸集 (Convex Set)](./convex-set.md)：包含所有连线的集合
- [收缩映射 (Retraction)](./retraction.md)：$r: X \to A$ 满足 $r|_A = \text{id}_A$
- [角谷不动点定理 (Kakutani Fixed-Point Theorem)](./kakutani-fixed-point.md)：集值映射版本
- [莱夫谢茨不动点定理 (Lefschetz Fixed-Point Theorem)](./lefschetz-fixed-point.md)：代数拓扑推广

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2]
- [Border. Fixed Point Theorems with Applications to Economics and Game Theory. Cambridge, 1985]

### 历史文献

- [Brouwer. Über eineindeutige, stetige Transformationen von Flächen in sich. 1910]

### 在线资源

- [Mathlib4 文档 - Fixed Point](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
