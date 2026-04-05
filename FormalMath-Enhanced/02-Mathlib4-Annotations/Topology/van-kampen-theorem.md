---
msc_primary: 00A99
processed_at: '2026-04-03'
title: van Kampen定理 (van Kampen Theorem)
---
# van Kampen定理 (van Kampen Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = ⊤)
  (hUV_conn : (U ∩ V).Nonempty) [PathConnectedSpace (U ∩ V)]

/-- van Kampen定理：基本群的Seifert-van Kampen定理 -/
theorem van_kampen (x₀ : U ∩ V) :
    let ιU : U ∩ V → U := fun x => ⟨x.1, x.2.1⟩
    let ιV : U ∩ V → V := fun x => ⟨x.1, x.2.2⟩
    let jU : U → X := fun x => x.1
    let jV : V → X := fun x => x.1
    FundamentalGroupoid.pushout (ιU : U ∩ V → U) (ιV : U ∩ V → V) jU jV := by
  -- 证明万有性质
  sorry

/-- van Kampen定理（群版本）-/
theorem van_kampen_group (x₀ : U ∩ V) :
    FundamentalGroup X x₀ ≅
      (FundamentalGroup U ⟨x₀.1, x₀.2.1⟩) ∗_{FundamentalGroup (U ∩ V) x₀}
      (FundamentalGroup V ⟨x₀.1, x₀.2.2⟩) := by
  -- 自由积 with amalgamation
  sorry

end VanKampen
```

## 数学背景

van Kampen定理由H. Seifert在1931年和E. R. van Kampen在1933年独立证明，是代数拓扑中计算基本群的基本工具。该定理表明，空间的基本群可以通过开覆盖的基本群"粘合"而成。这是将拓扑问题约化为代数问题的典范，使得许多复杂空间的基本群计算成为可能。

## 直观解释

van Kampen定理告诉我们：**复杂空间的基本群是其"碎片"基本群的"粘合"**。

想象空间 $X$ 被两个重叠的开集 $U$ 和 $V$ 覆盖。定理说，$X$ 的环路（基本群）可以由 $U$ 和 $V$ 中的环路生成，但重叠区域 $U \cap V$ 中的环路在两边被视为相同。这就像说，两个国家的共同边界上的公民，无论用哪国护照，都是同一个人。

## 形式化表述

设 $X = U \cup V$，$U, V$ 开，$U \cap V$ 非空道路连通。

**van Kampen定理**：
$$\pi_1(X, x_0) \cong \pi_1(U, x_0) *_{\pi_1(U \cap V, x_0)} \pi_1(V, x_0)$$

即 **自由积 with amalgamation**（融合积）。

**群的表现**：若
- $\pi_1(U) = \langle A_U | R_U \rangle$
- $\pi_1(V) = \langle A_V | R_V \rangle$
- $\pi_1(U \cap V)$ 的生成元映射到两边

则 $\pi_1(X) = \langle A_U \cup A_V | R_U \cup R_V \cup \{\text{粘合关系}\} \rangle$

## 证明思路

1. **环路分解**：
   - 将 $X$ 中环路分解为交替的 $U$ 和 $V$ 中路径
   - 利用Lebesgue数引理保证细分存在
   
2. **同伦类对应**：
   - 证明这种分解在同伦意义下良定义
   - 重叠区域保证转移的连续性
   
3. **泛性质**：
   - 验证融合积的泛性质
   - 任何到群 $G$ 的同态可由 $U$ 和 $V$ 诱导
   
4. **同构构造**：
   - 显式构造同态及其逆
   - 验证互逆

核心洞察是开覆盖的代数化和路径的分解。

## 示例

### 示例 1：圆的基本群

$S^1 = U \cup V$，$U = S^1 \setminus \{N\}$，$V = S^1 \setminus \{S\}$。

$U \cong V \cong \mathbb{R}$（可缩），$U \cap V \cong \mathbb{R} \sqcup \mathbb{R}$（两个道路分支）。

修正：需要道路交。用四个开弧覆盖。

结果：$\pi_1(S^1) \cong \mathbb{Z}$。

### 示例 2：8字形

$X = S^1 \vee S^1$（两个圆一点并）。

每个 $S^1$ 有一个开邻域可缩到自身。

$\pi_1(X) \cong \mathbb{Z} * \mathbb{Z}$（两个生成元的自由群）。

### 示例 3：$S^2$

$U = S^2 \setminus \{N\} \cong \mathbb{R}^2$，$V = S^2 \setminus \{S\} \cong \mathbb{R}^2$。

$U \cap V \cong \mathbb{R}^2 \setminus \{0\} \simeq S^1$。

$\pi_1(U) = \pi_1(V) = 0$，$\pi_1(U \cap V) = \mathbb{Z}$。

$\pi_1(S^2) = 0 *_{\mathbb{Z}} 0 = 0$（平凡群）。

## 应用

- **胞腔复形**：CW复形的基本群计算
- **纽结理论**：纽结群、环绕群
- **代数几何**：étale基本群
- **几何群论**：群的图分解
- **拓扑数据分析**：持久同调

## 相关概念

- 基本群 (Fundamental Group)：环路同伦类
- 自由积 (Free Product)：群的自由并
- 融合积 (Amalgamated Product)：带粘合的自由积
- 道路连通 (Path Connected)：基本群定义的前提
- 同伦 (Homotopy)：连续变形

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 1]
- [Massey. A Basic Course in Algebraic Topology. Springer, 1991. Chapter 4]

### 历史文献

- [Seifert. Konstruktion dreidimensionaler geschlossener Räume. 1931]
- [van Kampen. On the connection between the fundamental groups of some related spaces. 1933]

### 在线资源

- [Mathlib4 文档 - VanKampen](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.html)[需更新]
- [Hatcher - Algebraic Topology](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
