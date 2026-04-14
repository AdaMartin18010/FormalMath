---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Mayer-Vietoris序列 (Mayer-Vietoris Sequence)
---
# Mayer-Vietoris序列 (Mayer-Vietoris Sequence)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SingularHomology
import Mathlib.AlgebraicTopology.MayerVietoris

namespace MayerVietoris

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = ⊤)

/-- Mayer-Vietoris长正合列 -/
theorem mayer_vietoris_sequence (n : ℕ) :
    ExactSeq Ab [
      H_n (U ∩ V) → H_n U ⊞ H_n V → H_n X,
      H_n U ⊞ H_n V → H_n X → H_{n-1} (U ∩ V)
    ] := by
  -- 利用切除定理和正合性
  sorry

/-- 约化Mayer-Vietoris序列 -/
theorem reduced_mayer_vietoris (n : ℕ) :
    ExactSeq Ab [
      H̃_n (U ∩ V) → H̃_n U ⊞ H̃_n V → H̃_n X,
      H̃_n U ⊞ H̃_n V → H̃_n X → H̃_{n-1} (U ∩ V)
    ] := by
  sorry

end MayerVietoris
```

## 数学背景

Mayer-Vietoris序列是代数拓扑中计算同调群的重要工具，由Walther Mayer和Leopold Vietoris在1929年左右独立发展。该序列将空间的同调群与其开覆盖的同调群联系起来，提供了计算复杂空间同调的归纳方法。这是同调代数中正合列技术的典范应用，与van Kampen定理（基本群版本）形成对偶。

## 直观解释

Mayer-Vietoris序列告诉我们：**空间的"洞"信息可以从其部分的"洞"信息重建**。

想象空间 $X$ 被两个开集 $U$ 和 $V$ 覆盖。序列给出了 $X$ 的同调与 $U$、$V$ 以及交 $U \cap V$ 的同调之间的精确关系。这就像说，整体的几何特征可以通过局部部分的特征以及它们如何重叠来理解。

## 形式化表述

设 $X = U \cup V$，$U, V$ 开。

**Mayer-Vietoris长正合列**：
$$\cdots \to H_n(U \cap V) \xrightarrow{(i_*, j_*)} H_n(U) \oplus H_n(V) \xrightarrow{k_* - l_*} H_n(X) \xrightarrow{\partial} H_{n-1}(U \cap V) \to \cdots$$

其中：

- $i: U \cap V \to U$，$j: U \cap V \to V$ 是包含
- $k: U \to X$，$l: V \to X$ 是包含
- $\partial$ 是连接同态

## 证明思路

1. **链复形短正合列**：
   - $0 \to C_*(U \cap V) \xrightarrow{(i_\#, j_\#)} C_*(U) \oplus C_*(V) \xrightarrow{k_\# - l_\#} C_*(U + V) \to 0$
   - 其中 $C_*(U + V)$ 是小链（支撑在 $U$ 或 $V$ 中）

2. **同调长正合列**：
   - 短正合列诱导长正合列

3. **切除定理**：
   - $H_*(X) \cong H_*(U + V)$（小链与全链同调等价）

4. **正合性验证**：
   - 追踪各映射的核与像

核心洞察是链复形的代数性质与几何切除的结合。

## 示例

### 示例 1：球面

$X = S^n$，$U = S^n \setminus \{N\} \cong \mathbb{R}^n$，$V = S^n \setminus \{S\} \cong \mathbb{R}^n$。

$U \cap V \simeq S^{n-1}$。

Mayer-Vietoris给出 $H_k(S^n) \cong H_{k-1}(S^{n-1})$，归纳得 $H_n(S^n) = \mathbb{Z}$。

### 示例 2：环面

$T = S^1 \times S^1$，$U = T \setminus \{\text{一点}\}$，$V$ 是小圆盘。

$U \cap V \simeq S^1$。

计算得 $H_1(T) = \mathbb{Z}^2$，$H_2(T) = \mathbb{Z}$。

### 示例 3：双叶圆锥

两个圆锥沿顶点粘合。

$U, V$ 是各自圆锥，$U \cap V = \{\text{点}\}$。

计算约化同调，识别"粘合点"的影响。

## 应用

- **同调计算**：复杂空间的同调群计算
- **纤维丛**：Serre谱序列的基础
- **代数几何**：层上同调的计算
- **纽结理论**：补空间的同调
- **数据科学**：持续同调

## 相关概念

- 同调群 (Homology Group)：拓扑不变量
- 长正合列 (Long Exact Sequence)：同调代数工具
- [切除定理 (Excision Theorem)](./excision-theorem.md)：同调的局部化
- 相对同调 (Relative Homology)：空间对的同调
- 正合性 (Exactness)：核等于像

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2]
- [May. A Concise Course in Algebraic Topology. Chicago, 1999. Chapter 8]

### 历史文献

- [Mayer. Über abstrakte Topologie. 1929]
- [Vietoris. Über die Homologiegruppen der Vereinigung zweier Komplexe. 1930]

### 在线资源

- [Mathlib4 文档 - Homology][https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html](需更新)
- [Hatcher - Homology][https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
