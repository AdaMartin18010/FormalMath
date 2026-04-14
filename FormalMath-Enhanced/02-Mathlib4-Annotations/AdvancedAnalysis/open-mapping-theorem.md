---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 开映射定理 (Open Mapping Theorem)
---
# 开映射定理 (Open Mapping Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.Banach

namespace Analysis

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace E] [CompleteSpace F]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Banach 开映射定理：Banach 空间之间的满射连续线性映射是开映射 -/
theorem open_mapping {T : E →L[𝕜] F} (hT : Surjective T) :
    IsOpenMap T := by
  -- 利用 Baire 纲定理和线性映射的齐次性证明
  sorry

end Analysis
```

## 数学背景

开映射定理（Banach 开映射定理）是泛函分析中的核心结果之一，由波兰数学家斯特凡·巴拿赫（Stefan Banach）和德国数学家朱利叶斯·肖德尔（Juliusz Schauder）在20世纪20年代末证明。该定理断言：若 $T$ 是从 Banach 空间 $E$ 到 Banach 空间 $F$ 的满射连续线性映射，则 $T$ 是开映射——即 $T$ 将 $E$ 中的开集映为 $F$ 中的开集。开映射定理与闭图像定理、一致有界性原理一起被称为泛函分析的三大定理。

## 直观解释

开映射定理提供了一个反直觉但极其重要的结论：在完备赋范空间中，一个满射的连续线性映射不仅保持极限运算，还保持开集的结构。在有限维空间中，任何线性映射都是连续的，而满射线性映射自然将开集映为开集。但在无限维空间中，连续性并不自动保证开映射性。开映射定理告诉我们：只要定义域和值域都是完备的（Banach 空间），满射连续线性算子就一定是开映射。

## 形式化表述

设 $E$ 和 $F$ 是 Banach 空间，$T: E \to F$ 是满射的连续线性映射，则：

1. $T$ 是开映射：若 $U \subseteq E$ 是开集，则 $T(U) \subseteq F$ 也是开集
2. （逆映射定理）若 $T$ 还是单射，则 $T^{{-1}}: F \to E$ 是连续线性映射

等价表述：存在常数 $c > 0$ 使得对任意 $y \in F$，存在 $x \in E$ 满足 $Tx = y$ 且 $||x|| \leq c||y||$。

其中：

- Banach 空间是完备的赋范向量空间
- 开映射是指将开集映为开集的映射
- 逆映射定理是开映射定理的直接推论

## 证明思路

1. **Baire 纲定理**：由于 $T$ 满射，$F = \bigcup_{{n=1}}^\infty \overline{T(B_n)}$。由 Baire 纲定理，存在某个 $n$ 使得 $\overline{T(B_n)}$ 有非空内部
2. **开球像包含**：利用线性齐次性，证明单位开球 $B_E$ 的像包含 $F$ 中某个以原点为中心的开球
3. **开集保持**：对任意开集 $U \subseteq E$ 和 $x \in U$，证明 $T(U)$ 包含 $T(x)$ 的一个邻域
4. **逆映射连续性**：若 $T$ 是双射，则 $T^{{-1}}$ 作为开映射的逆映射必是连续的

核心洞察在于完备性（Baire 纲性质）使得线性映射的像不可能过于稀薄。

## 示例

### 示例 1：逆映射定理

设 $T: \ell^2 \to \ell^2$ 是由可逆无穷矩阵定义的线性算子。若 $T$ 是双射且连续，则逆映射定理保证 $T^{{-1}}$ 也连续。在数值计算中，这意味着方程 $Tx = y$ 的解关于 $y$ 是稳定的。

### 示例 2：Fourier 级数

在 $L^2([0, 2\pi])$ 中，Fourier 变换是从一个 Hilbert 空间到序列空间 $\ell^2$ 的等距同构。逆映射定理保证了 Fourier 逆变换的连续性，这是调和分析的基础。

### 示例 3：微分算子

考虑椭圆型偏微分算子 $P: H^s(M) \to H^{{s-k}}(M)$。在适当条件下，$P$ 是满射且连续，开映射定理保证了其像中的每个元素都可以被 $H^s$ 中的某个元素以可控范数实现。

## 应用

- **泛函分析**：Banach 空间上线性算子可逆性的判定
- **偏微分方程**：椭圆型方程解的正则性和稳定性估计
- **调和分析**：Fourier 变换和反演公式的连续性
- **控制理论**：线性系统可控性和可观测性的分析
- **数值分析**：算子方程离散化的适定性研究

## 相关概念

- Banach 空间 (Banach Space)：完备的赋范向量空间
- 开映射 (Open Map)：将开集映为开集的映射
- Baire 纲定理 (Baire Category Theorem)：完备度量空间中可数多个稠密开集的交仍稠密
- 逆映射定理 (Inverse Mapping Theorem)：双射连续线性算子的逆必连续
- 一致有界性原理 (Uniform Boundedness Principle)：泛函分析三大定理之一

## 参考

### 教材

- [W. Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 2]
- [H. Brezis. Functional Analysis, Sobolev Spaces and Partial Differential Equations. Springer, 2011. Chapter 2]

### 在线资源

- [Mathlib4 - Banach](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*