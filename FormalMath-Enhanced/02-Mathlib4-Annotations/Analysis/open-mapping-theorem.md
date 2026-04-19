---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 开映射定理 (Open Mapping Theorem)
---
# 开映射定理 (Open Mapping Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

namespace OpenMapping

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- 开映射定理：满射有界线性算子是开映射 -/
theorem open_mapping {T : E →L[ℝ] F} (hT : Function.Surjective T) :
    IsOpenMap T := by
  -- Baire纲定理的应用
  have h1 : ∃ r > 0, ball 0 r ⊆ closure (T '' ball 0 1) := by
    sorry
  -- 线性性和齐次性
  have h2 : ∀ y ∈ ball 0 r, ∃ x, ‖x‖ < 2 ∧ T x = y := by
    sorry
  -- 证明开性
  sorry

/-- 逆算子定理 -/
theorem inverse_operator {T : E →L[ℝ] F} (hT : Function.Bijective T) :
    Continuous (Function.invFun T) := by
  have : IsOpenMap T := open_mapping hT.surjective
  -- 双射开映射的逆连续
  sorry

/-- 闭图像定理 -/
theorem closed_graph {T : E → F} (hT : LinearMap ℝ E F T)
    (hgraph : IsClosed {p : E × F | p.2 = T p.1}) :
    Continuous T := by
  -- 将T视为图像到F的投影
  let G := {p : E × F | p.2 = T p.1}
  let π₁ : G → E := fun p => p.1.1
  let π₂ : G → F := fun p => p.1.2
  -- π₁是同胚
  sorry

end OpenMapping
```

## 数学背景

开映射定理由Stefan Banach和Juliusz Schauder在1929-1930年证明，是泛函分析的核心结果之一。该定理表明，Banach空间之间的满射有界线性算子必为开映射——将开集映为开集。作为推论，双射有界线性算子的逆自动连续（逆算子定理），这是泛函分析中少有的"自动连续性"结果。闭图像定理表明，线性算子的闭图像蕴含连续性，这是证明无界算子（如微分算子）闭延拓存在性的重要工具。

## 直观解释

开映射定理告诉我们：**Banach空间之间的"好"满射算子不会"压缩"开集**。

想象算子 $T$ 把空间 $E$ 拉伸或压缩映射到空间 $F$。定理说，如果 $T$ 是满射（覆盖全空间）且有界（不破坏收敛性），那么它不会把"开放的区域"压成"有边界的区域"。这就像说，一个完整且光滑的覆盖映射保持空间的"开放性"。

## 形式化表述

设 $E, F$ 是Banach空间，$T \in \mathcal{L}(E, F)$（有界线性算子）。

**开映射定理**：若 $T$ 满射，则 $T$ 是开映射（开集的像开）。

**逆算子定理**：若 $T$ 双射，则 $T^{-1} \in \mathcal{L}(F, E)$。

**闭图像定理**：若 $\text{graph}(T) = \{(x, Tx) : x \in E\}$ 在 $E \times F$ 中闭，则 $T$ 有界。

## 证明思路

1. **Baire纲定理**：
   - $F = \bigcup_n nT(\overline{B_E})$（$\overline{B_E}$ 是 $E$ 的闭单位球）
   - 某 $nT(\overline{B_E})$ 含内点（Baire纲）

2. **对称性和凸性**：
   - $T(\overline{B_E})$ 对称、凸
   - 若含内点，则 $0$ 是内点

3. **开性**：
   - 存在 $\delta > 0$ 使 $B_F(0, \delta) \subseteq \overline{T(B_E)}$
   - 由线性性，$T(B_E(x, r))$ 含 $B_F(Tx, \delta r)$

4. **闭图像 $\Rightarrow$ 连续性**：
   - 闭图像是Banach空间
   - 投影到 $E$ 是同胚
   - 投影到 $F$ 连续

核心洞察是Baire纲定理在完备空间上的威力。

## 示例

### 示例 1：逆算子不连续的反例（不完备）

设 $E = C[0,1]$（sup范数），$F = C[0,1]$（$L^1$范数）。

恒等映射 $I: E \to F$ 连续、双射。

但 $I^{-1}$ 不连续（可取 $f_n$ 集中于一点的函数列）。

$E$ 完备但 $F$（$L^1$范数下）不完备。

### 示例 2：微分算子

$T = \frac{d}{dx}: C^1[0,1] \to C[0,1]$。

不是满射，不开映射。

但考虑 $T: C^1[0,1] \to C[0,1] \times \mathbb{R}$，$Tf = (f', f(0))$，这是同构。

### 示例 3：积分算子

$(Tf)(x) = \int_0^x f(t) dt$ 从 $L^1[0,1]$ 到 $AC[0,1]$（绝对连续函数）。

双射，逆是微分，但 $AC[0,1]$ 需要合适的范数。

## 应用

- **Fredholm理论**：算子的指标理论
- **偏微分方程**：解的存在性和正则性
- **调和分析**：傅里叶变换的逆
- **控制理论**：系统可控性
- **量子力学**：自伴算子的谱理论

## 相关概念

- Banach空间 (Banach Space)：完备的赋范空间
- 有界线性算子 (Bounded Linear Operator)：连续线性映射
- Baire纲定理 (Baire Category Theorem)：完备空间的非空性
- 闭算子 (Closed Operator)：闭图像的线性算子
- Fredholm算子 (Fredholm Operator)：有限维核和余核的算子

## 参考

### 教材

- [Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 2]
- [Conway. A Course in Functional Analysis. Springer, 2nd edition, 1990. Chapter 3]

### 历史文献

- [Banach & Schauder. Über die Existenz invarianter Maße. 1929]

### 在线资源

- [Mathlib4 文档 - BanachSteinhaus][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/BanachSteinhaus.html](需更新)
- [Wikipedia - Open Mapping Theorem](https://en.wikipedia.org/wiki/Open_mapping_theorem_(functional_analysis))

---

*最后更新：2026-04-03 | 版本：v1.0.0*
