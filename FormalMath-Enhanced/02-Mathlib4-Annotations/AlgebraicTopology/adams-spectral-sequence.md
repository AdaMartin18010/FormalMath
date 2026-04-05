---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Adams谱序列
---
# Adams谱序列

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SpectralSequence.Adams

namespace AlgebraicTopology

/-- Adams谱序列 -/
theorem adams_spectral_sequence
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CWComplex X] [CWComplex Y]
    {p : ℕ} [Fact (Nat.Prime p)] :
    ∃ (E₂ : GradedObject (Module (ZMod p)) (ℕ × ℕ)),
      E₂ s t = Ext^{s,t}_{A_p}(H^*(Y), H^*(X)) ∧
      ConvergesTo (AssociatedGraded (StableHomotopy X Y)) := by
  -- 稳定同伦群的Adams谱序列
  sorry

/-- Adams滤过 -/
theorem adams_filtration
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CWComplex X] [CWComplex Y]
    (f : X → Y) [StableMap f] :
    ∃ (n : ℕ), f ∈ AdamsFiltration n ∧
    f ∉ AdamsFiltration (n+1) := by
  -- 映射的Adams滤过度数
  sorry

end AlgebraicTopology
```

## 数学背景

Adams谱序列由J. Frank Adams在1958年引入，是计算球面稳定同伦群的最重要工具之一。这一谱序列将拓扑问题转化为代数问题——用Steenrod代数的上同调来计算同伦群。Adams利用这一方法解决了Hopf不变量1问题，证明了实除代数只能在维数1,2,4,8存在。Novikov后来发展了基于复配边理论的推广版本（Adams-Novikov谱序列）。

## 直观解释

Adams谱序列如同"层层剥开"一个拓扑空间的结构。第一页 $E_2$ 包含了用模2上同调（或一般上同调理论）能检测到的"初级信息"。微分 $d_r$ 测量了"高阶 attach"的方式——这些信息在初级描述中不可见，但对同伦群至关重要。收敛结果给出了稳定同伦群的结构，滤过则对应了"复杂度"或"可检测性"的层次。

## 形式化表述

设 $X, Y$ 是CW复形，$p$ 是素数，$A_p$ 是模 $p$ Steenrod代数。

**Adams谱序列**：存在谱序列 $\{E_r^{s,t}\}$ 满足：
$$E_2^{s,t} = \text{Ext}_{A_p}^{s,t}(H^*(Y; \mathbb{Z}/p), H^*(X; \mathbb{Z}/p))$$

**收敛**：$E_\infty^{s,t} \Rightarrow \{Y, X\}_{t-s}$（稳定同伦群），带有Adams滤过。

**边缘同态**：$E_2^{0,t} = \text{Hom}_{A_p}(H^*(Y), H^*(X))$ 对应上同调运算。

## 证明思路

1. **Adams分解**：构造空间的"代数滤过"
2. **上纤维序列**：用Eilenberg-MacLane空间逼近
3. **Ext群计算**：Steenrod代数的同调代数
4. **微分结构**：确定 $d_2$ 和更高微分
5. **收敛证明**：验证到稳定同伦群的收敛

## 示例

### 示例 1：球面的同伦群

**问题**：计算 $\pi_{n+k}^S(S^n)$ 的低维群。

**解答**：

对 $X = Y = S^0$，Adams谱序列计算球面的稳定同伦群。

$E_2^{s,t} = \text{Ext}_{A_2}^{s,t}(\mathbb{Z}/2, \mathbb{Z}/2)$

Adams计算了前几十个稳定同伦群，发现了周期性的模式。

### 示例 2：Hopf不变量

**问题**：用Adams谱序列证明Hopf不变量1问题。

**解答**：

Hopf映射 $\eta, \nu, \sigma$ 分别对应 $E_2^{1,2}, E_2^{1,4}, E_2^{1,8}$。

Adams证明不存在更高维的Hopf不变量1元。

这等价于实除代数仅存在于维数1,2,4,8（Bott周期性）。

## 应用

- **球面同伦群**：稳定同伦群的系统计算
- **surgery理论**：流形分类的同伦障碍
- **代数K-理论**：Quillen的计算方法
- **配边理论**：Thom谱的计算
- **chromatic同伦论**：复杂性的分层

## 相关概念

- [Leray-Serre谱序列](./leray-serre-spectral-sequence.md)：同调版本
- Steenrod代数：Adams谱序列的基础
- Ext函子：$E_2$页的代数结构
- 稳定同伦群：收敛目标
- Adams-Novikov谱序列：推广版本

## 参考

### 教材

- Ravenel, D.C. Complex Cobordism and Stable Homotopy Groups of Spheres. AMS, 2004.
- Switzer, R.M. Algebraic Topology - Homotopy and Homology. Springer, 1975.

### 论文

- Adams, J.F. On the structure and applications of the Steenrod algebra. Comment. Math. Helv., 32: 180-214, 1958.
- Adams, J.F. On the non-existence of elements of Hopf invariant one. Ann. of Math., 72: 20-104, 1960.

### 在线资源

- [Adams Spectral Sequence Wikipedia](https://en.wikipedia.org/wiki/Adams_spectral_sequence)
- [nLab - Adams Spectral Sequence](https://ncatlab.org/nlab/show/Adams+spectral+sequence)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
