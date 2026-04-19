---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Peter-Weyl定理
---
# Peter-Weyl定理

## Mathlib4 引用

```lean
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.MeasureTheory.Function.LpSpace

namespace HarmonicAnalysis

/-- Peter-Weyl定理：紧致群的表示理论 -/
theorem peter_weyl_theorem
    {G : Type*} [TopologicalSpace G] [CompactSpace G]
    [Group G] [IsTopologicalGroup G]
    {𝕜 : Type*} [RCLike 𝕜] :
    Dense (Subalgebra.adjoin 𝕜
      {f : C(G, 𝕜) | ∃ (V : FiniteDimensional.Rep 𝕜 G),
        f = Matrix.trace ∘ V.representationMatrix})
      (ContinuousMap.mkContinuousMap G 𝕜) := by
  -- 利用Stone-Weierstrass定理证明稠密性
  apply stone_weierstrass
  · -- 分离点
    sorry
  · -- 对共轭封闭
    sorry

end HarmonicAnalysis
```

## 数学背景

Peter-Weyl定理由Hermann Weyl和Fritz Peter在1927年证明，是紧致群表示论的奠基性定理。它将有限群表示论中Maschke定理和特征标正交性的结果推广到紧致群情形，建立了紧致群上的调和分析理论。这一定理是现代抽象调和分析、非交换傅里叶分析和量子场论的基础。

## 直观解释

Peter-Weyl定理告诉我们：紧致群的"所有信息"都包含在它的有限维不可约表示中。就像周期函数可以用傅里叶级数展开为正弦余弦函数的叠加，紧致群上的函数也可以"展开"为矩阵系数的叠加。这些矩阵系数如同紧致群上的"正弦波"，构成了连续函数空间的稠密子集。

## 形式化表述

设 $G$ 是紧致拓扑群，$\widehat{G}$ 是其不可约酉表示的等价类集合。

**Peter-Weyl定理**：

1. $L^2(G)$ 可以分解为不可约表示矩阵系数的直和：
   $$L^2(G) \cong \widehat{\bigoplus}_{\pi \in \widehat{G}}} V_\pi \otimes V_\pi^*$$

2. 矩阵系数在 $C(G)$ 中稠密（一致拓扑）

3. 特征标 $\chi_\pi$ 构成类函数空间的正交基

## 证明思路

1. **构造卷积代数**：考虑 $L^2(G)$ 上的卷积算子
2. **紧算子谱理论**：证明卷积算子是紧的自伴算子
3. **谱分解**：利用紧算子的谱定理得到有限维不变子空间
4. **Stone-Weierstrass**：应用该定理证明矩阵系数的稠密性

## 示例

### 示例 1：圆周群 $\mathbb{T}$

**问题**：验证 $G = S^1$ 时Peter-Weyl定理给出经典傅里叶级数。

**解答**：

$S^1$ 的不可约表示为 $\rho_n(z) = z^n$（$n \in \mathbb{Z}$），都是一维的。

矩阵系数就是特征标本身：$\chi_n(e^{i\theta}) = e^{in\theta}$

Peter-Weyl定理退化为：$\{e^{in\theta}\}_{n \in \mathbb{Z}}$ 是 $L^2(S^1)$ 的正交基，即经典傅里叶级数。

### 示例 2：$SO(3)$ 的球谐函数

**问题**：应用Peter-Weyl定理于三维旋转群。

**解答**：

$SO(3)$ 的不可约表示由整数 $l \geq 0$ 标记，维数为 $2l+1$。

在 $L^2(S^2)$ 上，这对应球谐函数 $Y_l^m$ 的分解：
$$L^2(S^2) = \widehat{\bigoplus}_{l=0}^{\infty}} \mathcal{H}_l$$

其中 $\mathcal{H}_l$ 是 $2l+1$ 维的球谐函数空间。

## 应用

- **非交换傅里叶分析**：紧致群上的调和分析
- **量子力学**：角动量理论和选择定则
- **机器人学**：刚体运动的表示和插值
- **计算机图形学**：球谐光照
- **信号处理**：方向数据的分析

## 相关概念

- [Maschke定理](./maschke-theorem.md)：有限群版本
- [特征标正交性](./character-orthogonality.md)：离散情形
- Plancherel定理：傅里叶变换的等距性
- [Frobenius互反律](./frobenius-reciprocity.md)：诱导表示理论
- Tannaka对偶：从表示重构群

## 参考

### 教材

- Folland, G.B. A Course in Abstract Harmonic Analysis. CRC Press, 2015. Chapter 5
- Bump, D. Lie Groups. Springer, 2013. Chapter 2

### 论文

- Peter, F. & Weyl, H. Die Vollständigkeit der primitiven Darstellungen einer geschlossenen kontinuierlichen Gruppe. Math. Ann., 97: 737-755, 1927.

### 在线资源

- [Peter-Weyl Theorem Wikipedia](https://en.wikipedia.org/wiki/Peter%E2%80%93Weyl_theorem)
- [nLab - Peter-Weyl Theorem](https://ncatlab.org/nlab/show/Peter-Weyl+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
