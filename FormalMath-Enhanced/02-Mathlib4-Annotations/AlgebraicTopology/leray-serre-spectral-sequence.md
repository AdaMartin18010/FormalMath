---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Leray-Serre谱序列

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SpectralSequence.LeraySerre

namespace AlgebraicTopology

/-- Leray-Serre谱序列 -/
theorem leray_serre_spectral_sequence
    {B F E : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace E]
    (p : E → B) [IsFibration p]
    {R : Type*} [CommRing R] :
    ∃ (E₂ : GradedObject (Module R) (ℕ × ℕ)),
      E₂ p q = H^p (B, H^q (F, R)) ∧
      ConvergesTo E₂ (H^{p+q} (E, R)) := by
  -- 纤维丛的上同调谱序列
  sorry

/-- 边缘同态的构造 -/
theorem transgression_map
    {B F E : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace E]
    (p : E → B) [IsFibration p]
    {R : Type*} [CommRing R] (n : ℕ) :
    ∃ (τ : H^n F → H^{n+1} B),
      IsTransgression τ := by
  -- 从纤维到基空间的边缘同态
  sorry

end AlgebraicTopology
```

## 数学背景

Leray-Serre谱序列由Jean Leray在1946年发明，由Jean-Pierre Serre在1950年代发展完善。这是代数拓扑中计算纤维丛同调/上同调的最强大工具。谱序列将总空间的上同调用纤维和基空间的上同调来表达，通过逐页逼近的方式计算。Serre利用这一工具计算了球面的同伦群，证明了诸多深刻结果。

## 直观解释

Leray-Serre谱序列如同"层叠的过滤器"，逐步揭示纤维丛的整体结构。第一页 $E_2$ 包含纤维和基空间的"局部信息"（$H^p(B, H^q(F))$）。微分 $d_r$ 如同"连接组织"，告诉我们如何将这些局部片段"粘合"成整体。随着页数增加，信息逐渐"稳定"，最终给出总空间的上同调。这就像通过多个放大镜（不同的分辨率）来观察一个复杂物体。

## 形式化表述

设 $F \to E \xrightarrow{p} B$ 是纤维丛，$R$ 是系数环。

**Leray-Serre谱序列**：存在谱序列 $\{E_r, d_r\}$ 满足：
$$E_2^{p,q} = H^p(B, \mathcal{H}^q(F; R))$$
其中 $\mathcal{H}^q(F; R)$ 是局部系数系统。

**收敛**：$E_\infty^{p,q} \Rightarrow H^{p+q}(E; R)$（某种滤过结构的相伴分次）。

**边缘同态**（Transgression）：若 $E_2^{p,0} = H^p(B)$，$E_2^{0,q} = H^q(F)$，则存在 $\tau: H^{n}(F) \to H^{n+1}(B)$。

## 证明思路

1. **滤过构造**：用纤维诱导的滤过定义谱序列
2. **$E_2$页计算**：验证局部系数的上同调
3. **微分分析**：确定 $d_2, d_3, \ldots$ 的结构
4. **边缘映射**：识别特殊的边缘同态
5. **收敛性证明**：验证到总空间上同调的收敛

## 示例

### 示例 1：球丛

**问题**：设 $S^{n-1} \to E \to B$ 是球丛，计算 $H^*(E)$。

**解答**：

$E_2^{p,q} = H^p(B; H^q(S^{n-1}))$，其中 $H^q(S^{n-1}) = R$（$q = 0, n-1$）或0。

谱序列只有两行非零：$q = 0$ 和 $q = n-1$。

微分 $d_n: E_n^{p, n-1} \to E_n^{p+n, 0}$ 是Euler类的杯积。

### 示例 2：道路纤维丛

**问题**：计算 $  ext{Map}(S^1, X) = LX$ 的上同调。

**解答**：

$\Omega X \to LX \to X$ 是纤维丛。

若 $X$ 是单连通，Serre谱序列给出Hochschild同调与环路空间上同调的关系。

## 应用

- **球面同伦群**：Serre的计算方法
- **示性类**：Euler类、Stiefel-Whitney类的计算
- **K-理论**：Atiyah-Hirzebruch谱序列
- **等变拓扑**：Borel构造的上同调
- **弦拓扑**：Chas-Sullivan环结构

## 相关概念

- [谱序列基础](./spectral-sequence-basics.md)：Leray-Serre的理论基础
- [纤维丛](./fibre-bundle.md)：谱序列的几何对象
- [局部系数](./local-coefficient.md)：$E_2$页的系数系统
- [边缘同态](./transgression.md)：特殊的微分映射
- [Grothendieck谱序列](./grothendieck-spectral-sequence.md)：代数版本

## 参考

### 教材

- McCleary, J. A User's Guide to Spectral Sequences. Cambridge, 2001.
- Hatcher, A. Algebraic Topology. Cambridge, 2002. Chapter 1

### 论文

- Serre, J-P. Homologie singulière des espaces fibrés. Ann. of Math., 54: 425-505, 1951.
- Leray, J. L'anneau spectral et l'anneau filtré d'homologie d'un espace localement compact et d'une application continue. J. Math. Pures Appl., 29: 1-139, 1950.

### 在线资源

- [Serre Spectral Sequence Wikipedia](https://en.wikipedia.org/wiki/Serre_spectral_sequence)
- [nLab - Serre Spectral Sequence](https://ncatlab.org/nlab/show/Serre+spectral+sequence)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
