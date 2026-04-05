---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Riemann映射定理 (Riemann Mapping Theorem)
---
# Riemann映射定理 (Riemann Mapping Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.Conformal.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace RiemannMapping

open Complex Metric

variable {U V : Set ℂ}

/-- Riemann映射定理：单连通真子域共形等价于单位圆盘 -/
theorem riemann_mapping_theorem [hU : IsOpen U] [hUsc : SimplyConnected ℂ U]
    (hUneq : U ≠ ⊤) (hU0 : (0 : ℂ) ∈ U) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧
      Function.Bijective f ∧
      MapsTo f U (ball 0 1) ∧
      MapsTo (Function.invFunOn f U) (ball 0 1) U := by
  -- 构造极值函数
  sorry

/-- 归一化Riemann映射的唯一性 -/
theorem riemann_mapping_uniqueness {f g : ℂ → ℂ} (hf : IsConformalMapOn f U) (hg : IsConformalMapOn g U)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hf' : deriv f 0 > 0) (hg' : deriv g 0 > 0)
    (hfr : MapsTo f U (ball 0 1)) (hgr : MapsTo g U (ball 0 1)) :
    EqOn f g U := by
  sorry

/-- 边界对应原理 -/
theorem boundary_correspondence [hUreg : IsJordanDomain U] {f : ℂ → ℂ}
    (hf : IsConformalMapOn f U) (hfext : ContinuousOn f (closure U)) :
    Function.Bijective (f ∘ Subtype.val : U → ball 0 1) := by
  sorry

end RiemannMapping
```

## 数学背景

Riemann映射定理由Bernhard Riemann在1851年的博士论文中提出并"证明"（存在逻辑漏洞），后由William Osgood、Constantin Carathéodory和Lars Ahlfors在20世纪初给出严格证明。这是单复变函数论中最重要和最优美的定理之一，揭示了单连通区域的几何分类——它们本质上只有一种（圆盘）。该定理在共形映射、流体动力学和电子工程中都有应用。

## 直观解释

Riemann映射定理告诉我们：**任何非全平面的单连通区域都可以"压扁"成单位圆盘，保持角度不变**。

想象你有一块橡皮膜（单连通区域），可以拉伸和挤压但不能撕裂或粘合（保持角度，即共形）。定理说，只要这块膜不是无限大（真子集），你总能把它变形为单位圆盘。这就像说，所有"简单"形状的二维区域在共形几何下都是等价的。

## 形式化表述

区域 $U \subsetneq \mathbb{C}$（真子集）称为**单连通**，如果每个闭曲线可以在 $U$ 内连续缩为一点。

**Riemann映射定理**：设 $U \subsetneq \mathbb{C}$ 是单连通区域，$z_0 \in U$。则存在唯一的共形映射 $f: U \to \mathbb{D}$（单位圆盘）满足：

1. $f(z_0) = 0$（归一化中心）
2. $f'(z_0) > 0$（归一化旋转）

**共形映射**：全纯且导数处处非零，保持角度和定向。

## 证明思路

1. **极值原理**：
   - 考虑族 $\mathcal{F} = \{f: U \to \mathbb{D} \text{ 全纯单射}, f(z_0) = 0\}$
   - 证明 $\mathcal{F} \neq \emptyset$（利用单连通性构造平方根）

2. **紧性论证**：
   - 选取 $f \in \mathcal{F}$ 使 $|f'(z_0)|$ 最大
   - 证明此 $f$ 必为满射（否则可用变换增大导数）

3. **Montel定理**：
   - 全纯函数族的正规性
   - 保证极值函数存在

4. **Hurwitz定理**：
   - 单射函数的极限是单射或常数
   - 保证极限映射的单射性

核心洞察是单连通性允许我们迭代地"展开"区域趋近圆盘。

## 示例

### 示例 1：上半平面到圆盘

$U = \mathbb{H} = \{z : \text{Im } z > 0\}$

Cayley变换：$f(z) = \frac{z-i}{z+i}$

将上半平面共形映射到单位圆盘，$f(i) = 0$。

### 示例 2：带形区域

$U = \{z : 0 < \text{Im } z < \pi\}$

指数映射：$f(z) = e^z$ 将 $U$ 映到上半平面，再组合Cayley变换。

### 示例 3：多边形映射（Schwarz-Christoffel）

利用Schwarz-Christoffel公式，上半平面可以共形映射到任意多边形内部。

## 应用

- **空气动力学**：机翼剖面的共形映射
- **电子工程**：传输线理论
- **图像处理**：形状配准和变形
- **统计物理**：Schramm-Loewner演化
- **复动力系统**：Julia集和Mandelbrot集

## 相关概念

- [共形映射 (Conformal Map)](./conformal-map.md)：保持角度的映射
- [单连通 (Simply Connected)](./simply-connected.md)：无洞的区域
- [Montel定理 (Montel's Theorem)](./montel-theorem.md)：全纯函数族的紧性
- [Schwarz引理 (Schwarz Lemma)](./schwarz-lemma.md)：圆盘上的约束
- [Carathéodory定理 (Carathéodory's Theorem)](./caratheodory-theorem.md)：边界对应

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 6]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 8]

### 历史文献

- [Riemann. Grundlagen für eine allgemeine Theorie der Funktionen einer veränderlichen complexen Grösse. 1851]
- [Carathéodory. Untersuchungen über die konformen Abbildungen von festen und veränderlichen Gebieten. 1912]

### 在线资源

- [Mathlib4 文档 - Conformal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Conformal/Basic.html)
- [Wikipedia - Riemann Mapping Theorem](https://en.wikipedia.org/wiki/Riemann_mapping_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
