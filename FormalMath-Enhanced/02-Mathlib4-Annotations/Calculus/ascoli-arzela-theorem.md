---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Ascoli-Arzelà定理 (Ascoli-Arzelà Theorem)
---
# Ascoli-Arzelà定理 (Ascoli-Arzelà Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Equicontinuity

namespace AscoliArzela

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MetricSpace Y] [CompleteSpace Y]

/-- Ascoli-Arzelà定理 -/
theorem ascoli_arzela (F : Set (X → Y)) (hF₁ : ∀ x, CompactClosure {f x | f ∈ F})
    (hF₂ : EquicontinuousAt F) :
    CompactClosure F := by
  -- 利用等度连续性和逐点紧致性证明函数族紧致
  sorry

/-- 经典形式：一致有界等度连续函数族相对紧致 -/
theorem ascoli_arzela_classic (F : Set (C(X, Y))) (hbounded : ∃ M, ∀ f ∈ F, ∀ x, dist (f x) 0 ≤ M)
    (hequi : UniformEquicontinuous F) :
    IsCompact (closure F) := by
  -- 在C(X,Y)中证明相对紧致
  sorry

end AscoliArzela
```

## 数学背景

Ascoli-Arzelà定理由意大利数学家朱利奥·阿斯科利（Giulio Ascoli，1883年）和切萨雷·阿尔泽拉（Cesare Arzelà，1889年）发展完善。这是函数空间理论中最重要的紧性判别法，给出了连续函数空间中集合列紧的充分必要条件，在微分方程、变分法和泛函分析中有核心应用。

## 直观解释

Ascoli-Arzelà定理告诉我们：**在紧致空间上，一致有界且"同步连续"的函数族是紧致的**。就像一组协调良好、变化范围有限的"表演者"，总能找到一个收敛的子序列。"等度连续性"确保所有函数以相似的"速度"变化，没有"突变者"。

## 形式化表述

设 $X$ 是紧致度量空间，$Y$ 是完备度量空间，$\mathcal{F} \subset C(X, Y)$。

**Ascoli-Arzelà定理**：$\mathcal{F}$ 相对紧致（在一致拓扑下）当且仅当：
1. **逐点相对紧致**：对每个 $x \in X$，$\{f(x) : f \in \mathcal{F}\}$ 在 $Y$ 中相对紧致
2. **等度连续**：$\mathcal{F}$ 是等度连续的

当 $Y = \mathbb{R}^n$ 时，条件1等价于一致有界。

## 证明思路

1. **必要性**：紧致集的子集有界，连续映射保持等度连续性
2. **充分性**：
   - 对角线法构造收敛子列
   - 利用等度连续性证明一致收敛
   - 完备性保证极限连续
3. **关键步骤**：可数稠密集上的逐点收敛 + 等度连续性 = 一致收敛

## 示例

### 示例 1：Lipschitz函数族

设 $\mathcal{F} = \{f: [0,1] \to \mathbb{R} : |f(x) - f(y)| \leq L|x - y|, |f(x)| \leq M\}$

等度连续（Lipschitz常数一致），一致有界，故相对紧致。

### 示例 2：微分方程解族

初值问题 $y' = f(t, y)$ 的解族，若 $f$ 满足Lipschitz条件，则解族等度连续。

结合先验估计得到紧性，用于证明存在性。

## 应用

- **常微分方程**：Peano存在性定理
- **偏微分方程**：紧性方法、Sobolev嵌入
- **变分法**：极小化序列的收敛
- **复分析**：Montel定理（全纯函数族）
- **逼近理论**：多项式逼近

## 相关概念

- 等度连续性：函数族"同步连续"的概念
- 紧性 (Compactness)：拓扑空间的基本性质
- 函数空间：连续函数构成的空间
- Montel定理：全纯函数的紧性判别

## 参考

### 教材

- [Dunford & Schwartz. Linear Operators, Part I. Wiley, 1958. Chapter 4]
- [Lang. Real and Functional Analysis. Springer, 3rd edition, 1993. Chapter 3]

### 历史文献

- [Ascoli. Le curve limite di una varietà data di curve. 1883-1884]
- [Arzelà. Sulle funzioni di linee. 1889]

### 在线资源

- [Mathlib4 文档 - Equicontinuity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Equicontinuity.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
