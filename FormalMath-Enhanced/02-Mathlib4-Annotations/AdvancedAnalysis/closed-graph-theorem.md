---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 闭图像定理 (Closed Graph Theorem)
---
# 闭图像定理 (Closed Graph Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.Banach

namespace Analysis

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace E] [CompleteSpace F]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- 闭图像定理：Banach 空间之间的线性映射若图像闭则必连续 -/
theorem closed_graph {T : E → F} (hT : LinearMap 𝕜 E F T) (hgraph : IsClosed {p : E × F | p.2 = T p.1}) :
    Continuous T := by
  -- 利用开映射定理于乘积空间到 E 的投影
  sorry

end Analysis
```

## 数学背景

闭图像定理是泛函分析中与开映射定理、Hahn-Banach 定理并列的核心结果之一。该定理断言：若 $T$ 是从 Banach 空间 $E$ 到 Banach 空间 $F$ 的线性映射，且其图像 $\{(x, Tx) : x \in E\}$ 在乘积空间 $E \times F$ 中是闭集，则 $T$ 必为连续映射。

## 直观解释

闭图像定理提供了一个判断线性算子连续性的巧妙方法。在有限维空间中，任何线性映射都是自动连续的，但在无限维空间中这不再成立。闭图像定理告诉我们：如果一个线性算子 $T$ 的图像（即所有输入-输出对的集合 $\{(x, Tx)\}$）在乘积拓扑下是闭的，那么 $T$ 就一定是连续的。

## 形式化表述

设 $E$ 和 $F$ 是 Banach 空间，$T: E \to F$ 是线性映射。若 $T$ 的图像：

$$\text{Graph}(T) = \{(x, Tx) \in E \times F : x \in E\}$$

在 $E \times F$ 中是闭集，则 $T$ 是连续映射。

等价表述：若对任意序列 $\{x_n\} \subseteq E$，$x_n \to x$ 且 $Tx_n \to y$ 蕴含着 $y = Tx$，则 $T$ 连续。

其中：

- $E \times F$ 配备乘积范数
- 闭图像条件比直接证明连续性更弱，但结合完备性后二者等价
- 该定理是开映射定理的直接推论

## 证明思路

1. **图像空间**：$\text{Graph}(T)$ 是 $E \times F$ 的线性子空间，且由假设是闭的，因此它本身是一个 Banach 空间
2. **投影映射**：考虑投影 $\pi_E: \text{Graph}(T) \to E$，$\pi_E(x, Tx) = x$。这是连续双射线性映射
3. **开映射定理**：由开映射定理的逆映射定理形式，$\pi_E^{{-1}}$ 是连续的
4. **连续性传递**：$T = \pi_F \circ \pi_E^{{-1}}$ 是两个连续映射的复合，故连续

核心洞察在于图像的闭性使得图像空间成为 Banach 空间，从而可以应用开映射定理。

## 示例

### 示例 1：微分算子

考虑 $T = \frac{d}{dx}: C^1([0,1]) \to C([0,1])$。若赋予 $C^1$ 以图范数，则 $T$ 的图像闭且 $T$ 连续。但若 $C^1$ 仅赋予上确界范数，则 $T$ 不连续且图像不闭。

### 示例 2：无界算子的闭延拓

在量子力学中，许多算子（如位置算子和动量算子）在 $L^2$ 上不是处处定义的有界算子。闭图像定理的弱化形式用于研究这类无界算子的闭延拓和自伴性。

### 示例 3：分布理论

在 Schwartz 分布理论中，许多微分算子可以延拓为 $\mathcal{D}'$ 上的连续算子。闭图像定理是验证这类延拓连续性的标准工具。

## 应用

- **偏微分方程**：无界微分算子的闭性和可闭性研究
- **量子力学**：Hilbert 空间上无界算子的自伴延拓理论
- **分布理论**：广义函数空间上微分算子的连续性
- **随机分析**：随机积分和 Malliavin 微积分中的算子闭性
- **控制理论**：无穷维系统观测算子的连续性分析

## 相关概念

- 闭图像 (Closed Graph)：$\{(x, Tx)\}$ 是乘积空间中的闭集
- Banach 空间 (Banach Space)：完备的赋范向量空间
- 开映射定理 (Open Mapping Theorem)：闭图像定理的证明基础
- 无界算子 (Unbounded Operator)：定义域是稠密子空间的线性算子
- 图范数 (Graph Norm)：$||x||_{{\text{graph}}} = ||x|| + ||Tx||$

## 参考

### 教材

- [W. Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 2]
- [M. Reed, B. Simon. Methods of Modern Mathematical Physics I: Functional Analysis. Academic Press, 1980. Chapter III]

### 在线资源

- [Mathlib4 - Banach](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*