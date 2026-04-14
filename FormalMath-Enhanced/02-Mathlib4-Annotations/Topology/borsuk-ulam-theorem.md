---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Borsuk-Ulam 定理 (Borsuk-Ulam Theorem)
---
# Borsuk-Ulam 定理 (Borsuk-Ulam Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.HomotopyGroup

namespace AlgebraicTopology

variable {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ^n}

/-- Borsuk-Ulam 定理：从 S^n 到 R^n 的连续映射必将某对对径点映到同一点 -/
theorem borsuk_ulam (hf : Continuous f) :
    ∃ x : Fin (n + 1) → ℝ, ‖x‖ = 1 ∧ f x = f (-x) := by
  -- 利用映射度或上同调环的结构证明
  sorry

end AlgebraicTopology
```

## 数学背景

Borsuk-Ulam 定理由波兰数学家卡齐米日·博尔苏克（Kazimierz Borsuk）于1933年证明，是代数拓扑学中最优美、应用最广泛的结果之一。该定理断言：对于从 n 维球面 S^n 到 n 维欧氏空间 R^n 的任意连续映射，总存在一对对径点（antipodal points）被映射到同一点。这个看似简单的结论蕴含着深刻的几何和组合意义，是代数拓扑中不动点理论、映射度理论和组合几何的交汇点。

## 直观解释

Borsuk-Ulam 定理有一个著名的通俗表述：在地球表面（S^2）上任取两个连续变化的量（如温度和气压，对应于一个到 R^2 的映射），总存在一对对径点（地球直径的两端）具有完全相同的温度和气压。更一般地，n 维球面上任何 n 个连续变化的环境参数，总有一对对径点在所有参数上都完全相同。

## 形式化表述

设 f: S^n → R^n 是连续映射，其中 S^n = \{x \in R^{n+1} : ||x|| = 1\} 是 n 维单位球面，则存在 x \in S^n 使得：

$$f(x) = f(-x)$$

等价表述：

1. 不存在连续的对径保持映射 g: S^n → S^{n-1}
2. （Lusternik-Schnirelmann）若 S^n 被 n+1 个闭集覆盖，则至少有一个闭集包含一对对径点
3. 任何连续映射 f: S^n → R^n 都不是单射

其中：

- S^n 是 R^{n+1} 中的 n 维单位球面
- 对径点（antipodal points）是指满足 y = -x 的点对 (x, y)
- n = 1 时，定理等价于介值定理：圆周上连续函数必有某对对径点函数值相等

## 证明思路

1. **归纳法**：对 n 进行归纳，利用代数拓扑工具
2. **映射度/上同调**：假设不存在这样的对径点，则 f(x) - f(-x) 定义了一个从 S^n 到 R^n \setminus \{0\} 的连续对径映射
3. **投影到球面**：将 f(x) - f(-x) 单位化，得到一个对径保持映射 g: S^n → S^{n-1}
4. **拓扑阻碍**：利用 S^n 和 S^{n-1} 的上同调环（或映射度）证明这样的对径保持映射不可能存在，矛盾

核心洞察在于球面的拓扑复杂度（用同调或映射度衡量）不允许被低维球面对径保持地覆盖。

## 示例

### 示例 1：地球上必有对径点温度相同

将地球表面建模为 S^2，温度 T 和气压 P 定义连续映射 f: S^2 → R^2，f(x) = (T(x), P(x))。由 Borsuk-Ulam 定理，存在对径点 x, -x 使得 T(x) = T(-x) 且 P(x) = P(-x)。

### 示例 2：Ham Sandwich 定理

在 R^n 中给定 n 个具有有限测度的物体，总存在一个超平面同时将它们的体积平分。这是 Borsuk-Ulam 定理在测度论中的直接推论。

### 示例 3：图着色与 Kneser 猜想

Kneser 图 KG_{n,k} 的色数恰好为 n - 2k + 2。Lovász 在1978年利用 Borsuk-Ulam 定理给出了这一著名猜想的证明，开创了拓扑组合学的新领域。

## 应用

- **组合几何**：Ham Sandwich 定理、Lovász 的 Kneser 图着色定理
- **博弈论**：公平分配问题和 Nash 均衡的存在性
- **经济学**：社会选择理论和投票悖论
- **气象学与地理学**：对径点上的环境参数对称性
- **拓扑组合学**：拓扑方法在离散数学中的应用

## 相关概念

- 对径映射 (Antipodal Map)：A(x) = -x
- 映射度 (Mapping Degree)：拓扑映射的代数不变量
- 上同调环 (Cohomology Ring)：代数拓扑中的核心工具
- Ham Sandwich 定理：Borsuk-Ulam 的几何推论
- Lusternik-Schnirelmann 定理：用覆盖刻画球面的拓扑性质

## 参考

### 教材

- [A. Hatcher. Algebraic Topology. Cambridge, 2002. Section 2.2]
- [J. Matoušek. Using the Borsuk-Ulam Theorem. Springer, 2003]

### 在线资源

- [Mathlib4 - Homotopy Group](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*