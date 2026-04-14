---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Lefschetz 不动点定理 (Lefschetz Fixed-Point Theorem)
---
# Lefschetz 不动点定理 (Lefschetz Fixed-Point Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SimplicialSet

namespace AlgebraicTopology

variable {X : Type*} [TopologicalSpace X] [TriangulableSpace X] [CompactSpace X]

/-- Lefschetz 不动点定理：若 Lefschetz 数非零，则映射必有不动点 -/
theorem lefschetz_fixed_point {f : C(X, X)}
    (hL : LefschetzNumber f ≠ 0) :
    ∃ x : X, f x = x := by
  -- 利用单纯逼近、链映射的迹和 Hopf 迹公式证明
  sorry

end AlgebraicTopology
```

## 数学背景

Lefschetz 不动点定理是代数拓扑中关于连续映射不动点存在性的基本结果，由美国数学家所罗门·莱夫谢茨（Solomon Lefschetz）在20世纪20年代证明。该定理断言：设 $f: X \to X$ 是紧致可三角剖分空间上的连续映射。定义 $f$ 的 Lefschetz 数为：

$$\Lambda(f) = \sum_{{n=0}}^{{\dim X}} (-1)^n \text{tr}(f_* : H_n(X; \mathbb{Q}) \to H_n(X; \mathbb{Q}))$$

若 $\Lambda(f) \neq 0$，则 $f$ 至少有一个不动点（即存在 $x \in X$ 使得 $f(x) = x$）。Lefschetz 不动点定理是 Brouwer 不动点定理的高维推广，在动力系统、经济学（博弈论中的纳什均衡）和微分方程中具有广泛应用。

## 直观解释

Lefschetz 不动点定理提供了一个计算不动点是否存在的方法，而无需显式求解方程 $f(x) = x$。想象你有一个复杂的连续变换 $f$ 作用在一个空间上。直接找不动点可能极其困难，但 Lefschetz 定理告诉我们：你可以转而计算一个更容易处理的数值——Lefschetz 数。这个数是同调群上诱导映射的迹的交错和。如果这个数不为零，那么不动点一定存在！这就像通过计算一个空间的总体积来判断里面是否一定有某个特定类型的物体，而不需要逐个检查每个角落。特别地，当 $f$ 是恒等映射时，$\Lambda(f) = \chi(X)$（Euler 示性数），所以 Lefschetz 数可以看作是 Euler 示性数的推广。

## 形式化表述

设 $X$ 是紧致可三角剖分空间（如紧致流形或有限 CW 复形），$f: X \to X$ 是连续映射。$f$ 的 **Lefschetz 数** 定义为：

$$\Lambda(f) = \sum_{{n=0}}^{{\infty}} (-1)^n \text{tr}(f_{*n})$$

其中 $f_{*n}: H_n(X; \mathbb{Q}) \to H_n(X; \mathbb{Q})$ 是 $f$ 在 $n$ 维有理同调群上诱导的线性映射，$\text{tr}$ 表示矩阵的迹（不依赖于基的选择）。

**Lefschetz 不动点定理**：若 $\Lambda(f) \neq 0$，则 $f$ 必有不动点，即：

$$\exists x \in X, \quad f(x) = x$$

更精确的形式（Lefschetz-Hopf 定理）：若所有不动点都是孤立的，则：

$$\Lambda(f) = \sum_{{x = f(x)}} \text{ind}_f(x)$$

其中 $\text{ind}_f(x)$ 是不动点 $x$ 处的 Lefschetz 指数。

其中：

- 当 $f = \text{id}_X$ 时，$\Lambda(f) = \chi(X)$（Euler 示性数）
- 若 $X$ 是可缩空间（如闭球），$H_0 = \mathbb{Q}$，其余为 0，故 $\Lambda(f) = 1 \neq 0$，这推出 Brouwer 不动点定理
- Lefschetz 指数可以用 Jacobian 行列式或局部度数来计算

## 证明思路

1. **单纯逼近**：将 $f$ 用单纯映射 $g$ 逼近（由于 $X$ 可三角剖分）
2. **Hopf 迹公式**：对链复形上的链映射 $g_\bullet: C_\bullet(X) \to C_\bullet(X)$，有 $\sum (-1)^n \text{tr}(g_n) = \sum (-1)^n \text{tr}(g_{*n})$。左边可在单形层面计算
3. **不动点计数**：若 $g$ 无不动点，则每个单形被 $g$ 移到别处，链映射的迹为零，故 $\Lambda(f) = 0$
4. **反证法**：若 $f$ 无不动点，则任何足够好的单纯逼近也无不动点，这与 $\Lambda(f) \neq 0$ 矛盾

核心洞察在于同调层面上的迹（全局不变量）可以通过链层面的局部贡献来计算。

## 示例

### 示例 1：Brouwer 不动点定理

设 $D^n$ 是 $n$ 维闭球，$f: D^n \to D^n$ 连续。由于 $D^n$ 可缩，$H_0(D^n) = \mathbb{Q}$，$H_k(D^n) = 0$（$k > 0$）。故 $\Lambda(f) = \text{tr}(f_{*0}) = 1 \neq 0$，由 Lefschetz 定理，$f$ 必有不动点。

### 示例 2：环面上的旋转

设 $f: T^2 \to T^2$ 是 $f(z_1, z_2) = (e^{{i\theta_1}} z_1, e^{{i\theta_2}} z_2)$。$f_{*1}$ 是恒等映射（迹为 2），$f_{*2}$ 也是恒等映射（迹为 1）。故 $\Lambda(f) = 1 - 2 + 1 = 0$。事实上，当 $\theta_1, \theta_2$ 都是无理数倍 $2\pi$ 时，$f$ 无不动点。

### 示例 3：球面上的对径映射

设 $f: S^{2n} \to S^{2n}$ 是对径映射 $f(x) = -x$。$f_{*k}$ 在 $k = 0, 2n$ 上分别是 $1$ 和 $(-1)^{{2n+1}} = -1$。故 $\Lambda(f) = 1 + (-1) = 0$，所以没有不动点，与事实一致（对径映射无不动点）。

## 应用

- **动力系统**：周期轨道的存在性和 Poincaré-Birkhoff 定理
- **博弈论**：Nash 均衡存在性证明的拓扑基础
- **偏微分方程**：非线性方程解的存在性（如 Leray-Schauder 不动点定理）
- **代数几何**：Frobenius 映射的不动点和 Weil 猜想
- **数论**：p-adic 分析和 p-adic 动力系统

## 相关概念

- Lefschetz 数 (Lefschetz Number)：诱导映射迹的交错和
- Euler 示性数 (Euler Characteristic)：恒等映射的 Lefschetz 数
- 不动点指数 (Fixed-Point Index)：局部不动点的带符号计数
- Brouwer 不动点定理 (Brouwer Fixed-Point Theorem)：Lefschetz 定理的特例
- Hopf 迹公式 (Hopf Trace Formula)：链复形上的迹关系

## 参考

### 教材

- [A. Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2C]
- [J. W. Vick. Homology Theory. Springer, 2nd edition, 1994. Chapter 6]

### 在线资源

- [Mathlib4 - SimplicialSet](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
