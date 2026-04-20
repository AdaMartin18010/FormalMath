---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Sard定理 (Sard's Theorem)
---
# Sard定理 (Sard's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace SardTheorem

variable {M N : Type*} [SmoothManifoldWithCorners (𝓡 m) M] [SmoothManifoldWithCorners (𝓡 n) N]
variable {f : M → N} [ContMDiff ℝ ∞ f]

/-- Sard定理：光滑映射临界值的测度为零 -/
theorem sard_theorem (hmn : m ≤ n) :
    MeasureZero (HausdorffMeasure n) (CriticalValues f) := by
  -- 局部化和Fubini论证
  sorry

/-- 光滑映射的正则值稠密 -/
theorem regular_values_dense :
    Dense (RegularValues f) := by
  -- Sard定理的推论
  sorry

end SardTheorem
```

## 数学背景

Sard定理由美国数学家Arthur Sard于1942年证明，是微分拓扑学中最基本、最重要的结果之一。它从测度论的角度回答了"光滑映射的像集有多大"这一基本问题，表明在适当意义下，光滑映射的"坏"值（临界值）集合"很小"（测度为零），从而"好"值（正则值）在目标空间中稠密。

### 临界值与正则值

**定义（临界点与临界值）**：设 $f: M \to N$ 是光滑流形之间的光滑映射，$\dim M = m$，$\dim N = n$。点 $p \in M$ 称为**临界点**（critical point），如果微分 $df_p: T_p M \to T_{f(p)} N$ 不是满射。等价地，当 $m \geq n$ 时，$p$ 是临界点当且仅当 $\text{rank}(df_p) < n$；当 $m < n$ 时，所有点都是临界点。

若 $p \in M$ 不是临界点，则称它为**正则点**（regular point）。

值 $q \in N$ 称为**临界值**（critical value），如果存在临界点 $p \in f^{-1}(q)$。值 $q$ 称为**正则值**（regular value），如果它不是临界值。注意：正则值可以是像集之外的点（ vacuously regular）。

### 测度零集

在流形上，**测度零集**（set of measure zero）是指在每个坐标卡下对应于欧氏空间中Lebesgue测度为零的集合。具体地，子集 $S \subseteq N$ 有测度零，如果存在 $N$ 的坐标卡图册 $\{(U_\alpha, \phi_\alpha)\}$，使得对每个 $\alpha$，$\phi_\alpha(S \cap U_\alpha) \subseteq \mathbb{R}^n$ 的Lebesgue测度为零。

## Sard定理的陈述

**定理（Sard）**：设 $f: M \to N$ 是 $C^r$ 映射，其中 $r \geq \max\{1, m-n+1\}$（特别地，$C^\infty$ 光滑映射总是满足条件）。则 $f$ 的临界值集合在 $N$ 中测度为零。

**推论**：正则值集合在 $N$ 中稠密（且是剩余集，即包含可数多个开稠密集的交）。

### 定理的适用范围

- 若 $m < n$，则每个点都是临界点，Sard定理断言整个像集 $f(M)$ 在 $N$ 中测度为零。这直观上合理，因为低维流形到高维流形的像不可能"填满"目标空间。
- 若 $m = n$，临界值是使Jacobian行列式为零的那些值。Sard定理说这些值构成零测集。
- 若 $m > n$，临界值对应于映射"折叠"或"塌缩"的方向，Sard定理保证这些"折叠"的像不会占据正测度。

## 证明概要

Sard定理的证明通常采用局部化策略，将问题约化到欧氏空间之间的映射，然后使用归纳法和Fubini论证。

### 第一步：局部化

利用流形的第二可数性，只需证明对每个坐标卡中的映射成立。因此假设 $f: U \to \mathbb{R}^n$，其中 $U \subseteq \mathbb{R}^m$ 是开集。

### 第二步：归纳法

对维数 $m$ 进行归纳。定义**k阶临界点集**：

$$C_k = \{x \in U : D^\alpha f(x) = 0 \text{ 对所有 } 1 \leq |\alpha| \leq k\}$$

即 $C_k$ 是所有直到 $k$ 阶导数都为零的点集。有包含链：

$$C \supseteq C_1 \supseteq C_2 \supseteq \cdots$$

其中 $C = C_1$ 是临界点集。

### 第三步：关键引理

**引理1**：$f(C \setminus C_1)$ 测度为零。

证明思路：若 $x \in C \setminus C_1$，则存在某个一阶偏导数非零。由隐函数定理，可以在 $x$ 附近将 $f$ 表示为先投影再复合的形式，然后对 $m-1$ 维截面应用归纳假设。

**引理2**：对 $k \geq 1$，$f(C_k \setminus C_{k+1})$ 测度为零。

证明类似：利用某个 $k+1$ 阶导数非零，局部地将 $C_k$ 表示为更低维子流形，然后应用归纳。

**引理3**：对充分大的 $k$（$k > m/n - 1$），$f(C_k)$ 测度为零。

这是证明中最技术性的部分，利用Taylor展开和映射的Lipschitz性质，证明 $f$ 在 $C_k$ 上的像可以被体积任意小的集合覆盖。

### 第四步：组合结果

由于 $C = (C \setminus C_1) \cup (C_1 \setminus C_2) \cup \cdots \cup (C_{k-1} \setminus C_k) \cup C_k$，每个部分的像测度为零，因此 $f(C)$ 测度为零。 $\square$

## 例子

### 例子1：一元实函数

设 $f: \mathbb{R} \to \mathbb{R}$ 是光滑函数。临界点满足 $f'(x) = 0$。Sard定理断言 $\{f(x) : f'(x) = 0\}$ 的Lebesgue测度为零。

例如，$f(x) = x^3 - 3x$ 有临界点 $x = \pm 1$，临界值为 $f(1) = -2$ 和 $f(-1) = 2$。有限集当然测度为零。

更复杂的例子：$f(x) = e^{-1/x^2}\sin(1/x)$（$x \neq 0$，$f(0)=0$）有无穷多个临界点，但其临界值集合仍然可数（从而测度为零）。

### 例子2：从 $\mathbb{R}$ 到 $\mathbb{R}^2$ 的映射

设 $f: \mathbb{R} \to \mathbb{R}^2$，$f(t) = (\cos t, \sin t)$。这里 $m=1 < n=2$，所有点都是临界点。Sard定理断言像集（单位圆）在 $\mathbb{R}^2$ 中测度为零，这是显然的（一维曲线不可能填充平面区域）。

### 例子3：Whitney折叠映射

经典的Whitney折叠映射 $f: \mathbb{R}^2 \to \mathbb{R}^2$：

$$f(x, y) = (x^2, y)$$

Jacobi矩阵为 $Df = \begin{pmatrix} 2x & 0 \\ 0 & 1 \end{pmatrix}$，临界点满足 $x = 0$（即 $y$ 轴）。临界值集合是 $f(\{0\} \times \mathbb{R}) = \{(0, y) : y \in \mathbb{R}\}$，即 $x=0$ 的直线。这条直线在 $\mathbb{R}^2$ 中测度为零。

### 例子4：Morse函数

Morse函数是指所有临界点都是非退化（Hessian矩阵非奇异）的光滑函数。对Morse函数 $f: M \to \mathbb{R}$，临界点是孤立的，临界值集合是离散的，当然测度为零。Morse理论利用这一性质通过分析临界点来研究流形的拓扑。

## 应用

### 1. 横截性定理

Sard定理是证明各种横截性定理的基础工具。横截性定理断言：给定光滑映射 $f: M \to N$ 和子流形 $W \subseteq N$，通过 $f$ 的小扰动可以使 $f$ 横截于 $W$。证明中需要利用Sard定理说明非横截的扰动参数构成零测集。

### 2. Whitney嵌入定理

Whitney嵌入定理断言任何 $m$ 维光滑流形都可以光滑嵌入到 $\mathbb{R}^{2m}$ 中。证明的关键步骤是利用Sard定理说明"坏"的嵌入方向（导致自交或奇异的投影方向）构成测度零集，因此"好"的嵌入方向稠密存在。

### 3. Morse理论

Morse理论研究光滑函数的临界点与流形拓扑的关系。Sard定理保证正则值稠密，这允许Morse理论在正则值处分析流形的水平集（level sets）的变化。临界值虽然存在，但由于它们测度为零，流形的整体拓扑可以通过正则值处的纤维来理解。

### 4. 度数理论

在代数拓扑中，映射的Brouwer度数或映射度（mapping degree）通常只对正则值定义。Sard定理保证正则值存在且稠密，从而使度数的定义良好。例如，对光滑映射 $f: S^n \to S^n$，度数 $\deg(f)$ 可以通过计算任意正则值的原像个数（带符号）来定义。

### 5. 参数化定理与隐函数定理的加强

Sard定理与隐函数定理结合，可以用来证明各种参数化解的存在性结果。在经济学中，Sard定理被用来证明一般均衡的存在性和正则经济的稠密性（Debreu定理）。在微分方程理论中，Sard型结果用于证明一般参数下方程的解具有良好的正则性。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
