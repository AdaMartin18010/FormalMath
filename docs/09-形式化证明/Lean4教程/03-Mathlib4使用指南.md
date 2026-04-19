---
title: "Mathlib4使用指南"
msc_primary: "03"
msc_secondary:
  - 03B35
  - 68T15
processed_at: '2026-04-20'
---

# Mathlib4 使用指南

## 引言

[Mathlib4](https://github.com/leanprover-community/mathlib4) 是 Lean 4 生态系统中最大、最全面的数学库，涵盖代数、分析、几何、数论、组合、概率统计等几乎所有现代数学分支。截至 2026 年，Mathlib4 已包含超过 100 万行 Lean 代码和 15 万条定理。本指南介绍 Mathlib4 的核心模块、查找定理的方法、典型证明模式以及贡献规范。

---

## 1. 基础导入与模块结构

### 1.1 核心代数模块

```lean
import Mathlib.Algebra.Group.Basic      -- 群、幺半群、半群
import Mathlib.Algebra.Ring.Basic       -- 环、域
import Mathlib.Algebra.Field.Basic      -- 域的进阶性质
import Mathlib.Algebra.Module.Basic     -- 模、向量空间
import Mathlib.Algebra.Algebra.Basic    -- 代数结构
```

### 1.2 分析学模块

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic      -- 导数基础
import Mathlib.Analysis.Calculus.ContDiff.Basic   -- 高阶可微
import Mathlib.Analysis.SpecialFunctions.Exp      -- 指数函数
import Mathlib.Analysis.SpecialFunctions.Log      -- 对数函数
import Mathlib.Analysis.NormedSpace.Basic         -- 赋范空间
import Mathlib.MeasureTheory.Integral.Bochner     -- Bochner 积分
```

### 1.3 数论与组合

```lean
import Mathlib.NumberTheory.Divisors        -- 因子、整除
import Mathlib.NumberTheory.Primes          -- 素数理论
import Mathlib.Combinatorics.SimpleGraph.Basic  -- 简单图
```

### 1.4 拓扑与集合论

```lean
import Mathlib.Topology.Basic               -- 拓扑空间
import Mathlib.Topology.MetricSpace.Basic   -- 度量空间
import Mathlib.SetTheory.Ordinal.Basic      -- 序数
```

---

## 2. 定理查找与证明搜索

### 2.1 使用 `#check` 和 `#print`

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

#check Nat.add_comm              -- ∀ (n m : ℕ), n + m = m + n
#check Real.exp_add              -- ∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y

-- 查看定理的完整证明（若可访问）
#print Nat.add_comm
```

### 2.2 使用 `#find`

`#find` 可根据模式搜索库中的定理：

```lean
#find _ + _ = _ + _              -- 搜索交换律或结合律相关
#find _ * (_ + _) = _            -- 搜索分配律相关
```

### 2.3 使用 Loogle（在线搜索）

[Loogle](https://loogle.lean-lang.org/) 是在线 Mathlib 搜索引擎，支持按类型签名搜索：

```
Real.exp ?x → Real.exp ?y = Real.exp (?x + ?y)
```

### 2.4 命名约定速查

Mathlib 的命名遵循严格的约定，可据此猜测定理名：

| 模式 | 含义 | 例子 |
|------|------|------|
| `add_comm` | 加法交换律 | `Nat.add_comm`, `Real.add_comm` |
| `mul_assoc` | 乘法结合律 | `mul_assoc` |
| `le_trans` | 不等式传递 | `le_trans` |
| `deriv_id` | 恒等函数的导数 | `deriv_id''` |
| `continuous_add` | 加法的连续性 | `Continuous.add` |

---

## 3. 典型证明模式

### 3.1 使用 `calc` 进行等式推导

```lean
import Mathlib.Data.Real.Basic

example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := by rw [h1]
    _ = c := by rw [h2]
```

### 3.2 使用 `linarith` 和 `nlinarith`

```lean
import Mathlib.Data.Real.Basic

example (x y : ℝ) (h1 : x + 2*y ≤ 3) (h2 : 2*x - y ≤ 1) : x ≤ 1 := by
  linarith   -- 线性算术自动求解

example (x : ℝ) (h : x^2 + 2*x + 1 = 0) : x = -1 := by
  have : (x + 1)^2 = 0 := by linarith
  have : x + 1 = 0 := by apply pow_eq_zero ; exact this
  linarith
```

### 3.3 使用 `simp` 和 `ring`

```lean
import Mathlib.Algebra.Ring.Basic

example (R : Type*) [CommRing R] (a b : R) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring    -- 环的自动化简化

example (n : ℕ) : n + 0 = n := by
  simp    -- 使用 simp-lemma 数据库自动简化
```

### 3.4 连续性证明

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic

-- 证明 f(x) = x^2 在 x=3 处可导
example : DifferentiableAt ℝ (fun x : ℝ => x^2) 3 := by
  apply DifferentiableAt.pow
  exact differentiableAt_id'
```

---

## 4. 常用定理速查表

### 4.1 自然数与整数

| 定理 | 类型签名 | 说明 |
|------|---------|------|
| `Nat.add_comm` | `∀ n m, n + m = m + n` | 加法交换律 |
| `Nat.mul_comm` | `∀ n m, n * m = m * n` | 乘法交换律 |
| `Nat.gcd_dvd_left` | `∀ a b, Nat.gcd a b ∣ a` | 最大公约数整除性 |
| `Nat.Prime.irreducible` | 素数不可约 | 素数定义推论 |

### 4.2 实分析与微积分

| 定理 | 类型签名 | 说明 |
|------|---------|------|
| `Real.exp_add` | `∀ x y, exp (x+y) = exp x * exp y` | 指数加法公式 |
| `Real.log_mul` | `∀ x y, 0 < x → 0 < y → log (x*y) = log x + log y` | 对数乘法公式 |
| `hasDerivAt_id` | `∀ x, HasDerivAt id 1 x` | 恒等函数导数为 1 |
| `HasDerivAt.add` | 导数的加法性 | 和函数的导数 |

### 4.3 群论与代数

| 定理 | 类型签名 | 说明 |
|------|---------|------|
| `mul_inv_cancel` | `∀ a, a ≠ 0 → a * a⁻¹ = 1` | 乘法逆元 |
| `inv_inv` | `∀ a, (a⁻¹)⁻¹ = a` | 逆元的逆元 |
| `Subgroup.normal_core` | 子群的核 | 正规子群构造 |

---

## 5. 高级技巧

### 5.1 类型类推断（Type Class Inference）

Mathlib 大量使用类型类来管理数学结构：

```lean
-- 自动推断群结构
example (G : Type*) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  simp [mul_inv_rev]

-- 自动推断拓扑空间上的连续性
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : Continuous f := hf
```

### 5.2 使用 `library_search` 和 `exact?`

Lean 4 提供自动搜索库中匹配定理的策略：

```lean
example (n m : ℕ) : n + m = m + n := by
  exact?    -- 自动找到 Nat.add_comm
```

### 5.3 使用 `aesop` 自动化证明

`aesop` 是 Mathlib 中强大的自动化证明搜索策略：

```lean
import Aesop

example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  aesop    -- 自动构造传递性推导
```

---

## 6. 贡献指南

1. **阅读 [Mathlib4 贡献文档](https://leanprover-community.github.io/contribute/index.html)**：了解编码风格、命名约定、PR 流程。
2. **遵循 [Style Guide](https://leanprover-community.github.io/contribute/style.html)**：
   - 每行不超过 100 字符；
   - 使用两个空格缩进；
   - 定理命名使用 `snake_case`；
   - 类型参数使用大写字母（如 `α`, `β`, `M`, `N`）。
3. **编写详细文档字符串**：每个公开定义和定理应有 `/-- ... -/` 文档。
4. **提交 PR 前检查 CI**：运行 `lake build` 和 `lake exe cache get` 确保本地编译通过。

---

## 7. 与已有文档的关联

- [Lean4 证明策略指南](01-证明策略指南.md)：Mathlib4 中具体证明策略的深入讲解。
- [Lean4 常见错误与调试](02-常见错误与调试.md)：类型错误、 universe 层级问题的诊断。
- [Mathlib4 代数结构速查](../mathlib-algebra-cheatsheet.md)：更详细的代数模块索引。

---

## 参考文献

1. The Mathlib4 Community, *Mathlib4 Documentation*, https://leanprover-community.github.io/mathlib4_docs/
2. J. Avigad, et al., *Theorem Proving in Lean 4*, https://lean-lang.org/theorem_proving_in_lean4/
3. P. Massot, *Lean for the Curious Mathematician*, https://leanprover-community.github.io/lftcm2020/

---

**适用**：docs/09-形式化证明/Lean4教程/
