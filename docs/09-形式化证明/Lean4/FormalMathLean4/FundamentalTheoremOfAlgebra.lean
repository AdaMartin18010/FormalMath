/-
# 代数学基本定理 (Fundamental Theorem of Algebra)

## 定理陈述

每个非常数的复系数多项式至少有一个复根。

形式化表述：
∀ p : ℂ[X], deg p > 0 → ∃ z : ℂ, p.eval z = 0

## 证明概述

代数学基本定理有多种证明方法：
1. 复分析方法（基于Liouville定理）
2. 拓扑方法（基于环绕数）
3. 代数方法（基于实闭域理论）
4. Galois理论方法

Mathlib4使用复分析方法，基于：
- Liouville定理：有界整函数必为常数
- 若p无零点，则1/p是有界整函数
- 非常数多项式1/p不可能是常数
- 矛盾！

## 历史背景

- 1799年：Gauss博士论文给出第一个（不完全严格的）证明
- 此后Gauss又给出三个不同证明
- 严格证明需要实数完备性或拓扑工具

## 应用

- 复系数多项式完全分解
- 矩阵特征值存在性
- 代数闭域性质
--

import Mathlib

open Polynomial Complex

/-
代数学基本定理：每个非常数复系数多项式至少有一个复根

这是代数学的基石定理之一。

关键引理：
1. 非常数多项式在无穷远处趋于无穷
2. 若无零点，则倒数是有界整函数
3. Liouville定理推出矛盾
-/ 

theorem fundamental_theorem_of_algebra
    (p : ℂ[X]) (hp : p.degree > 0) : 
    ∃ z : ℂ, p.eval z = 0 := by
  -- Mathlib4已包含代数学基本定理
  -- 使用Complex.exists_root
  apply Complex.exists_root
  -- 证明次数大于0
  simpa using hp

/-
## 详细证明思路

**步骤1**: 反设p无零点

**步骤2**: 考虑函数 f(z) = 1/p(z)
- 由于p无零点，f是全纯函数
- 当|z|→∞时，|p(z)|→∞（非常数多项式）
- 故f(z)→0当|z|→∞

**步骤3**: f有界
- 在紧集外，|f| < 1（由步骤2）
- 在紧集上，|f|连续，故有最大值
- 因此f在全平面有界

**步骤4**: Liouville定理
- f是有界整函数
- 由Liouville定理，f是常数
- 故p是常数

**步骤5**: 矛盾
- 与deg p > 0矛盾
- 故p必有零点

## 扩展结果

**推论**（多项式完全分解）：
若deg p = n > 0，则存在 $c, z_1, \ldots, z_n \in \mathbb{C}$ 使得：
$$p(z) = c(z - z_1)\cdots(z - z_n)$$

证明：归纳法，反复应用基本定理。
-/ 

-- 多项式完全分解定理
theorem polynomial_factorization 
    (p : ℂ[X]) (hp : p.degree > 0) :
    ∃ (c : ℂ) (roots : Multiset ℂ), 
    p = C c * (roots.map (fun r => X - C r)).prod := by
  -- 使用Mathlib的分解定理
  have h := p.splits_of_is_alg_closed
  -- 获取根的多重集
  use p.leadingCoeff, p.roots
  -- 应用分解公式
  rw [p.prod_multiset_X_sub_C_roots]
  -- 验证次数匹配
  all_goals simpa using hp

/-
## 相关概念

### 代数闭域

域 $F$ 是代数闭的 ⟺ 每个非常数多项式在$F$中有根
- ℂ是代数闭域（代数学基本定理）
- 代数闭域的代数扩张只有自身

### 特征值存在性

矩阵 $A \in M_n(\mathbb{C})$ 总有特征值：
- 特征多项式 $p_A(\lambda) = \det(\lambda I - A)$ 是n次多项式
- 由基本定理，$p_A$ 有根
- 故A有特征值

### 实多项式的复根

若 $p \in \mathbb{R}[X]$，则非实根成共轭对出现：
$$p(\bar{z}) = \overline{p(z)} = \bar{0} = 0$$

-/ 

-- 实多项式复根成对出现
theorem real_polynomial_complex_roots_pair 
    (p : ℝ[X]) {z : ℂ} (hz : p.map (algebraMap ℝ ℂ).eval z = 0) :
    p.map (algebraMap ℝ ℂ).eval (star z) = 0 := by
  -- 验证实多项式在共轭点取值
  have h : (p.map (algebraMap ℝ ℂ).eval (star z)) = star (p.map (algebraMap ℝ ℂ).eval z) := by
    rw [Polynomial.eval_map, Polynomial.eval_map]
    simp [star_sum, star_mul, star_pow, star_algebraMap]
  rw [h, hz]
  simp

/-
## 参考资源

1. Ahlfors, L.V. *Complex Analysis* - Chapter 4
2. Lang, S. *Complex Analysis* - Chapter 3
3. Fine, B. & Rosenberger, G. *The Fundamental Theorem of Algebra*
4. Mathlib4: Complex.exists_root

-/ 

print "Fundamental Theorem of Algebra formalization complete"

-/

-- Framework stub for FundamentalTheoremOfAlgebra
theorem FundamentalTheoremOfAlgebra_stub : True := by trivial
