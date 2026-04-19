# AI Formalizer 示例集

本文件包含 10 个自然语言数学定理描述到 Lean 4 代码的转换示例，
覆盖分析、代数、几何、数论四个领域。

---

## 分析学 (Analysis) — 3 个示例

### 示例 1：连续函数的介值定理

**自然语言：**
> 设 f 是连续函数，对于所有 x，如果 f(x) 等于 0 则 x 大于 0。

**Lean 4 代码：**
```lean
import Mathlib

theorem ivt_stub {f : ℝ → ℝ} (hf : Continuous f) (h1 : ∀ x, f x = 0 → x > 0) : sorry := by
  sorry
```

---

### 示例 2：可微函数的中值定理

**自然语言：**
> 设 f 是可微函数，f 在 [a,b] 上连续，f 在 (a,b) 上可微，则存在 c 使得 f(b) - f(a) 等于 f'(c) * (b - a)。

**Lean 4 代码：**
```lean
import Mathlib

theorem mvt_stub {f : ℝ → ℝ} (hf : Differentiable ℝ f)
  (h1 : ContinuousOn f (Icc a b)) (h2 : DifferentiableOn ℝ f (Ioo a b))
  : ∃ c, f b - f a = deriv f c * (b - a) := by
  sorry
```

---

### 示例 3：单调有界数列收敛

**自然语言：**
> 设 a_n 是单调递增数列且有上界，则 a_n 收敛。

**Lean 4 代码：**
```lean
import Mathlib

theorem monotone_convergence {a : ℕ → ℝ} (h1 : Monotone a) (h2 : BddAbove (Set.range a))
  : ∃ L, a → L := by
  sorry
```

---

## 代数学 (Algebra) — 3 个示例

### 示例 4：拉格朗日定理（有限群）

**自然语言：**
> 设 G 是有限群，H 是 G 的子群，则 H 的阶整除 G 的阶。

**Lean 4 代码：**
```lean
import Mathlib

theorem lagrange {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  : Nat.card H ∣ Nat.card G := by
  sorry
```

---

### 示例 5：域上的多项式根与因式分解

**自然语言：**
> 设 F 是域，p 是 F 上的多项式，如果 a 属于 F 且 p(a) 等于 0，则存在 q 使得 p(x) 等于 (x - a) * q(x)。

**Lean 4 代码：**
```lean
import Mathlib

theorem factor_theorem {F : Type*} [Field F] {p : Polynomial F} {a : F}
  (ha : p.eval a = 0) : ∃ q, p = (X - C a) * q := by
  sorry
```

---

### 示例 6：交换群的中心非空

**自然语言：**
> 设 G 是交换群，则对于所有 g 属于 G，g 属于 G 的中心。

**Lean 4 代码：**
```lean
import Mathlib

theorem abelian_center {G : Type*} [CommGroup G] : ∀ g ∈ G, g ∈ Subgroup.center G := by
  sorry
```

---

## 几何学 (Geometry) — 2 个示例

### 示例 7：欧几里得空间中三角不等式

**自然语言：**
> 设 X 是度量空间，对于所有 x y z 属于 X，d(x,z) 小于等于 d(x,y) + d(y,z)。

**Lean 4 代码：**
```lean
import Mathlib

theorem triangle_inequality {X : Type*} [MetricSpace X] (x y z : X)
  : dist x z ≤ dist x y + dist y z := by
  sorry
```

---

### 示例 8：凸集中的线段包含性

**自然语言：**
> 设 S 是 ℝ^n 中的凸集，对于所有 x y 属于 S 和所有 t 属于 [0,1]，(1-t)*x + t*y 属于 S。

**Lean 4 代码：**
```lean
import Mathlib

theorem convex_set {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)
  (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (hy : y ∈ S)
  (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
  : (1 - t) • x + t • y ∈ S := by
  sorry
```

---

## 数论 (Number Theory) — 2 个示例

### 示例 9：费马小定理

**自然语言：**
> 设 p 是素数，a 是整数，如果 a 不被 p 整除，则 a^(p-1) 模 p 等于 1。

**Lean 4 代码：**
```lean
import Mathlib

theorem fermat_little {p : ℕ} (hp : Nat.Prime p) {a : ℤ} (ha : ¬ (p ∣ a))
  : a ^ (p - 1) ≡ 1 [ZMOD p] := by
  sorry
```

---

### 示例 10：欧几里得算法（最大公约数存在性）

**自然语言：**
> 设 a b 是自然数，则存在 d 使得 d 整除 a 且 d 整除 b 且对于所有 e 如果 e 整除 a 且 e 整除 b 则 e 小于等于 d。

**Lean 代码：**
```lean
import Mathlib

theorem gcd_exists (a b : ℕ) : ∃ d, d ∣ a ∧ d ∣ b ∧ ∀ e, e ∣ a ∧ e ∣ b → e ≤ d := by
  sorry
```

---

*注：以上代码均为框架代码（含 `sorry`），需要进一步人工完善证明部分。*
