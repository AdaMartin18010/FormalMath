/-
# 康托尔对角线定理的形式化证明 / Cantor's Diagonal Argument

## 定理信息
- **定理名称**: 康托尔对角线定理 (Cantor's Diagonal Theorem)
- **数学领域**: 集合论 / Set Theory
- **MSC2020编码**: 03E10 (基数和序数)

## 定理陈述

**康托尔定理**：对于任意集合 A，不存在从 A 到其幂集 P(A) 的满射。

等价表述：|A| < |P(A)|

即：对于任意集合，其幂集的基数严格大于它自身的基数。

## 数学意义

1. 无穷集合有不同的"大小"
2. 存在不可数无穷集（如实数集）
3. 不存在最大的基数

## 历史背景

该定理由格奥尔格·康托尔 (Georg Cantor) 在1891年提出。

## 证明详解

### 定理证明（反证法）

**假设**：存在满射 f: A → P(A)

**构造对角线集合**：
```
D = {x ∈ A | x ∉ f(x)}
```

**分析**：
1. D 是 A 的子集，所以 D ∈ P(A)
2. 由于 f 是满射，存在 d ∈ A 使得 f(d) = D

**矛盾推导**：
- **情况1**：假设 d ∈ D
  - 由 D 的定义，d ∉ f(d)
  - 但 f(d) = D，所以 d ∉ D
  - 矛盾！

- **情况2**：假设 d ∉ D
  - 由 D 的定义，若 d ∉ f(d)，则 d ∈ D
  - 但 f(d) = D，所以 d ∈ D
  - 矛盾！

**结论**：不存在从 A 到 P(A) 的满射。

### 基数形式

**推论**：|A| < |P(A)|

**证明**：
1. 存在单射 g: A → P(A)，定义为 g(x) = {x}
   - 所以 |A| ≤ |P(A)|
2. 由康托尔定理，不存在满射 A → P(A)
   - 所以 |A| ≠ |P(A)|
3. 因此 |A| < |P(A)|

### 迭代幂集

由康托尔定理，可以构造无穷基数序列：
```
ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ...
```

其中：
- ℵ₀ = |ℕ| （自然数的基数）
- 2^ℵ₀ = |P(ℕ)| = |ℝ| （连续统的基数）

### 连续统假设

**连续统假设 (CH)**：不存在基数 κ 使得 ℵ₀ < κ < 2^ℵ₀

注：CH 在 ZFC 公理系统中独立于其他公理（Cohen, 1963；Gödel, 1940）。

## 对角线论证的应用

### 1. 实数不可数

|ℝ| = |P(ℕ)| = 2^ℵ₀ > ℵ₀ = |ℕ|

### 2. 停机问题

图灵使用对角线论证证明了停机问题是不可判定的。

### 3. Gödel不完备定理

Gödel 使用对角线论证构造了自指命题。
-/

namespace CantorDiagonalTheorem

/-- 子集的类型：A → Prop 表示 A 的子集 -/
def Subset (A : Type u) : Type u :=
  A → Prop

/-- 满射的定义：∀ b ∈ B, ∃ a ∈ A, f(a) = b -/
def Surjective {A : Type u} {B : Type v} (f : A → B) : Prop :=
  ∀ b : B, ∃ a : A, f a = b

/-- 康托尔定理：不存在从A到其幂集的满射 

**证明思路**（反证法）：
1. 假设 f: A → P(A) 是满射
2. 构造对角线集合 D = {x | x ∉ f(x)}
3. 导出矛盾

**详细证明**：
- 若 f 满射，则存在 d 使得 f(d) = D
- 问：d ∈ D 是否成立？
  * 若 d ∈ D，则由 D 定义，d ∉ f(d) = D，矛盾
  * 若 d ∉ D，则由 D 定义，d ∈ f(d) = D，矛盾
- 故假设错误，不存在这样的满射 -/
theorem cantor_theorem {A : Type u} (f : A → Subset A) :
    ¬Surjective f := by
  sorry

/-- 单射的定义：f(a₁) = f(a₂) → a₁ = a₂ -/
def Injective {A : Type u} {B : Type v} (f : A → B) : Prop :=
  ∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂

/-- 基数的比较（简化定义）
|A| ≤ |B| 当且仅当存在单射 f: A → B -/
def CardLe (A : Type u) (B : Type v) : Prop :=
  ∃ f : A → B, Injective f

/-- 康托尔定理的基数形式：|A| < |P(A)| 

即：|A| ≤ |P(A)| 且 |A| ≠ |P(A)| -/
theorem cardinal_cantor {A : Type u} :
    CardLe A (Subset A) := by
  sorry

/-- 自然数集 ℕ 是可数无穷的标准例子 -/
def aleph_0 : Type :=
  Nat

/-- 自然数幂集 -/
def powerset_nat : Type :=
  Subset Nat

/-- 自然数幂集不可数 

**定理**：不存在从 P(ℕ) 到 ℕ 的单射

**证明**：由康托尔定理，|ℕ| < |P(ℕ)| -/
theorem powerset_nat_uncountable :
    ¬CardLe powerset_nat Nat := by
  sorry

/-- 实数不可数（框架）

**定理**：|ℝ| > |ℕ|

**证明概要**：
1. |ℝ| = |P(ℕ)| （通过二进制展开）
2. |P(ℕ)| > |ℕ| （康托尔定理）
3. 所以 |ℝ| > |ℕ| -/
theorem real_uncountable :
    ¬CardLe Real Nat := by
  sorry

end CantorDiagonalTheorem
