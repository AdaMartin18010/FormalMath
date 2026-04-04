/-
# 反常积分收敛判别 / Improper Integral Convergence

## 数学背景

反常积分（Improper Integral）是定积分的推广，主要处理两种情况：
1. 无穷区间上的积分：∫ₐ^∞ f(x)dx
2. 无界函数的积分：∫ₐᵇ f(x)dx，其中f在[a,b]上无界

## 收敛判别法
- 比较判别法 (Comparison Test)
- p-判别法 (p-Test)
- 绝对收敛判别法 (Absolute Convergence)
- 柯西收敛准则 (Cauchy Criterion)

## 定义

**定义1（无穷区间反常积分）**：设函数 f 在 [a, +∞) 上有定义，且对任意 b > a，f 在 [a, b] 上可积。若极限
  lim_{b→∞} ∫ₐᵇ f(x)dx
存在且有限，则称反常积分 ∫ₐ^∞ f(x)dx **收敛**。

**定义2（瑕积分）**：设函数 f 在 (a, b] 上有定义，在点 a 的右邻域无界，且对任意 ε > 0，f 在 [a+ε, b] 上可积。若极限
  lim_{ε→0⁺} ∫_{a+ε}^b f(x)dx
存在且有限，则称瑕积分 ∫ₐᵇ f(x)dx **收敛**。

## 定理

**定理1（比较判别法）**：设 0 ≤ f(x) ≤ g(x) 对所有 x ≥ a 成立，
- 若 ∫ₐ^∞ g(x)dx 收敛，则 ∫ₐ^∞ f(x)dx 也收敛
- 若 ∫ₐ^∞ f(x)dx 发散，则 ∫ₐ^∞ g(x)dx 也发散

**证明框架**：
1. 设 F(t) = ∫ₐᵗ f(x)dx，G(t) = ∫ₐᵗ g(x)dx
2. 由于 0 ≤ f ≤ g，有 0 ≤ F(t) ≤ G(t) 对所有 t ≥ a
3. G(t) 单调递增且收敛，故有上界
4. F(t) 单调递增且有上界，由单调有界定理，F(t) 收敛

**定理2（p-判别法）**：积分 ∫₁^∞ (1/xᵖ)dx
- 当 p > 1 时收敛，且值为 1/(p-1)
- 当 p ≤ 1 时发散

**证明框架（p > 1 情况）**：
1. 计算定积分：∫₁^t x^(-p)dx = [x^(1-p)/(1-p)]₁^t = (t^(1-p) - 1)/(1-p)
2. 当 t → ∞ 时，由于 1-p < 0，有 t^(1-p) → 0
3. 所以极限值为 (0 - 1)/(1-p) = 1/(p-1)

**证明框架（p = 1 情况）**：
1. ∫₁^t 1/x dx = ln(t) - ln(1) = ln(t)
2. 当 t → ∞ 时，ln(t) → ∞，积分发散

**定理3（绝对收敛判别法）**：若 ∫ₐ^∞ |f(x)|dx 收敛，则 ∫ₐ^∞ f(x)dx 也收敛。

**证明框架**：
1. 利用不等式 |∫_{t₁}^{t₂} f(x)dx| ≤ ∫_{t₁}^{t₂} |f(x)|dx
2. 由绝对收敛的柯西条件，∀ε>0, ∃N, 当 t₁,t₂ > N 时，∫_{t₁}^{t₂} |f(x)|dx < ε
3. 所以 |∫_{t₁}^{t₂} f(x)dx| < ε，满足柯西收敛条件
4. 由实数完备性，∫ₐ^∞ f(x)dx 收敛

**定理4（柯西收敛准则）**：反常积分 ∫ₐ^∞ f(x)dx 收敛当且仅当
∀ε>0, ∃N>a, ∀t₁,t₂>N, |∫_{t₁}^{t₂} f(x)dx| < ε

**证明框架**：
- (⇒) 若积分收敛于 L，则 F(t) = ∫ₐᵗ f(x)dx → L，由极限的柯西性质得证
- (⇐) 若满足柯西条件，由实数完备性（R的完备性），F(t) 收敛

**定理5（瑕积分的p-判别法）**：对于 ∫₀¹ (1/xᵖ)dx
- 当 p < 1 时收敛，且值为 1/(1-p)
- 当 p ≥ 1 时发散
-/

namespace ImproperIntegral

/-- 反常积分在无穷区间收敛的定义 

**数学定义**：∫ₐ^∞ f(x)dx 收敛当且仅当极限 lim_{t→∞} ∫ₐᵗ f(x)dx 存在且有限 -/
def ConvergentAtTop (f : Float → Float) (a : Float) : Prop :=
  ∃ L : Float, ∀ ε : Float, ε > 0 → ∃ N : Float, N > a ∧ ∀ t : Float, t > N → 
    ∃ I : Float, (I - L).abs < ε

/-- 瑕积分在奇点处收敛的定义 

**数学定义**：∫ₐᵇ f(x)dx 收敛（f在a处无界）当且仅当 
lim_{t→a⁺} ∫ₜᵇ f(x)dx 存在且有限 -/
def ConvergentAtSingularity (f : Float → Float) (a b : Float) : Prop :=
  ∃ L : Float, ∀ ε : Float, ε > 0 → ∃ δ : Float, δ > 0 ∧ ∀ t : Float, a < t ∧ t < a + δ → 
    ∃ I : Float, (I - L).abs < ε

-- 定理陈述（框架）

/-- 比较判别法框架 

**定理**：设 0 ≤ f(x) ≤ g(x) 对所有 x ≥ a 成立，
若 ∫ₐ^∞ g(x)dx 收敛，则 ∫ₐ^∞ f(x)dx 也收敛 -/
theorem comparison_test (f g : Float → Float) (a : Float)
    (hf : ∀ x, x ≥ a → 0 ≤ f x ∧ f x ≤ g x)
    (hg : ConvergentAtTop g a) :
    ConvergentAtTop f a := by
  /- 
  证明思路：利用单调有界定理
  详细证明需要积分理论和实数完备性
  
  **完整证明**：
  1. 设 F(t) = ∫ₐᵗ f(x)dx，G(t) = ∫ₐᵗ g(x)dx
  2. 由于 0 ≤ f ≤ g，有 0 ≤ F(t) ≤ G(t) 对所有 t ≥ a
  3. G(t) 单调递增且收敛，故有上界 M
  4. F(t) 单调递增且 F(t) ≤ G(t) ≤ M，故 F(t) 有上界
  5. 由单调有界定理，F(t) 收敛
  -/
  sorry

/-- p-判别法（收敛情况）

**定理**：积分 ∫₁^∞ (1/xᵖ)dx 当 p > 1 时收敛，且值为 1/(p-1) -/
theorem p_test_convergent (p : Float) (hp : p > 1) :
    ConvergentAtTop (fun x => 1 / (x ^ p)) 1 := by
  /- 
  证明详解：
  1. 对于 p > 1，计算 ∫₁^t x^(-p) dx
  2. 原函数为 F(x) = x^(1-p) / (1-p)
  3. F(t) - F(1) = (t^(1-p) - 1) / (1-p)
  4. 由于 1-p < 0，当 t → ∞ 时，t^(1-p) → 0
  5. 极限值为 -1/(1-p) = 1/(p-1)
  -/
  sorry

/-- p-判别法（发散情况）

**定理**：积分 ∫₁^∞ (1/xᵖ)dx 当 p ≤ 1 时发散 -/
theorem p_test_divergent (p : Float) (hp : p ≤ 1) :
    ¬ ConvergentAtTop (fun x => 1 / (x ^ p)) 1 := by
  /-
  证明详解：
  - p = 1: ∫₁^t 1/x dx = ln(t) → ∞ 当 t → ∞
  - p < 1: ∫₁^t x^(-p) dx = (t^(1-p) - 1)/(1-p) → ∞ 当 t → ∞
    （因为 1-p > 0，所以 t^(1-p) → ∞）
  -/
  sorry

/-- 绝对收敛判别法框架 

**定理**：若 ∫ₐ^∞ |f(x)|dx 收敛，则 ∫ₐ^∞ f(x)dx 也收敛 -/
theorem abs_implies_convergence (f : Float → Float) (a : Float)
    (hf : ConvergentAtTop (fun x => (f x).abs) a) :
    ConvergentAtTop f a := by
  /-
  证明详解：
  利用 |∫ f| ≤ ∫|f| 和柯西收敛准则
  
  **详细证明**：
  1. 对任意 ε > 0，由 ∫|f| 收敛，存在 N 使得当 t₁,t₂ > N 时
     ∫_{t₁}^{t₂} |f(x)|dx < ε
  2. 由 |∫_{t₁}^{t₂} f(x)dx| ≤ ∫_{t₁}^{t₂} |f(x)|dx < ε
  3. 满足柯西收敛条件，故 ∫f 收敛
  -/
  sorry

/-- 柯西收敛准则框架 

**定理**：反常积分 ∫ₐ^∞ f(x)dx 收敛当且仅当
∀ε>0, ∃N>a, ∀t₁,t₂>N, |∫_{t₁}^{t₂} f(x)dx| < ε -/
theorem cauchy_criterion (f : Float → Float) (a : Float) :
    ConvergentAtTop f a ↔ 
    ∀ ε : Float, ε > 0 → ∃ N : Float, N > a ∧ ∀ t₁ t₂ : Float, t₁ > N → t₂ > N → 
      ∃ I₁ I₂ : Float, (I₁ - I₂).abs < ε := by
  /-
  证明详解：
  - (⇒) 由收敛的定义和极限的唯一性
    若 F(t) → L，则对 ε/2 > 0，存在 N 使得当 t > N 时 |F(t) - L| < ε/2
    于是 |F(t₁) - F(t₂)| ≤ |F(t₁) - L| + |L - F(t₂)| < ε
  
  - (⇐) 若满足柯西条件，由实数完备性（柯西序列收敛），F(t) 收敛
  -/
  sorry

/-- 瑕积分的p-判别法框架 

**定理**：对于 ∫₀¹ (1/xᵖ)dx
- 当 p < 1 时收敛，且值为 1/(1-p)
- 当 p ≥ 1 时发散 -/
theorem p_test_singular (p : Float) (b : Float) (hb : b > 0) :
    ConvergentAtSingularity (fun x => 1 / (x ^ p)) 0 b ↔ p < 1 := by
  /-
  证明思路：
  类似无穷区间情况，计算 ∫_t^1 x^(-p)dx 并令 t → 0⁺
  
  **详细证明**：
  - p ≠ 1: ∫_t^1 x^(-p)dx = [x^(1-p)/(1-p)]_t^1 = (1 - t^(1-p))/(1-p)
    当 t → 0⁺：
    * p < 1: 1-p > 0, t^(1-p) → 0, 极限 = 1/(1-p)
    * p > 1: 1-p < 0, t^(1-p) → ∞, 发散
  - p = 1: ∫_t^1 1/x dx = -ln(t) → ∞ 当 t → 0⁺
  -/
  sorry

end ImproperIntegral
