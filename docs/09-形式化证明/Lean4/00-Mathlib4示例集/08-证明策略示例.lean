import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic

/-! 
# 证明策略（Tactics）示例

对应的FormalMath文档：
- docs/09-形式化证明/01-证明系统基础-深度扩展版.md
- docs/09-形式化证明/01-证明系统基础.md

对应的Mathlib4模块：
- Mathlib.Tactic

## 概述

Lean4使用tactics（策略）来构造证明。本文档展示常用策略及其用法。
-/ 

/-! 
## 基础策略

最基本的证明策略。
-/

section BasicTactics

-- rfl：自反性证明
example (n : ℕ) : n = n := by
  rfl

-- exact：直接提供证明项
example (n : ℕ) : n = n := by
  exact rfl

-- intro：引入假设
example (P Q : Prop) : P → (P → Q) → Q := by
  intro hp hpq
  exact hpq hp

-- apply：应用蕴含关系
example (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

-- assumption：使用现有假设
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  apply hpq
  assumption

-- trivial：证明显然目标（如True）
example : True := by
  trivial

-- contradiction：从矛盾推导
example (P : Prop) (hp : P) (hnp : ¬P) : False := by
  contradiction

end BasicTactics

/-! 
## 重写策略

使用等式进行重写。
-/

section Rewriting

-- rw：重写
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw [h2]

-- rw [...] at ...：在假设中重写
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1] at *
  exact h2

-- simp：简化
example (n : ℕ) : n + 0 = n := by
  simp

-- simp only [...]：仅使用指定引理简化
example (n : ℕ) : n + 0 = n := by
  simp only [add_zero]

-- dsimp：定义简化
example (n : ℕ) : id n = n := by
  dsimp [id]
  rfl

-- calc：计算式证明
example (a b c d : ℕ) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  calc
    a = b := by rw [h1]
    _ = c := by rw [h2]
    _ = d := by rw [h3]

end Rewriting

/-! 
## 目标分解策略

分解复杂目标。
-/

section GoalDecomposition

-- constructor：分解合取（∧）目标
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- cases：分解合取（∧）假设
example (P Q : Prop) (hpq : P ∧ Q) : P := by
  cases hpq with
  | intro hp hq => exact hp

-- rcases：更强大的模式匹配分解
example (P Q R : Prop) (hpqr : P ∧ Q ∧ R) : R := by
  rcases hpqr with ⟨hp, hq, hr⟩
  exact hr

-- left/right：证明析取（∨）的某一边
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

-- obtain：存在量词消去
example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ n, P n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩

-- use：存在量词引入
example : ∃ n : ℕ, n = 0 := by
  use 0
  rfl

-- ext：外延性（扩展证明）
example (A B : Set ℕ) (h : ∀ n, n ∈ A ↔ n ∈ B) : A = B := by
  ext n
  exact h n

-- refine：部分构造证明项
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  refine ⟨hp, ?_⟩
  exact hq

end GoalDecomposition

/-! 
## 归纳法

数学归纳法。
-/

section Induction

-- induction：归纳法
example (n : ℕ) : ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    cases n with
    | zero => simp
    | succ n => 
      simp [Nat.mul_succ, Nat.add_assoc]
      ring

-- induction'：另一种归纳法
example (n : ℕ) : n + 0 = n := by
  induction' n with n ih
  · rfl
  · simp [ih]

-- cases：对自然数进行情况分析
example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  cases n with
  | zero => left; rfl
  | succ n => right; use n; rfl

-- strong_recursion：强归纳法
example (P : ℕ → Prop) (h : ∀ n, (∀ m < n, P m) → P n) (n : ℕ) : P n := by
  apply Nat.strongRecOn
  exact h

end Induction

/-! 
## 反证法

反证和矛盾推导。
-/

section Contradiction

-- by_contra：反证法
example (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_contra hnp
  exact hnnp hnp

-- by_cases：分情况讨论
example (P Q : Prop) : (P → Q) → (¬P → Q) → Q := by
  intro hpq hnpq
  by_cases hp : P
  · exact hpq hp
  · exact hnpq hp

-- push_neg：否定推进
example (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro h
  push_neg at h
  assumption

-- contrapose：逆否命题
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq
  contrapose! hnq
  exact hpq hnq

end Contradiction

/-! 
## 算术和线性算术

处理算术目标。
-/

section Arithmetic

-- linarith：线性算术求解器
example (a b c : ℕ) (h1 : a + b = c) (h2 : a = b) : 2 * a = c := by
  linarith

-- omega：整数线性算术
example (m n : ℤ) (h : m + n = 10) : n + m = 10 := by
  omega

-- ring：环论简化
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

-- ring_nf：环论标准形
example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring_nf

-- norm_num：数值计算
example : 2 + 2 = 4 := by
  norm_num

example : 10 / 3 = 3 := by
  norm_num

-- abel：阿贝尔群计算
example (a b c : ℤ) : a + b + c = c + b + a := by
  abel

end Arithmetic

/-! 
## 自动化策略

更强的自动化证明。
-/

section Automation

-- aesop：自动证明搜索
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  aesop

-- tauto：命题逻辑自动证明
example (P Q : Prop) : (P → Q) → P → Q := by
  tauto

-- finish：基于上下文的自动证明
example (P Q : Prop) (h : P ∧ Q) : P := by
  finish

-- tidy：整理和简化目标
example (P Q : Prop) (h : P ∧ Q) : P := by
  tidy

end Automation

/-! 
## 集合和逻辑

处理集合和逻辑的特殊策略。
-/

section SetTheory

-- set_tac：集合论自动证明
example (A B : Set ℕ) : A ∩ B ⊆ A := by
  intro n hn
  simp at hn
  exact hn.1

-- simp_set：集合简化
example (A B : Set ℕ) (n : ℕ) (hn : n ∈ A ∩ B) : n ∈ B ∩ A := by
  simp [Set.mem_inter] at hn ⊢
  tauto

end SetTheory

/-! 
## 结构化证明

编写可读性强的证明。
-/

section StructuredProofs

-- 使用bullet points（·）组织证明
example (P Q R : Prop) (hp : P) (hq : Q) (hqr : Q → R) : P ∧ R := by
  constructor
  · exact hp
  · apply hqr
    exact hq

-- 使用show明确目标
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  show Q
  apply hpq
  show P
  exact hp

-- 使用have引入中间步骤
example (n : ℕ) : n + 0 = n := by
  have h : n + 0 = n := by
    rw [add_zero]
  exact h

-- 使用suffices转换目标
example (P Q : Prop) (hpq : P → Q) : P → Q := by
  suffices P → Q by assumption
  intro hp
  exact hpq hp

end StructuredProofs

/-! 
## 示例：综合证明

展示多种策略的综合使用。
-/

section ComprehensiveExample

-- 证明：群的单位元唯一
theorem group_id_unique {G : Type*} [Group G] (e₁ e₂ : G) 
    (h1 : ∀ g, e₁ * g = g) (h2 : ∀ g, e₂ * g = g) : e₁ = e₂ := by
  calc
    e₁ = e₁ * e₂ := by rw [h2]
    _  = e₂      := by rw [h1]

-- 使用结构化证明重写
example {G : Type*} [Group G] (e₁ e₂ : G) 
    (h1 : ∀ g, e₁ * g = g) (h2 : ∀ g, e₂ * g = g) : e₁ = e₂ := by
  have he2 : e₁ * e₂ = e₂ := h2 e₁
  have he1 : e₁ * e₂ = e₁ := by
    calc
      e₁ * e₂ = e₁ := by rw [mul_one]
      _       = e₁ := rfl
  rw [he1] at he2
  exact he2.symm

end ComprehensiveExample

/-! 
## 练习

1. 使用induction证明：对于所有自然数n，∑_{i=0}^{n-1} 2^i = 2^n - 1。

2. 使用contrapose证明：如果n²是偶数，那么n是偶数。

3. 使用ring证明：(a + b + c)² = a² + b² + c² + 2ab + 2bc + 2ca。

4. 使用by_cases证明排中律：P ∨ ¬P。

5. 编写一个结构化证明，证明群的逆元唯一。

-/ 

section Exercises

-- 练习1的框架
example (n : ℕ) : ∑ i in Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    cases n with
    | zero => norm_num
    | succ n => 
      simp [pow_succ, Nat.add_assoc]
      ring

-- 练习4的框架
example (P : Prop) : P ∨ ¬P := by
  by_cases hp : P
  · left; exact hp
  · right; exact hp

end Exercises
