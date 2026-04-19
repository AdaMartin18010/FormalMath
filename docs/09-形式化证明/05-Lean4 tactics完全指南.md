---
title: "Lean4 tactics完全指南"
msc_primary: "03"
---

# Lean4 Tactics 完全指南

本文档提供 Lean4 中 60+ 个 tactics 的完整参考，包括分类索引、使用场景和组合技巧。

---

## 目录

1. [基础 Tactics](#基础-tactics)
2. [进阶 Tactics](#进阶-tactics)
3. [专业 Tactics](#专业-tactics)
4. [自动化 Tactics](#自动化-tactics)
5. [组合技巧](#组合技巧)
6. [快速参考表](#快速参考表)

---

## 基础 Tactics

### 1. exact

**用途**：当手头有恰好匹配目标的证明项时使用。

```lean4
example (p : Prop) (hp : p) : p := by exact hp
example (n : Nat) : n = n := by exact rfl
```

### 2. apply

**用途**：将目标的结论与定理的结论匹配。

```lean4
example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp
```

**变体**：`apply?` - 自动搜索 Mathlib 中的适用定理。

### 3. intro / intros

**用途**：引入假设（→）或变量（∀）。

```lean4
-- 引入一个
example (p q : Prop) : p → q → p ∧ q := by
  intro hp hq
  exact ⟨hp, hq⟩

-- 引入多个
example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros hp hq hr
  exact ⟨hp, hq, hr⟩
```

### 4. revert

**用途**：intro 的逆操作，将假设移回目标。

```lean4
example (p q : Prop) (hp : p) : p → q → p := by
  intro hp' hq
  revert hp'  -- 目标变回 p → ...
  exact id
```

### 5. assumption

**用途**：在假设中查找恰好匹配目标的项。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p := by
  assumption  -- 找到 hp
```

### 6. contradiction / exfalso

**用途**：从矛盾假设推导任意结论。

```lean4
example (p : Prop) (hp : p) (hnp : ¬p) : q := by
  contradiction  -- 发现 hp 和 hnp 矛盾

example (p : Prop) (h : p ∧ ¬p) : q := by
  exfalso
  exact h.2 h.1
```

### 7. trivial

**用途**：证明显然为真的目标（如 `True`，`x = x` 等）。

```lean4
example : True := by trivial
example (x : Nat) : x = x := by trivial  -- 实际上是 rfl
```

### 8. rfl / reflexivity

**用途**：证明自反性等式。

```lean4
example (x : Nat) : x = x := by rfl
example (f : Nat → Nat) : f = f := by reflexivity
```

---

## 进阶 Tactics

### 9. have

**用途**：引入中间引理。

```lean4
example (n : Nat) : n + n = 2 * n := by
  have h : n + n = n * 2 := by ring
  rw [h]
  rw [Nat.mul_comm]
```

**语法**：`have name : type := by proof` 或 `have name := term`

### 10. let

**用途**：引入局部定义。

```lean4
example (x : Nat) : ∃ n, x + x = n := by
  let n := 2 * x
  use n
  ring
```

### 11. show

**用途**：显式声明当前目标类型（用于文档和类型检查）。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  show p ∧ q
  exact ⟨hp, hq⟩
```

### 12. suffices

**用途**：证明一个足够强的陈述。

```lean4
example (n : Nat) : n ≥ 0 := by
  suffices n = n by linarith
  rfl
```

### 13. rewrite (rw)

**用途**：使用等式进行替换。

```lean4
-- 正向重写
example (n : Nat) : (n + 1) * (n + 1) = n^2 + 2*n + 1 := by
  rw [Nat.add_mul, Nat.mul_add]
  -- 更多步骤...
  sorry

-- 反向重写
example (n : Nat) : n * (n + 1) = n^2 + n := by
  rw [←Nat.mul_add_one]

-- 在假设中重写
example (n m : Nat) (h : n + 0 = m) : n = m := by
  rw [Nat.add_zero] at h
  exact h
```

### 14. simp

**用途**：使用 simp 引理集自动简化。

```lean4
example (n : Nat) : n + 0 = n := by simp

-- 指定引理
example (l : List Nat) : [] ++ l = l := by simp [List.append]

-- 简化所有
example (n : Nat) (h1 : n > 0) (h2 : n - 1 + 1 = n) : n ≥ 1 := by
  simp_all
```

**变体**：

- `simp only [...]` - 仅使用指定引理
- `simp [-lemma]` - 禁用特定引理
- `simp at h` - 在假设 h 中简化
- `simp at *` - 在所有位置简化

### 15. unfold

**用途**：展开定义。

```lean4
def isEven (n : Nat) : Bool := n % 2 = 0

example (n : Nat) : isEven (2*n) = true := by
  unfold isEven
  simp [Nat.mul_mod]
```

### 16. dsimp

**用途**：定义性简化（不依赖引理）。

```lean4
def double (n : Nat) := n + n

example (n : Nat) : double n = 2 * n := by
  dsimp [double]  -- 展开 double
  ring
```

### 17. change

**用途**：改变目标为定义相等的类型。

```lean4
example (n : Nat) : n + 0 = n := by
  change n = n  -- 因为 n + 0 = n 定义上
  rfl
```

### 18. generalize

**用途**：将表达式替换为变量。

```lean4
example (n m : Nat) (h : n + m = m + n) : n + m = m + n := by
  generalize hnm : n + m = x  -- 现在 x = n + m
  rw [h]
```

### 19. clear

**用途**：清除不再需要的假设。

```lean4
example (p q : Prop) (hp : p) (hq : q) : q := by
  clear hp  -- 移除 hp
  exact hq
```

### 20. specialize

**用途**：对全称量词应用特定值。

```lean4
example (p : Nat → Prop) (h : ∀ n, p n) : p 0 ∧ p 1 := by
  have h0 : p 0 := by specialize h 0; exact h
  have h1 : p 1 := by specialize h 1; exact h
  exact ⟨h0, h1⟩
```

---

## 证明结构 Tactics

### 21. by_cases

**用途**：分情况讨论（排中律）。

```lean4
example (p q : Prop) : (p → q) → (¬p → q) → q := by
  intro hpq hnq
  by_cases p
  · apply hpq; assumption
  · apply hnq; assumption
```

### 22. by_contra / by_contradiction

**用途**：反证法。

```lean4
example (p : Prop) : ¬¬p → p := by
  intro hnnp
  by_contra hnp
  exact hnnp hnp
```

### 23. push_neg

**用途**：将否定向内推。

```lean4
example (P : Nat → Prop) : ¬(∀ n, P n) → ∃ n, ¬P n := by
  intro h
  push_neg at h
  exact h
```

### 24. contrapose

**用途**：转置蕴含。

```lean4
example (p q : Prop) : (¬q → ¬p) → (p → q) := by
  intro h hp
  contrapose hp
  apply h
```

### 25. wlog

**用途**：不失一般性（Without Loss of Generality）。

```lean4
example (a b : Nat) : max a b = max b a := by
  wlog h : a ≤ b
  · -- 情况 a ≤ b
    rw [max_eq_right h, max_eq_left h]
  · -- 其他情况由对称性
    rw [max_comm]
```

### 26. done

**用途**：声明证明已完成（检查无剩余目标）。

```lean4
example (p : Prop) (hp : p) : p := by
  exact hp
  done  -- 确认完成
```

### 27. skip

**用途**：暂时跳过当前目标（用于开发中）。

```lean4
example (p : Prop) : p → p := by
  intro hp
  -- 暂时跳过
  skip
```

### 28. stop

**用途**：停止策略执行。

```lean4
example (p : Prop) : p → p := by
  intro hp
  stop  -- 在此处停止，保留目标
```

---

## 归纳与递归 Tactics

### 29. induction

**用途**：数学归纳法。

```lean4
example (n : Nat) : 2 * ∑ i in Finset.range n, i = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [Nat.mul_add, ih]
    ring
    omega
```

### 30. cases

**用途**：对归纳类型进行案例分析。

```lean4
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; apply Nat.succ_pos

-- 使用 rcases 进行模式匹配
example (p q r : Prop) : p ∧ q ∧ r → r ∧ p := by
  rintro ⟨hp, hq, hr⟩
  exact ⟨hr, hp⟩
```

### 31. rcases

**用途**：递归案例分析。

```lean4
example (p q r : Prop) : (p ∨ q) ∧ r → (p ∧ r) ∨ (q ∧ r) := by
  rintro (hp | hq) hr
  · left; exact ⟨hp, hr⟩
  · right; exact ⟨hq, hr⟩
```

### 32. obtain

**用途**：从存在量词获得见证。

```lean4
example (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, p n := by
  obtain ⟨n, hp, hq⟩ := h
  exact ⟨n, hp⟩
```

### 33. use

**用途**：提供存在量词的见证。

```lean4
example : ∃ n : Nat, n > 10 := by
  use 11
  norm_num

-- 多个见证
example : ∃ n m : Nat, n + m = 10 := by
  use 3, 7
  norm_num
```

### 34. exists

**用途**：use 的替代（更符合逻辑阅读）。

```lean4
example : ∃ n : Nat, n > 10 := by
  exists 11
```

---

## 等式与不等式 Tactics

### 35. linarith

**用途**：线性算术自动证明。

```lean4
example (x y : Int) (h1 : x > y) (h2 : y > 0) : x > 0 := by
  linarith

-- 使用特定假设
example (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  linarith [h1, h2]
```

### 36. nlinarith

**用途**：非线性算术自动证明。

```lean4
example (x : Int) : x^2 ≥ 0 := by
  nlinarith

example (a b : Int) (ha : a > 0) (hb : b > 0) : (a + b)^2 ≥ 4*a*b := by
  nlinarith [sq_nonneg (a - b)]
```

### 37. omega

**用途**：Presburger 算术（整数和自然数）。

```lean4
example (n m : Int) (h : n < m) : n + 1 ≤ m := by
  omega

example (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  omega
```

### 38. ring

**用途**：环结构中的等式证明。

```lean4
example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring
```

### 39. ring_nf

**用途**：将表达式化为环正规形式。

```lean4
example (x : Int) : (x + 1) * (x - 1) = x^2 - 1 := by
  ring_nf
```

### 40. field_simp

**用途**：域中的表达式简化。

```lean4
example (x y : Rat) (hy : y ≠ 0) : (x / y) * y = x := by
  field_simp [hy]
```

### 41. abel

**用途**：阿贝尔群中的表达式。

```lean4
example (G : Type) [AddCommGroup G] (a b c : G) : a + b + c = c + b + a := by
  abel
```

### 42. norm_num

**用途**：数值计算和证明。

```lean4
example : 2 + 2 = 4 := by norm_num
example : 10 < 100 := by norm_num
example : Nat.Prime 17 := by norm_num
```

### 43. positivity

**用途**：自动证明表达式为正。

```lean4
example (n : Nat) (hn : n > 0) : n^2 + 1 > 0 := by
  positivity
```

---

## 逻辑 Tactics

### 44. tauto

**用途**：命题逻辑自动证明。

```lean4
example (p q : Prop) : p → (p → q) → q := by
  tauto

example (p q r : Prop) : (p ∧ q) ∨ (p ∧ r) → p := by
  tauto
```

### 45. finish

**用途**：结合逻辑推理和等式重写。

```lean4
example (p q : Prop) (h1 : p → q) (h2 : ¬q) : ¬p := by
  finish
```

### 46. aesop

**用途**：强大的自动证明搜索。

```lean4
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  aesop
```

### 47. solve_by_elim

**用途**：通过反复应用假设来求解。

```lean4
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  solve_by_elim
```

---

## 集合与类型 Tactics

### 48. ext

**用途**：外延性证明（集合、函数等）。

```lean4
example (α : Type) (A B : Set α) : A ∩ B = B ∩ A := by
  ext x
  simp [Set.mem_inter_iff, And.comm]

-- 函数外延性
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext x
  apply h
```

### 49. funext

**用途**：函数外延性。

```lean4
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x
```

### 50. propext

**用途**：命题外延性。

```lean4
example (p q : Prop) (h : p ↔ q) : p = q := by
  propext
  exact h
```

---

## 自动化 Tactics

### 51. auto

**用途**：通用自动证明。

```lean4
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  auto
```

### 52. decide

**用途**：判定可判定命题。

```lean4
example : 2 + 2 = 4 := by decide
example : Nat.Prime 13 := by decide
```

### 53. native_decide

**用途**：使用原生代码进行判定（更快，但不验证）。

```lean4
example : 1000000 < 1000001 := by native_decide
```

### 54. hint

**用途**：获取证明建议。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  hint  -- 可能建议使用 exact ⟨hp, hq⟩
```

### 55. library_search

**用途**：在 Mathlib 中搜索定理。

```lean4
example (n : Nat) : n + 0 = n := by
  apply?  -- library_search 的新名称
```

---

## 元编程与高级 Tactics

### 56. macro

**用途**：定义新的 tactic 宏。

```lean4
macro "my_tac" : tactic => `(tactic| simp [Nat.add_comm])

example (n m : Nat) : n + m = m + n := by
  my_tac
```

### 57. elab

**用途**：自定义 tactic 实现。

```lean4
elab "my_exact" t:term : tactic => do
  let g ← getMainGoal
  closeMainGoalUsing `my_exact fun expectedType => do
    -- 自定义逻辑
    sorry
```

### 58. first | ... | ...

**用途**：尝试多个 tactics 直到成功。

```lean4
example (n : Nat) : n + 0 = n := by
  first | simp | rfl | ring
```

### 59. try

**用途**：尝试 tactic，失败不报错。

```lean4
example (n : Nat) : n ≥ 0 := by
  try linarith
  try omega
  -- 继续其他策略
```

### 60. try!

**用途**：尝试 tactic，要求至少一个成功。

```lean4
example (n : Nat) : n + 0 = n := by
  try! simp  -- simp 成功
```

### 61. <;> (all_goals 语法糖)

**用途**：对所有生成的目标应用 tactic。

```lean4
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> constructor <;> assumption
```

### 62. all_goals

**用途**：对所有目标应用 tactic。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  all_goals assumption
```

### 63. any_goals

**用途**：对任意目标应用 tactic（不要求全部成功）。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  any_goals assumption
```

### 64. focus

**用途**：专注于特定目标。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  focus
    exact hp
  focus
    exact hq
```

### 65. pick_goal

**用途**：选择特定目标。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  pick_goal 2
  exact hq
  exact hp
```

### 66. swap

**用途**：交换前两个目标。

```lean4
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  swap
  · exact hq
  · exact hp
```

### 67. rotate_left / rotate_right

**用途**：轮换目标顺序。

```lean4
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  constructor
  rotate_left
  -- 现在 hr 对应的目标在前
  exact hr
```

---

## 组合技巧

### 管道组合

```lean4
example (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]
  <;> rfl
```

### 条件组合

```lean4
example (n : Nat) : n ≥ 0 := by
  by_cases h : n > 0
  · linarith
  · push_neg at h
    omega
```

### 重复应用

```lean4
example (n : Nat) : n + 0 + 0 + 0 = n := by
  repeat rw [Nat.add_zero]
```

### 结构化证明

```lean4
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  have hq : q := by
    apply h1
    exact hp
  have hr : r := by
    apply h2
    exact hq
  exact hr
```

---

## 快速参考表

| 类别 | Tactic | 用途 |
|------|--------|------|
| 基础 | exact | 精确匹配 |
| 基础 | apply | 应用定理 |
| 基础 | intro | 引入假设 |
| 基础 | assumption | 查找假设 |
| 基础 | rfl | 自反性 |
| 结构 | have | 中间结论 |
| 结构 | let | 局部定义 |
| 结构 | show | 显示类型 |
| 结构 | suffices | 充分条件 |
| 重写 | rw | 等式重写 |
| 重写 | simp | 自动简化 |
| 重写 | unfold | 展开定义 |
| 重写 | dsimp | 定义性简化 |
| 归纳 | induction | 数学归纳 |
| 归纳 | cases | 案例分析 |
| 归纳 | rcases | 递归案例 |
| 存在 | use | 提供见证 |
| 存在 | obtain | 获得见证 |
| 算术 | linarith | 线性算术 |
| 算术 | nlinarith | 非线性算术 |
| 算术 | omega | Presburger |
| 算术 | ring | 环运算 |
| 算术 | field_simp | 域运算 |
| 算术 | norm_num | 数值计算 |
| 逻辑 | tauto | 命题逻辑 |
| 逻辑 | finish | 逻辑完成 |
| 逻辑 | aesop | 自动搜索 |
| 集合 | ext | 外延性 |
| 自动 | decide | 可判定命题 |
| 控制 | try | 尝试 |
| 控制 | <;> | 全目标 |
| 控制 | first | | | 或选择 |

---

*本文档是 FormalMath 项目的一部分，包含 60+ Lean4 tactics 的完整参考。*
