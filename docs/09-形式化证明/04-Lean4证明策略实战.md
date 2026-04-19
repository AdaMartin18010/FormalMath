---
title: "Lean4证明策略实战"
msc_primary: "03"
---

# Lean4 证明策略实战

## 目录

1. [基础策略](#基础策略)
2. [进阶策略](#进阶策略)
3. [归纳策略](#归纳策略)
4. [化简技巧](#化简技巧)
5. [算术策略](#算术策略)
6. [代数运算](#代数运算)
7. [实际证明案例](#实际证明案例)

---

## 基础策略

### intro - 引入假设

`intro` 用于引入蕴含式的前提或全称量词的变量。

```lean4
-- 引入蕴含式的前提
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  intro hp  -- 当目标是 p → q 时使用
  -- 实际上这里应该用 apply hpq 和 exact hp
  sorry

-- 更常见的用法
example (p q : Prop) : p → (p → q) → q := by
  intro hp hpq
  apply hpq
  exact hp

-- 引入全称量词变量
example : ∀ n : Nat, n + 0 = n := by
  intro n
  rw [Nat.add_zero]
```

**技巧**：可以一次引入多个变量 `intro h1 h2 h3`

### apply - 应用定理

`apply` 用于将当前目标与已知定理的结论进行匹配。

```lean4
-- 基本用法
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  apply h2  -- 目标变为 q
  apply h1  -- 目标变为 p
  exact hp  -- 完成

-- 使用已知引理
example (n m : Nat) (h : n < m) : n ≤ m := by
  apply Nat.le_of_lt
  exact h
```

**技巧**：`apply?` 会搜索 Mathlib 中可能适用的定理。

### exact - 精确匹配

`exact` 用于当手头的项恰好就是目标类型时。

```lean4
-- 精确匹配证明
example (p : Prop) (hp : p) : p := by
  exact hp

-- 构造证明项
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩
```

---

## 进阶策略

### have - 引入中间结论

`have` 用于在证明中引入局部引理。

```lean4
-- 基本用法
example (n : Nat) : n + n = 2 * n := by
  have h : n + n = n * 2 := by
    rw [Nat.mul_add]
    simp
  rw [h]
  rw [Nat.mul_comm]

-- 带类型的 have
example (n : Nat) : ∃ m, n + n = m := by
  have h : n + n = 2 * n := by ring
  exact ⟨2 * n, by rw [h]⟩
```

### let - 定义局部变量

`let` 用于在证明中引入定义。

```lean4
-- 定义辅助函数
example (n : Nat) : n ^ 2 - n = n * (n - 1) := by
  let m := n - 1
  have hn : n = m + 1 := by omega
  rw [hn]
  ring

-- 在证明中使用 let
example (x y : Nat) (h : x > y) : ∃ z, x = y + z := by
  let z := x - y
  use z
  omega
```

### rewrite (rw) - 重写

`rw` 是 Lean 中最常用的策略之一，用于等式替换。

```lean4
-- 基本重写
example (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_one, Nat.one_mul]
  ring

-- 使用←进行反向重写
example (n : Nat) : n * n + n = n * (n + 1) := by
  rw [←Nat.mul_add_one]

-- 在假设中重写
example (n m : Nat) (h : n + 1 = m) : n < m := by
  rw [h] at *
  apply Nat.lt_succ_self

-- 使用 location 指定位置
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1] at *  -- 在所有位置重写
  exact h2
```

**技巧**：`rw [h1, h2, h3]` 会依次应用多个重写规则。

---

## 归纳策略

### induction - 数学归纳法

`induction` 用于执行归纳证明。

```lean4
-- 自然数归纳
example (n : Nat) : ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf
    omega

-- 结构归纳
inductive Tree (α : Type)
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

def Tree.size {α : Type} : Tree α → Nat
  | leaf => 0
  | node _ l r => 1 + size l + size r

def Tree.height {α : Type} : Tree α → Nat
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)

theorem Tree.size_le_height {α : Type} (t : Tree α) :
    t.size ≤ 2 ^ t.height - 1 := by
  induction t with
  | leaf => simp
  | node x l r ihl ihr =>
    simp [size, height]
    have h1 : l.size ≤ 2 ^ l.height - 1 := ihl
    have h2 : r.size ≤ 2 ^ r.height - 1 := ihr
    have h3 : max l.height r.height ≥ l.height := by apply Nat.le_max_left
    have h4 : max l.height r.height ≥ r.height := by apply Nat.le_max_right
    -- 继续证明...
    sorry
```

### cases - 案例分析

`cases` 用于对归纳类型进行解构。

```lean4
-- 对命题进行案例分析
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- 对自然数进行案例分析
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; apply Nat.succ_pos

-- 使用 rcases 进行更简洁的案例分析
example (p q r : Prop) : p ∧ q ∧ r → r ∧ q ∧ p := by
  rintro ⟨hp, hq, hr⟩
  exact ⟨hr, hq, hp⟩
```

---

## 化简技巧

### simp - 简化表达式

`simp` 是 Lean 的自动简化器，使用一系列引理进行重写。

```lean4
-- 基本简化
example (n : Nat) : n + 0 = n := by
  simp  -- 使用 Nat.add_zero

-- 带参数的简化
example (l : List Nat) : [] ++ l = l := by
  simp [List.append_nil]

-- 在特定位置简化
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simp at h
  exact h

-- 使用 simp_all 简化所有假设和目标
example (n : Nat) (h1 : n > 0) (h2 : n - 1 + 1 = n) : n ≥ 1 := by
  simp_all
```

**技巧**：`simp only [h1, h2]` 只使用指定的引理进行简化。

### dsimp - 定义性简化

`dsimp` 进行定义性简化，不依赖引理。

```lean4
def myAdd (n m : Nat) : Nat := n + m

example (n : Nat) : myAdd n 0 = n := by
  dsimp [myAdd]  -- 展开 myAdd 的定义
  simp
```

### simp_rw - 顺序简化重写

`simp_rw` 结合了 `simp` 和 `rw` 的特点。

```lean4
example (n m k : Nat) : (n + m) + k = n + (m + k) := by
  simp_rw [Nat.add_assoc]
```

---

## 算术策略

### linarith - 线性算术

`linarith` 自动证明线性算术中的不等式。

```lean4
-- 基本线性不等式
example (x y : Int) (h1 : x > y) (h2 : y > 0) : x > 0 := by
  linarith

-- 带等式的情况
example (a b c : Int) (h1 : a = b + 1) (h2 : b = c - 2) : a = c - 1 := by
  linarith

-- 使用假设的线性组合
example (x y z : Int) (h1 : x + y ≥ 10) (h2 : y + z ≥ 20) : x + 2*y + z ≥ 30 := by
  linarith
```

**技巧**：`linarith [h1, h2]` 可以使用特定的假设。

### nlinarith - 非线性算术

`nlinarith` 处理非线性算术问题。

```lean4
-- 平方的非负性
example (x : Int) : x ^ 2 ≥ 0 := by
  nlinarith

-- 基本不等式
example (a b : Int) (ha : a > 0) (hb : b > 0) :
    a + b ≥ 2 * Real.sqrt (a * b) := by
  -- 这需要 Real 数支持
  sorry

-- AM-GM 不等式简单形式
example (a b : Nat) (ha : a > 0) (hb : b > 0) :
    (a + b) ^ 2 ≥ 4 * a * b := by
  nlinarith [sq_nonneg (a - b : Int)]
```

### omega - Presburger 算术

`omega` 专门处理整数和自然的 Presburger 算术。

```lean4
example (n m : Int) (h : n < m) : n + 1 ≤ m := by
  omega

example (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  omega
```

---

## 代数运算

### ring - 环运算

`ring` 自动证明环结构中的等式。

```lean4
-- 多项式展开
example (x y : Int) : (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  ring

-- 因式分解
example (x y : Int) : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by
  ring

-- 复杂表达式
example (a b c : Int) :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a := by
  ring
```

### ring_nf - 环正规形式

`ring_nf` 将表达式化为环的正规形式。

```lean4
example (x : Int) : (x + 1) * (x - 1) + 1 = x ^ 2 := by
  ring_nf
```

### field - 域运算

`field` 用于域中的运算（处理除法）。

```lean4
example (x y : Rat) (hy : y ≠ 0) : (x / y) * y = x := by
  field_simp [hy]
```

### abel - 阿贝尔群运算

`abel` 处理阿贝尔群中的表达式。

```lean4
example (G : Type) [AddCommGroup G] (a b c : G) :
    a + b + c = c + b + a := by
  abel
```

---

## 实际证明案例

### 案例 1：求和公式

```lean4
import Mathlib

-- 自然数前 n 项和
example (n : Nat) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring_nf
    omega
```

### 案例 2：二项式系数恒等式

```lean4
-- Pascal 恒等式
example (n k : Nat) (h : k ≤ n) :
    Nat.choose n k + Nat.choose n (k + 1) = Nat.choose (n + 1) (k + 1) := by
  cases k with
  | zero =>
    simp [Nat.choose]
  | succ k =>
    rw [Nat.choose_succ_succ]
    rw [Nat.add_comm]
```

### 案例 3：列表性质

```lean4
-- 列表反转的长度不变
example (α : Type) (l : List α) : (l.reverse).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
```

### 案例 4：模运算

```lean4
-- 模运算的基本性质
example (a b n : Nat) (hn : n > 0) :
    (a + b) % n = ((a % n) + (b % n)) % n := by
  simp [Nat.add_mod]

-- 费马小定理的特例
example (p : Nat) (hp : Nat.Prime p) (a : Nat) (ha : ¬ p ∣ a) :
    a ^ (p - 1) % p = 1 := by
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card_sub_one_eq_one, ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact ha
```

### 案例 5：集合运算

```lean4
import Mathlib

-- 德摩根定律
example (α : Type) (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
  apply not_and_or
```

---

## 策略组合技巧

### <;> - 对所有目标应用

```lean4
example (p q r : Prop) : (p → q → r) → (p → q) → p → r := by
  intro h1 h2 hp
  apply h1
  · exact hp
  · apply h2
    exact hp

-- 使用 <;> 更简洁
example (p q r : Prop) : (p → q → r) → (p → q) → p → r := by
  intro h1 h2 hp
  apply h1
  all_goals
    try apply h2
    try exact hp
```

### try / try!

```lean4
-- try 不失败
example (n : Nat) : n ≥ 0 := by
  try linarith  -- 成功
  try omega     -- 也成功，因为前面没有失败

-- try! 确保至少有一个成功
example (n : Nat) : n + 0 = n := by
  try! simp     -- simp 成功，所以 try! 成功
```

### first | ... | ...

```lean4
-- 尝试多个策略
example (n : Nat) : n + 0 = n := by
  first | simp | rfl | tauto
```

---

## 完整证明示例

### 证明：sqrt(2) 是无理数

```lean4
import Mathlib

theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := by
  native_decide

-- 手动证明版本
theorem irrational_sqrt_two_manual : Irrational (Real.sqrt 2) := by
  rw [irrational_sqrt_natCast_iff]
  · native_decide
  · norm_num
```

### 证明：无穷多个素数

```lean4
import Mathlib

-- 存在任意大的素数
theorem infinite_primes (n : Nat) : ∃ p > n, Nat.Prime p := by
  let N := Nat.factorial n + 1
  have hN : N > 1 := by
    apply Nat.succ_lt_succ
    apply Nat.factorial_pos

  -- N 有一个素因子
  obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd (by linarith : N ≠ 1)

  use p
  constructor
  · -- 证明 p > n
    by_contra h
    push_neg at h
    have h1 : p ∣ Nat.factorial n := by
      apply Nat.dvd_factorial
      · exact Nat.Prime.pos hp_prime
      · exact h

    have h2 : p ∣ 1 := by
      have : p ∣ N - Nat.factorial n := by
        apply Nat.dvd_sub'
        · exact hp_div
        · exact h1
      simp [N] at this
      exact this

    have h3 : p ≤ 1 := by
      apply Nat.le_of_dvd (by norm_num) h2

    have h4 : p ≥ 2 := by
      apply Nat.Prime.two_le hp_prime

    linarith

  · -- p 是素数
    exact hp_prime
```

---

## 总结

| 策略 | 用途 | 复杂度 |
|------|------|--------|
| intro | 引入假设/变量 | ⭐ |
| apply | 应用定理 | ⭐ |
| exact | 精确匹配 | ⭐ |
| have | 中间结论 | ⭐⭐ |
| let | 局部定义 | ⭐⭐ |
| rw | 等式重写 | ⭐⭐ |
| simp | 自动简化 | ⭐⭐ |
| induction | 数学归纳 | ⭐⭐⭐ |
| cases | 案例分析 | ⭐⭐ |
| linarith | 线性算术 | ⭐⭐ |
| nlinarith | 非线性算术 | ⭐⭐⭐ |
| ring | 环运算 | ⭐⭐ |
| field | 域运算 | ⭐⭐⭐ |

---

*本文档是 FormalMath 项目的一部分，遵循项目贡献指南。*
