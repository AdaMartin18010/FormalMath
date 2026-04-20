---
title: Lean4形式化证明习题与练习
msc_primary: 68

  - 68V15
---

# Lean4形式化证明习题与练习

---

## 基础练习

### 练习1

证明：对任意自然数$n$，$n + 0 = n$

```lean
 theorem add_zero_n (n : Nat) : n + 0 = n := by
  rfl
```

**策略解析**：`rfl`（reflexivity）策略用于证明等式两边在定义上相同。在Lean中，`n + 0 = n` 是加法定义的一部分（递归定义的基础情形），因此直接可用 `rfl` 证明。这体现了Lean的核心哲学：**定义即证明**。如果两个项在计算后完全相同，则它们相等。

**相关概念**：自然数加法的递归定义：
- `0 + m = m`（左零元）
- `succ n + m = succ (n + m)`

注意这里练习要求的是 $n + 0 = n$（右零元），而定义给出的是 $0 + m = m$（左零元）。在Lean中，`Nat.add` 的定义实际上同时蕴含了两者，因此 `rfl` 可以直接解决。

---

### 练习2

证明：对任意自然数$n$，$0 + n = n$

```lean
theorem zero_add_n (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]
```

**策略解析**：
1. **归纳奠基**：当 $n = 0$ 时，$0 + 0 = 0$ 由定义直接成立（`rfl`）
2. **归纳步骤**：假设 $0 + n = n$（归纳假设 `ih`），证明 $0 + \text{succ}(n) = \text{succ}(n)$
   - `rw [Nat.add_succ]`：使用引理 $0 + \text{succ}(n) = \text{succ}(0 + n)$
   - `rw [ih]`：代入归纳假设，得到 $\text{succ}(n)$

**核心技巧**：对递归定义的操作（如自然数加法），数学归纳法是天然的选择。Lean的 `induction` 策略自动生成归纳子目标。

---

### 练习3

证明：加法结合律

```lean
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]
```

**策略解析**：对第三个参数 $c$ 进行归纳。
- **奠基**：$(a + b) + 0 = a + b = a + (b + 0)$
- **步骤**：$(a + b) + \text{succ}(c) = \text{succ}((a + b) + c) = \text{succ}(a + (b + c)) = a + \text{succ}(b + c) = a + (b + \text{succ}(c))$

连续使用三次 `Nat.add_succ` 分别展开：
1. $(a + b) + \text{succ}(c) = \text{succ}((a + b) + c)$
2. $a + \text{succ}(b + c) = \text{succ}(a + (b + c))$... 实际上需要更仔细分析

更准确的重写链：
- $(a + b) + \text{succ}(c) = \text{succ}((a + b) + c)$（第一个 `Nat.add_succ`）
- 由 `ih`，$(a + b) + c = a + (b + c)$
- $a + (b + \text{succ}(c)) = a + \text{succ}(b + c) = \text{succ}(a + (b + c))$

Lean的重写会自动处理这些等式链。

---

### 练习4（补充）

证明：乘法对加法的分配律

```lean
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ c ih =>
    rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, Nat.add_assoc]
```

**策略解析**：
- **奠基**：$a \cdot (b + 0) = a \cdot b = a \cdot b + 0 = a \cdot b + a \cdot 0$
- **步骤**：$a \cdot (b + \text{succ}(c)) = a \cdot \text{succ}(b + c) = a \cdot (b + c) + a = (a \cdot b + a \cdot c) + a = a \cdot b + (a \cdot c + a) = a \cdot b + a \cdot \text{succ}(c)$

---

## 中级练习

### 练习5

证明：对任意列表$l$，$l ++ [] = l$

```lean
theorem list_append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rw [List.cons_append, ih]
```

**策略解析**：
- **奠基**：`[] ++ [] = []`（`rfl`）
- **步骤**：`[h] ++ t ++ [] = [h] ++ (t ++ []) = [h] ++ t`
  - `List.cons_append`：`([h] ++ t) ++ [] = [h] ++ (t ++ [])`... 实际上 `List.cons_append` 展开的是 `(h :: t) ++ l = h :: (t ++ l)`

更准确的理解：
- `(h :: t) ++ [] = h :: (t ++ [])`（由 `cons_append`）
- $= h :: t$（由归纳假设 `ih`）

---

### 练习6

证明：列表长度在map下保持不变

```lean
theorem map_length (f : α → β) (l : List α) :
    (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rw [List.map_cons, List.length_cons, List.length_cons, ih]
```

**策略解析**：
- **奠基**：`[].map f = []`，长度均为 0
- **步骤**：
  - `List.map_cons`：`(h :: t).map f = f h :: t.map f`
  - `List.length_cons`（两次）：`length(f h :: t.map f) = length(t.map f) + 1 = length(t) + 1 = length(h :: t)`

---

## 高级练习

### 练习7（补充）

证明：对任意命题 $P$，$P \lor \neg P$（排中律在 `Classical` 环境下）

```lean
open Classical

theorem em' (P : Prop) : P ∨ ¬P := by
  apply em
```

**策略解析**：Lean的构造逻辑默认不包含排中律。需要 `open Classical` 来使用经典逻辑的工具。`em` 是 "excluded middle" 的缩写，是 `Classical` 命名空间中的定理。

**构造数学 vs 经典数学**：
- 构造数学中，要证明 $P \lor Q$，必须能判定哪个为真
- 经典数学接受 "$P$ 要么为真要么为假" 作为公理

---

### 练习8（补充）

证明：不存在最大的自然数

```lean
theorem no_max_nat : ¬∃ n : Nat, ∀ m : Nat, m ≤ n := by
  intro h
  rcases h with ⟨n, hn⟩
  have h := hn (n + 1)
  linarith
```

**策略解析**：
1. `intro h`：假设存在最大自然数
2. `rcases h with ⟨n, hn⟩`：提取该自然数 $n$ 和性质 $\forall m, m \leq n$
3. `have h := hn (n + 1)`：将 $m = n + 1$ 代入，得到 $n + 1 \leq n$
4. `linarith`：线性算术求解器推出矛盾（$n + 1 \leq n$ 不成立）

---

## 证明策略速查表

| 策略 | 用途 | 示例 |
|------|------|------|
| `rfl` | 自反性，定义等式 | `n + 0 = n` |
| `rw [lemma]` | 用等式重写目标 | `rw [Nat.add_comm]` |
| `induction x with` | 数学归纳法 | 自然数、列表上的证明 |
| `intro h` | 引入假设（→, ∀, ¬） | 证明蕴含式 |
| `apply lemma` | 用定理匹配目标 | `apply Nat.le_add_right` |
| `linarith` | 线性不等式自动求解 | $n + 1 \leq n$ 推出矛盾 |
| `simp` | 简化表达式 | 自动化简常用等式 |
| `tauto` | 命题逻辑自动证明 | 重言式判定 |
| `rcases` | 分解复杂结构 | `∃, ∧, ∨` 的消去 |
| `have h : ...` | 引入中间结论 | 分步证明 |

---

**适用**：docs/09-形式化证明/
