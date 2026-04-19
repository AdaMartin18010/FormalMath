---
title: Lean4形式化证明习题与练习
msc_primary: 68

  - 68V15
---

# Lean4形式化证明习题与练习

## 基础练习

### 练习1

证明：对任意自然数$n$，$n + 0 = n$

```lean
theorem add_zero_n (n : Nat) : n + 0 = n := by
  rfl
```

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

### 练习3

证明：加法结合律

```lean
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]
```

---

## 中级练习

### 练习4

证明：对任意列表$l$，$l ++ [] = l$

```lean
theorem list_append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rw [List.cons_append, ih]
```

### 练习5

证明：列表长度在map下保持不变

```lean
theorem map_length (f : α → β) (l : List α) :
    (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rw [List.map_cons, List.length_cons, List.length_cons, ih]
```

---

**适用**：docs/09-形式化证明/
