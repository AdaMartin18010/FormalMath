---
msc_primary: 68V20
msc_secondary:
- 03B35
title: Lean4基础证明示例 - 工作示例
processed_at: '2026-04-08'
---
# Lean4基础证明示例 - 工作示例

**类型**: 证明示例
**领域**: 形式化证明
**难度**: L1
**前置知识**: Lean4基础语法
**创建日期**: 2026年4月8日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | Lean4中基本证明策略的应用 |
| **领域** | 形式化证明 / 定理证明 |
| **MSC** | 68V20（形式化数学）、03B35（自动推理） |
| **相关概念** | 形式化证明、Lean4、类型论 |

---

## 题目

用Lean4证明下列命题：

1. 对任意命题 $P, Q$，$P \land Q \to Q \land P$（合取交换律）
2. 对任意自然数 $n$，$n + 0 = n$
3. 对任意自然数 $n, m$，$(n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2$

---

## 完整解答（工作示例）

### Lean4基本策略

- `intro`：引入假设
- `exact`：精确匹配目标
- `apply`：应用引理或定理
- `simp`：简化表达式
- `rw`：重写（rewrite）
- `linarith`：线性算术自动证明

---

**解答 1**：合取交换律

```lean
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hp hq =>
    exact ⟨hq, hp⟩
```

**证明说明**：
- `intro h`：引入假设 $h : P \land Q$
- `cases h with`：对合取进行解构
- `⟨hq, hp⟩`：构造 $Q \land P$ 的证明对

**简化版本**：
```lean
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩
```

---

**解答 2**：加法零元

```lean
import Mathlib

theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [Nat.add_succ, ih]
```

**证明说明**：
- `induction n with`：对 $n$ 进行归纳
- **基例** `zero`：`0 + 0 = 0` 由 `rfl`（自反性）得证
- **归纳步** `succ n`：
  - `ih`：归纳假设 $n + 0 = n$
  - `Nat.add_succ`：$(n+1) + 0 = (n + 0) + 1$
  - `simp` 自动应用归纳假设

**使用Mathlib的简化版本**：
```lean
theorem add_zero' (n : ℕ) : n + 0 = n := by
  simp
```

---

**解答 3**：平方展开公式

```lean
theorem square_expand (n m : ℕ) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  ring
```

**证明说明**：
- `ring`：环结构自动证明策略
- 自动展开 $(n + m)^2$ 并整理为标准形式

**手动证明版本**：
```lean
theorem square_expand' (n m : ℕ) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  calc
    (n + m) ^ 2 = (n + m) * (n + m) := by rw [pow_two]
    _ = n * n + n * m + m * n + m * m := by rw [mul_add, add_mul, add_mul]
    _ = n ^ 2 + 2 * n * m + m ^ 2 := by 
      ring_nf
      <;> simp [pow_two, mul_comm]
      <;> ring
```

---

## 关键步骤说明

- **结构证明**：`intro` 和 `cases`/`rintro` 进行假设管理
- **归纳证明**：`induction` 处理自然数性质
- **自动化**：`simp`、`ring`、`linarith` 自动处理计算
- **计算证明**：`calc` 用于逐步等式推导

---

## 相关概念链接

- [形式化证明](../../../docs/09-形式化证明/01-Lean4/01-Lean4.md)
- [类型论](../../../docs/01-基础数学/03-类型论/01-类型论.md)
