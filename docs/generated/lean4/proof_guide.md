---
msc_primary: 00

  - 00A99
title: Lean4 证明编写指南
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# Lean4 证明编写指南

**生成时间**: 2026-04-04 13:07:54

## 常用证明策略

### 1. 直接证明 (tactic)

```lean4
example : p → p := by
  intro hp
  exact hp

```

### 2. 反证法 (by_contra)

```lean4
example : ¬¬p → p := by
  intro hnnp
  by_contra hnp
  exact hnnp hnp

```

### 3. 归纳法 (induction)

```lean4
theorem nat_add_zero : ∀ n : ℕ, n + 0 = n := by
  intro n
  induction n with

  | zero => rfl
  | succ n ih => 

    rw [Nat.add_succ]
    rw [ih]

```

### 4. 情况分析 (cases)

```lean4
example : p ∨ q → q ∨ p := by
  intro h
  cases h with

  | inl hp => 

    apply Or.inr
    exact hp

  | inr hq =>

    apply Or.inl
    exact hq

```

## 证明状态检查清单

- [ ] 所有 `sorry` 是否已替换为实际证明
- [ ] 是否添加了适当的文档注释 (`/-- ... -/`)
- [ ] 定理命名是否符合规范
- [ ] 是否使用了正确的导入语句
- [ ] 证明是否通过了 `lake build`

## 定理命名规范

| 类型 | 命名示例 | 说明 |
|------|----------|------|
| 基本定理 | `theoremName` | 驼峰命名 |
| 引理 | `lemmaName` | 辅助结果 |
| 定义 | `defName` | 新定义 |
| 实例 | `instName` | 类型类实例 |

## 形式化覆盖率

- **已完成定理**: 0
- **未完成定理**: 43
- **总定理数**: 43
- **完成率**: 0.0%

---
*由 FormalMath Lean4文档生成器创建*
