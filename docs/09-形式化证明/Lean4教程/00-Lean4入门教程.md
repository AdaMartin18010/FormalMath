---
title: "Lean4入门教程"
msc_primary: "03"
---

# Lean4入门教程

## 概述

本教程旨在帮助数学和计算机科学领域的学习者快速掌握Lean4定理证明器。

## 1. Lean4简介

Lean4是微软研究院开发的定理证明器，结合了依赖类型理论和高性能编译。

## 2. 基础语法

```lean
-- 定义定理
theorem hello : 1 + 1 = 2 := by rfl

-- 使用策略
example (n : Nat) : n + 0 = n := by simp
```

## 3. 证明策略

| 策略 | 功能 |
|------|------|
| `rfl` | 自反性 |
| `simp` | 简化 |
| `rw` | 重写 |
| `linarith` | 线性算术 |
| `ring` | 环简化 |

## 4. Mathlib4使用

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
```

## 5. 学习资源

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)
