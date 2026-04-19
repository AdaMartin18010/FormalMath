---
title: "Mathlib4使用指南"
msc_primary: "03"
---

# Mathlib4使用指南

## 导入模块

```lean
-- 基础数学
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

-- 代数
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

-- 分析
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
```

## 查找定理

### 使用#check

```lean
#check Nat.add_comm
#check Real.exp_add
```

### 使用#find

```lean
#find _ + _ = _ + _
```

## 常用定理

| 领域 | 定理 | 模块 |
|------|------|------|
| 自然数 | `Nat.add_comm` | `Data.Nat.Basic` |
| 整数 | `Int.mul_comm` | `Data.Int.Basic` |
| 实数 | `Real.exp_add` | `SpecialFunctions.Exp` |
| 群论 | `mul_inv_cancel` | `Algebra.Group.Basic` |
| 分析 | `hasDerivAt_id` | `Calculus.Deriv.Basic` |

## 贡献指南

1. 阅读贡献文档
2. 遵循编码规范
3. 编写详细文档
4. 提交PR前检查CI
