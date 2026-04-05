---
title: FormalMath Lean4 最佳实践示例
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath Lean4 最佳实践示例

本文档展示Lean4形式化数学的最佳实践，以TaylorTheorem.lean为标杆。

## 1. 文件结构模板

```lean
/-
# 定理名称

## 数学背景

简要介绍定理的数学背景、历史意义和应用领域。

## 核心结果
- 主要定理1
- 主要定理2

## Mathlib4对应
- `Mathlib.Path.To.Module`

## 参考
- 经典教材引用
-/

import Mathlib.Module1
import Mathlib.Module2

namespace TheoremName

open NameSpace1 NameSpace2

variable {X : Type*} [TypeClass X]

-- 核心定义

-- 主要定理

-- 辅助引理

end TheoremName
```

## 2. 命名规范

### 2.1 类型和结构
```lean
-- ✅ 正确: PascalCase
structure SmoothManifold
class IsNoetherianRing
def FundamentalGroup
```

### 2.2 定理和引理
```lean
-- ✅ 正确: snake_case
theorem taylor_theorem_lagrange
theorem sylow_first_theorem
lemma continuous_add
```

### 2.3 变量命名
```lean
-- ✅ 正确: 语义化命名
variable {f g : ℝ → ℝ}  -- 函数
variable {x y : ℝ}       -- 点/值
variable {n m : ℕ}       -- 自然数
variable {G H : Type*} [Group G]  -- 群
```

## 3. 文档注释规范

### 3.1 文件头文档
```lean
/-
# 中心极限定理

## 数学背景

中心极限定理（CLT）是概率论中最重要的定理之一。
它表明，大量独立随机变量之和，经适当标准化后，
收敛于正态分布。

## 核心结果
- Lindeberg-Lévy CLT（i.i.d.情形）
- Lindeberg-Feller CLT（独立不同分布）
- Berry-Esseen定理（收敛速度）

## Mathlib4对应
- `Mathlib.Probability.CentralLimitTheorem`
- `Mathlib.Probability.Distributions.Gaussian`

## 参考
- Durrett, R. "Probability: Theory and Examples"
-/
```

### 3.2 定理文档
```lean
/-
## 泰勒定理（带拉格朗日余项）

**定理陈述**：设函数f在区间[a,x]上有连续的n+1阶导数，则存在ξ∈(a,x)使得：

f(x) = Σ(k=0 to n)[f⁽ᵏ⁾(a)/k!]·(x-a)ᵏ + Rₙ(x)

其中余项Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)/(n+1)!·(x-a)ⁿ⁺¹

**证明要点**：
1. 构造辅助函数g(t)
2. 应用柯西中值定理
3. 通过递推得到余项表达式

**参考**: Mathlib.Analysis.Calculus.Taylor
-/
```

## 4. 证明编写规范

### 4.1 证明结构
```lean
theorem example_theorem (h : Hypothesis) : Conclusion := by
  -- 步骤1: 展开定义
  simp only [definition]
  
  -- 步骤2: 应用已知引理
  apply known_lemma
  
  -- 步骤3: 验证条件
  · -- 子目标1
    exact condition1
  · -- 子目标2
    exact condition2
  
  -- 步骤4: 完成证明
  ring
```

### 4.2 替代`sorry`的最佳实践
```lean
-- ❌ 避免: 直接使用sorry
theorem bad_example : Statement := by
  sorry

-- ✅ 正确: 提供详细注释说明证明思路
theorem good_example : Statement := by
  -- 证明思路:
  -- 1. 首先证明辅助引理 X
  -- 2. 然后应用定理 Y
  -- 3. 最后验证条件 Z
  -- TODO: 需要Mathlib中的某个性质
  sorry
```

## 5. 导入管理

### 5.1 导入顺序
```lean
-- 1. Mathlib核心
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic

-- 2. 分析学模块
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

-- 3. 项目内部模块（如有）
-- import Project.HelperModule
```

### 5.2 最小导入原则
```lean
-- ✅ 正确: 只导入需要的模块
import Mathlib.Analysis.Calculus.Taylor

-- ❌ 避免: 导入整个大模块
-- import Mathlib.Analysis -- 过于宽泛
```

## 6. 类型类实例

### 6.1 实例声明
```lean
instance fundamentalGroupGroup : Group (π₁(X, x₀)) where
  mul := ...
  one := ...
  inv := ...
  mul_assoc := by
    -- 证明结合律
    sorry
  one_mul := by
    -- 证明单位元性质
    sorry
  -- ...
```

### 6.2 类型类派生
```lean
-- ✅ 正确: 显式声明派生
def TangentSpace (n : ℕ) [SmoothManifold M n] (p : M) : Type _ := ...

instance : AddCommGroup (TangentSpace n p) where
  -- 实现群结构
```

## 7. 常用Tactic模式

### 7.1 代数简化
```lean
-- 简化表达式
simp only [definition1, definition2]

-- 域运算
field_simp
ring

-- 线性运算
linarith
nlinarith
```

### 7.2 结构证明
```lean
-- 构造函数
constructor
· -- 证明第一部分
  ...
· -- 证明第二部分
  ...

-- 存在性证明
use value
-- 验证条件
```

### 7.3 归纳证明
```lean
induction n with
| zero =>
  -- 基础情形
  simp
| succ n ih =>
  -- 归纳步骤
  rw [definition]
  exact ih
```

## 8. 代码格式化

### 8.1 缩进和对齐
```lean
-- ✅ 正确: 2空格缩进，对齐参数
theorem well_formatted 
    (h1 : Condition1)
    (h2 : Condition2)
    (h3 : Condition3) :
    Conclusion := by
  step1
  step2

-- ❌ 避免: 不一致的缩进
theorem badly_formatted (h1:Condition1)(h2:Condition2):Conclusion:=by
step1
    step2
```

### 8.2 行长限制
```lean
-- ✅ 正确: 适当换行
theorem long_statement :
    VeryLongConditionThatNeedsToBeSplit := by
  ...

-- ❌ 避免: 过长的行
theorem bad_statement : VeryLongConditionThatGoesOnAndOnAndOnWithoutBreaking := by
```

## 9. 测试和验证

### 9.1 简单测试
```lean
-- 在文件末尾添加简单测试
#check taylorPolynomial
#eval gammaIntegral 1  -- 应该等于 1
```

### 9.2 编译检查
```bash
# 检查单个文件
lean --check FormalMath/TaylorTheorem.lean

# 构建整个项目
lake build
```

## 10. 完整示例文件

参见: `FormalMath/TaylorTheorem.lean`

该文件展示了：
- ✅ 完整的文件头文档
- ✅ 清晰的定义结构
- ✅ 详细的定理证明
- ✅ 正确的命名规范
- ✅ 适当的注释说明

---

**参考**: Mathlib4代码风格指南
