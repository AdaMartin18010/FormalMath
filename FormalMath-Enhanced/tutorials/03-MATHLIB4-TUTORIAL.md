---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Mathlib4 学习教程

**预计阅读时间**: 45分钟
**目标读者**: 希望学习形式化数学、使用Lean 4和Mathlib4的学习者

---

## 目录

- [Mathlib4 学习教程](#mathlib4-学习教程)
  - [目录](#目录)
  - [1. 如何选择定理学习](#1-如何选择定理学习)
    - [1.1 选择标准](#11-选择标准)
    - [1.2 项目中的定理分类](#12-项目中的定理分类)
    - [1.3 推荐学习路径](#13-推荐学习路径)
  - [2. 从注释到Lean4代码](#2-从注释到lean4代码)
    - [2.1 注释文档结构](#21-注释文档结构)
    - [关键概念](#关键概念)
    - [证明思路](#证明思路)
    - [完整证明](#完整证明)
  - [相关定理](#相关定理)
  - [练习](#练习)
    - [符号重载](#符号重载)
    - [证明策略 (Tactics)](#证明策略-tactics)
  - [3. 实践：理解一个定理的完整流程](#3-实践理解一个定理的完整流程)
    - [3.1 案例：费马小定理](#31-案例费马小定理)
      - [Step 1: 阅读定理陈述](#step-1-阅读定理陈述)
      - [Step 2: 理解直观意义](#step-2-理解直观意义)
      - [Step 3: 阅读Mathlib4实现](#step-3-阅读mathlib4实现)
      - [Step 4: 分析证明结构](#step-4-分析证明结构)
      - [Step 5: 本地验证](#step-5-本地验证)
    - [3.2 案例：谱定理（Spectral Theorem）](#32-案例谱定理spectral-theorem)
      - [定理陈述](#定理陈述)
      - [Lean 4实现](#lean-4实现)
      - [学习要点](#学习要点)
  - [4. 如何在Lean4中验证](#4-如何在lean4中验证)
    - [4.1 环境配置](#41-环境配置)
      - [安装Lean 4](#安装lean-4)
      - [配置编辑器](#配置编辑器)
    - [4.2 创建验证项目](#42-创建验证项目)
    - [4.3 验证定理](#43-验证定理)
    - [4.4 常见验证方法](#44-常见验证方法)
      - [使用native\_decide验证具体数值](#使用native_decide验证具体数值)
      - [使用simp简化表达式](#使用simp简化表达式)
      - [使用linarith处理不等式](#使用linarith处理不等式)
    - [4.5 调试技巧](#45-调试技巧)
      - [查看中间结果](#查看中间结果)
      - [使用show查看目标](#使用show查看目标)
  - [5. 进阶学习路径](#5-进阶学习路径)
    - [5.1 从理解到贡献](#51-从理解到贡献)
    - [5.2 深入Mathlib4](#52-深入mathlib4)
      - [推荐学习资源](#推荐学习资源)
      - [进阶主题](#进阶主题)
  - [6. 练习题](#6-练习题)
    - [基础练习](#基础练习)
    - [进阶练习](#进阶练习)
    - [实践项目](#实践项目)

---

## 1. 如何选择定理学习

### 1.1 选择标准

```
┌─────────────────────────────────────────────────────────────┐
│                    定理选择决策树                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. 你的数学背景？                                          │
│     ├── 高中 → 基础代数/数论定理                            │
│     ├── 本科 → 线性代数/分析学定理                          │
│     └── 研究生 → 抽象代数/拓扑学定理                        │
│                                                             │
│  2. 你的Lean经验？                                          │
│     ├── 初学者 → 选择注释详细的简单定理                     │
│     └── 有经验 → 选择证明复杂的定理                         │
│                                                             │
│  3. 学习目标？                                              │
│     ├── 理解概念 → 选择有直观解释的定理                     │
│     ├── 学习证明技巧 → 选择有多种证明的定理                 │
│     └── 研究前沿 → 选择高级专题定理                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 项目中的定理分类

| 领域 | 定理 | 难度 | 前置知识 | 文件路径 |
|------|------|------|----------|----------|
| **代数学** |||||
| | 拉格朗日定理 | ⭐⭐ | 群论基础 | `Algebra/lagrange-theorem.md` |
| | 群同态基本定理 | ⭐⭐⭐ | 正规子群 | `Algebra/first-isomorphism-theorem.md` |
| | 西罗定理 | ⭐⭐⭐⭐ | 群作用 | `Algebra/sylow-theorems.md` |
| | 中国剩余定理 | ⭐⭐ | 环论基础 | `Algebra/chinese-remainder.md` |
| **分析学** |||||
| | 柯西积分公式 | ⭐⭐⭐ | 复分析基础 | `Analysis/cauchy-integral-formula.md` |
| | 留数定理 | ⭐⭐⭐⭐ | 复变函数 | `Analysis/residue-theorem.md` |
| | 微分中值定理 | ⭐⭐ | 微积分 | `Calculus/mean-value-theorem.md` |
| **数论** |||||
| | 费马小定理 | ⭐⭐ | 模运算 | `NumberTheory/fermat-little-theorem.md` |
| | 二次互反律 | ⭐⭐⭐ | 二次剩余 | `NumberTheory/quadratic-reciprocity.md` |
| **线性代数** |||||
| | 谱定理 | ⭐⭐⭐ | 内积空间 | `LinearAlgebra/spectral-theorem.md` |
| | 凯莱-哈密顿定理 | ⭐⭐⭐ | 特征多项式 | `LinearAlgebra/cayley-hamilton.md` |
| | SVD | ⭐⭐⭐ | 矩阵分解 | `LinearAlgebra/svd.md` |

### 1.3 推荐学习路径

**路径A: 代数学路线**（适合抽象代数初学者）

```
第1周: 拉格朗日定理
    └── 理解子群、陪集、指数概念

第2周: 群同态基本定理
    └── 理解同态、核、商群

第3周: 中国剩余定理
    └── 理解环同态、理想

第4周: 西罗定理
    └── 理解群作用、轨道
```

**路径B: 分析学路线**（适合分析学方向）

```
第1周: 微分中值定理
    └── 复习微积分基础

第2周: 柯西积分公式
    └── 学习复变函数基础

第3周: 留数定理
    └── 掌握围道积分
```

**路径C: 数论路线**（适合竞赛数学背景）

```
第1周: 费马小定理
    └── 理解模运算

第2周: 二次互反律
    └── 学习Legendre符号

第3周: 素数定理（选学）
    └── 了解解析数论方法
```

---

## 2. 从注释到Lean4代码

### 2.1 注释文档结构

每个定理注释包含以下部分：

```markdown
# 定理名称 (Theorem Name)

## 定理陈述
[自然语言陈述]

## 直观理解
[几何解释、例子、动机]

## 历史背景
[数学家、年代、发展脉络]

## Mathlib4 实现
[Lean 4 代码]

### 类型签名
```lean
theorem name (参数 : 类型) : 结论
```

### 关键概念

- 概念1: 解释
- 概念2: 解释

### 证明思路

1. 步骤1
2. 步骤2

### 完整证明

```lean
[完整Lean代码]
```

## 相关定理

- [相关定理1](link)
- [相关定理2](link)

## 练习

[验证练习]

```

### 2.2 自然语言到形式化代码的对应

**示例: 拉格朗日定理**

| 自然语言 | Lean 4 | 说明 |
|----------|--------|------|
| 设G为有限群 | `(G : Type) [Group G] [Finite G]` | 类型参数+类型类实例 |
| H是G的子群 | `(H : Subgroup G)` | Subgroup类型 |
| \|H\|整除\|G\| | `Nat.card H ∣ Nat.card G` | 整除关系 |

**示例: 费马小定理**

| 自然语言 | Lean 4 | 说明 |
|----------|--------|------|
| 设p为素数 | `(p : ℕ) (hp : Nat.Prime p)` | 自然数+素数条件 |
| a不被p整除 | `(a : ℤ) (ha : ¬p ∣ a)` | 整数+不整除条件 |
| a^(p-1) ≡ 1 (mod p) | `a^(p-1) ≡ 1 [ZMOD p]` | 模同余记号 |

### 2.3 理解Lean代码的关键

#### 类型类 (Type Classes)

```lean
-- 群结构
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_left_inv : ∀ a, mul (inv a) a = one
```

#### 符号重载

```lean
-- Lean中使用标准数学符号
#check a * b      -- 群乘法
check a⁻¹        -- 逆元
check 1          -- 单位元
#check a • b     -- 群作用
```

#### 证明策略 (Tactics)

```lean
-- 基本策略
intro      -- 引入假设
exact      -- 精确匹配
calc       -- 计算链
rw         -- 重写
simp       -- 简化
linarith   -- 线性算术
```

---

## 3. 实践：理解一个定理的完整流程

### 3.1 案例：费马小定理

#### Step 1: 阅读定理陈述

打开文件: `02-Mathlib4-Annotations/NumberTheory/fermat-little-theorem.md`

**自然语言陈述**:
> 如果p是素数，a是不被p整除的整数，那么 a^(p-1) ≡ 1 (mod p)。

#### Step 2: 理解直观意义

**例子验证**:

- p = 5, a = 2
- 2^4 = 16 ≡ 1 (mod 5) ✓
- p = 7, a = 3
- 3^6 = 729 = 104×7 + 1 ≡ 1 (mod 7) ✓

**历史背景**: Pierre de Fermat于1640年提出，1736年由Euler证明。

#### Step 3: 阅读Mathlib4实现

```lean
-- Mathlib4中的费马小定理
import Mathlib

theorem ZMod.pow_card_sub_one_eq_one {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  -- 证明基于(Z/pZ)*构成一个阶为p-1的乘法群
  -- 应用拉格朗日定理
  have h : a ^ (Fintype.card ((ZMod p)ˣ)) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    simpa using ha
  simpa using h
```

#### Step 4: 分析证明结构

```
证明思路:
1. 考虑有限域 Z/pZ 的非零元构成的乘法群
2. 这个群的阶为 p-1
3. 由拉格朗日定理，任意元素的阶整除群的阶
4. 因此 a^(p-1) = 1
```

#### Step 5: 本地验证

```bash
# 创建测试文件
cat > test_fermat.lean << 'EOF'
import Mathlib

-- 验证费马小定理的具体例子
example : (2 : ZMod 5) ^ 4 = 1 := by
  native_decide

example : (3 : ZMod 7) ^ 6 = 1 := by
  native_decide

-- 一般形式
theorem fermat_test {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one a ha
EOF

# 验证
lean test_fermat.lean
```

### 3.2 案例：谱定理（Spectral Theorem）

#### 定理陈述

> 设T是有限维复内积空间上的正规算子，则存在由T的特征向量组成的标准正交基。

#### Lean 4实现

```lean
import Mathlib

-- 正规算子的谱定理
theorem LinearMap.IsNormal.exists_orthonormalBasis_eigenvectors
    {V : Type} [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (hT : T.IsNormal) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
    ∀ i, ∃ α, T (b i) = α • b i := by
  -- 证明使用正规算子的谱分解
  sorry  -- 完整证明较长
```

#### 学习要点

1. **类型理解**:
   - `InnerProductSpace ℂ V`: V是复内积空间
   - `FiniteDimensional ℂ V`: V是有限维的
   - `V →ₗ[ℂ] V`: V到V的ℂ-线性映射

2. **结论理解**:
   - 存在标准正交基 `b`
   - 基中每个向量都是T的特征向量

---

## 4. 如何在Lean4中验证

### 4.1 环境配置

#### 安装Lean 4

**Windows**:

```powershell
# 使用elan安装器
curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
```

**验证安装**:

```bash
lean --version
# 输出: Lean (version 4.7.0, commit xxxxx, Release)
```

#### 配置编辑器

**VS Code**:

1. 安装VS Code
2. 在扩展商店搜索 "Lean 4" 并安装
3. 打开Lean文件时自动激活语言支持

### 4.2 创建验证项目

```bash
# 创建新项目
lake new formalmath-test math

# 进入项目目录
cd formalmath-test

# 更新依赖
lake update

# 构建项目
lake build
```

### 4.3 验证定理

**创建测试文件**: `FormalmathTest/Basic.lean`

```lean
import Mathlib

-- 导入项目命名空间
namespace FormalmathTest

-- 测试拉格朗日定理的特例
section LagrangeTest

-- 验证S_3的子群阶整除6
-- S_3的阶为6，其Sylow 2-子群阶为2，Sylow 3-子群阶为3
def S3_order : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Equiv.Perm.permGroup, Nat.card_perm]

end LagrangeTest

-- 测试费马小定理
section FermatTest

-- 验证具体例子
example : (2 : ZMod 5) ^ 4 = 1 := by
  native_decide

example : (3 : ZMod 7) ^ 6 = 1 := by
  native_decide

-- 测试不满足条件的情况（应该失败）
-- example : (5 : ZMod 5) ^ 4 = 1 := by native_decide  -- 5 ≡ 0 (mod 5)

end FermatTest

-- 测试微分中值定理
section MVTTest

open Real

-- 验证sin(x)在[0, π]上满足中值定理条件
example : ∃ c ∈ Set.Ioo 0 Real.pi, deriv sin c = (sin Real.pi - sin 0) / (Real.pi - 0) := by
  use Real.pi / 2
  constructor
  · -- 证明 π/2 ∈ (0, π)
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  · -- 验证导数条件
    simp [deriv_sin]
    field_simp
    linarith [Real.pi_pos]

end MVTTest

end FormalmathTest
```

### 4.4 常见验证方法

#### 使用native_decide验证具体数值

```lean
-- 自动计算验证
example : (2 : ZMod 5) ^ 4 = 1 := by native_decide
example : Nat.Prime 17 := by native_decide
```

#### 使用simp简化表达式

```lean
-- 使用simp策略简化
example (n : ℕ) : n + 0 = n := by simp
example (G : Type) [Group G] (a : G) : a * 1 = a := by simp
```

#### 使用linarith处理不等式

```lean
-- 线性算术求解器
example (a b c : ℝ) (h1 : a < b) (h2 : b < c) : a < c := by
  linarith
```

### 4.5 调试技巧

#### 查看中间结果

```lean
example (n : ℕ) : n + 0 = n := by
  dbg_trace "Before simp: n + 0 = n"
  simp
  dbg_trace "After simp: n = n"
```

#### 使用show查看目标

```lean
example (n : ℕ) : n + 0 = n := by
  show n + 0 = n  -- 显式显示当前目标
  simp
```

---

## 5. 进阶学习路径

### 5.1 从理解到贡献

```
阶段1: 阅读理解 (1-2个月)
├── 阅读10+个定理注释
├── 在本地验证5+个定理
└── 完成所有练习题

阶段2: 修改尝试 (2-3个月)
├── 修改现有证明，理解变化
├── 添加自己的注释和例子
└── 修复小错误

阶段3: 独立贡献 (3+个月)
├── 为新定理创建注释
├── 参与代码审查
└── 帮助改进文档
```

### 5.2 深入Mathlib4

#### 推荐学习资源

| 资源 | 链接 | 说明 |
|------|------|------|
| Mathlib4文档 | https://leanprover-community.github.io/mathlib4_docs/ | API文档 |
| Lean 4手册 | https://lean-lang.org/lean4/doc/ | 官方文档 |
| Mathematics in Lean | https://leanprover-community.github.io/mathematics_in_lean/ | 教程书籍 |
| Lean Zulip | https://leanprover.zulipchat.com/ | 社区讨论 |

#### 进阶主题

```
主题1: 泛型编程
├── 类型类推导
├── 类型级编程
└── 范畴论抽象

主题2: 证明自动化
├── 元编程 (Meta)
├── 自定义策略
└── 决策过程

主题3: 特定领域
├── 代数几何
├── 代数拓扑
└── 分析学高级主题
```

---

## 6. 练习题

### 基础练习

**练习1**: 阅读并验证拉格朗日定理

1. 打开文件 `02-Mathlib4-Annotations/Algebra/lagrange-theorem.md`
2. 理解定理的自然语言陈述
3. 阅读Mathlib4实现
4. 在本地Lean环境中创建一个测试文件，验证定理的特例

<details>
<summary>提示</summary>

```lean
import Mathlib

-- 验证 S_3 的阶为6
example : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp
```

</details>

**练习2**: 翻译自然语言到Lean

将以下数学陈述翻译为Lean 4代码：

a) "对于任意实数x, y，有 |x + y| ≤ |x| + |y|"

<details>
<summary>答案</summary>

```lean
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  apply abs_add
```

</details>

b) "如果n是偶数，那么n²也是偶数"

<details>
<summary>答案</summary>

```lean
theorem even_square {n : ℕ} (h : Even n) : Even (n ^ 2) := by
  rcases h with ⟨k, hk⟩
  use 2 * k ^ 2
  rw [hk]
  ring
```

</details>

### 进阶练习

**练习3**: 证明组合恒等式

在Lean 4中证明：∑(k=0到n) C(n,k) = 2^n

<details>
<summary>答案</summary>

```lean
import Mathlib

open Nat Finset BigOperators

theorem sum_choose_eq_pow_two (n : ℕ) :
    ∑ k in range (n + 1), Nat.choose n k = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    simp [Nat.choose_succ_succ]
    ring
```

</details>

**练习4**: 创建自定义定理注释

选择一个Mathlib4中的定理（如`Nat.Prime.dvd_choose_self`），按照项目模板创建完整的注释文档。

### 实践项目

**项目**: 形式化一道IMO题目

1. 从 `03-IMO-Competition/` 中选择一道题目
2. 理解题目的数学内容
3. 在Lean 4中形式化该问题的陈述
4. 尝试证明（或部分证明）
5. 记录学习笔记

---

**完成本教程后，你应该能够：**

- ✅ 选择适合自己水平的定理学习
- ✅ 理解自然语言与Lean代码的对应关系
- ✅ 在本地验证Mathlib4中的定理
- ✅ 独立阅读和注释新的定理

继续学习下一教程: [IMO备赛教程](./04-IMO-PREPARATION.md)

---

*最后更新: 2026年4月*
*教程版本: v1.0*
