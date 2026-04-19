---
title: "Lean4入门教程"
msc_primary: "03"
---

# Lean4依赖类型理论入门与形式化数学实践

## 1. 引言

Lean4是由微软研究院Leonardo de Moura团队开发的定理证明器与通用编程语言。它基于**归纳构造演算**（Calculus of Inductive Constructions, CIC），将Martin-Löf类型论的构造性框架与经典的数学推理能力相结合，通过庞大的数学库Mathlib4支持从基础代数到高级代数几何的形式化。

Lean4的独特之处在于其**双重身份**：既是严格的逻辑系统（保证证明的绝对正确性），又是高效的通用编程语言（编译到C代码，支持元编程与宏系统）。这一统一使得Lean4成为形式化数学、程序验证以及教学演示的理想平台。

本文系统介绍Lean4的类型理论核心、证明语法与Mathlib4生态系统，并通过实例展示如何形式化基础数学定理。

---

## 2. 严格数学定义

### 2.1 依赖类型基础

**定义 2.1（类型层级）**
Lean4的类型宇宙形成累积层级：
$$\text{Prop} = \text{Sort 0} : \text{Type 0} = \text{Sort 1} : \text{Type 1} = \text{Sort 2} : \cdots$$

- $\text{Prop}$：证明无关的命题宇宙。若 $P: \text{Prop}$，则对任意证明 $p, q: P$，有 $p = q$（proof irrelevance）
- $\text{Type}\, u$：数据类型宇宙，可存储计算信息

**定义 2.2（依赖函数类型）**
设 $A: \text{Type}$，$B: A \to \text{Type}$。**依赖函数类型**记为
$$(x: A) \to B(x) \quad \text{或} \quad \forall (x: A), B(x)$$
元素为函数 $f$ 使得 $f(a): B(a)$ 对所有 $a: A$。

**定义 2.3（归纳类型）**
归纳类型由**构造子**生成。自然数 $\mathbb{N}$ 定义为：
```lean
inductive Nat
  | zero : Nat
  | succ (n : Nat) : Nat
```
其**归纳原理**为：
$$\forall P: \mathbb{N} \to \text{Prop},\; P(0) \to (\forall n,\; P(n) \to P(n+1)) \to \forall n,\; P(n)$$

### 2.2 Curry-Howard对应

**定义 2.4（命题即类型）**
在Lean4中，逻辑命题对应类型，证明对应项：

| 逻辑 | 类型 |
|------|------|
| $A \wedge B$ | $A \times B$（积类型） |
| $A \vee B$ | $A \oplus B$（和类型） |
| $A \to B$ | $A \to B$（函数类型） |
| $\forall x, P(x)$ | $(x: A) \to P(x)$（依赖积） |
| $\exists x, P(x)$ | $\Sigma (x: A), P(x)$（依赖和） |
| $a = b$ | $Eq(a, b)$（恒等类型） |

**定义 2.5（策略模式与项模式）**
Lean4支持两种证明风格：
- **项模式**（term mode）：直接构造证明项，如 `fun h => h`
- **策略模式**（tactic mode）：通过交互式指令逐步构造，如 `by intro h; exact h`

---

## 3. 核心定理与证明

### 定理 3.1（自然数加法的交换律）

对任意 $n, m: \mathbb{N}$，$n + m = m + n$。

**证明（Lean4形式化）**：
```lean
theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
  | succ n ih =>
    rw [Nat.succ_add, Nat.add_succ, ih]
```

**数学解释**：
- **基例**（$n = 0$）：由 $0 + m = m$（`Nat.zero_add`）和 $m + 0 = m$（`Nat.add_zero`）
- **归纳步骤**：假设 $n + m = m + n$，证 $(n+1) + m = m + (n+1)$
  - $(n+1) + m = (n + m) + 1$（由 `Nat.succ_add`：$\text{succ}(n) + m = \text{succ}(n + m)$）
  - $m + (n+1) = (m + n) + 1$（由 `Nat.add_succ`）
  - 由归纳假设，等式成立

### 定理 3.2（恒等类型的单消去律）

对类型 $A$、谓词 $P: A \to \text{Prop}$，以及 $a, b: A$ 满足 $p: a = b$，有
$$\text{Eq.rec}(P(a), p): P(b)$$
即相等元素可互换所有谓词下的性质。

**证明**：恒等类型 $Eq: A \to A \to \text{Prop}$ 只有一个构造子 `refl : Eq a a`。归纳原理说明：为证 $\forall (a b: A)(p: a = b), Q(a, b, p)$，只需证 $Q(a, a, \text{refl}_a)$ 对所有 $a$。取 $Q(a, b, p) = P(a) \to P(b)$，则 $Q(a, a, \text{refl}_a) = P(a) \to P(a)$ 显然成立（恒等函数）。$\square$

---

## 4. 详细例子

### 例 4.1：基础语法与证明

```lean
-- 定义定理（项模式）
theorem hello : 1 + 1 = 2 := rfl

-- 使用策略模式
example (n : Nat) : n + 0 = n := by
  simp  -- 使用 simp-lemmas 自动简化

-- 蕴含证明
example (P Q : Prop) (h1 : P → Q) (hp : P) : Q := by
  exact h1 hp
```

### 例 4.2：Mathlib4的代数结构

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- 实数的基本性质
#check Real.exp_add  -- ∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y

-- 导数的链式法则
example (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g (f x)) :
    deriv (g ∘ f) x = deriv g (f x) * deriv f x := by
  rw [deriv.comp x hg hf]
```

### 例 4.3：结构归纳的完整模式

```lean
-- 列表长度的性质
inductive MyList (α : Type)
  | nil : MyList α
  | cons (hd : α) (tl : MyList α) : MyList α

open MyList

def length {α} : MyList α → Nat
  | nil => 0
  | cons _ tl => 1 + length tl

theorem length_append {α} (l1 l2 : MyList α) :
    length (append l1 l2) = length l1 + length l2 := by
  induction l1 with
  | nil => rfl
  | cons h t ih =>
    rw [append, length, length, ih]
    rw [Nat.succ_add]
```

---

## 5. Mathlib4生态系统

### 5.1 模块组织结构

| 领域 | 主要模块 | 说明 |
|------|----------|------|
| 代数 | `Mathlib.Algebra` | 群、环、域、模、李代数 |
| 线性代数 | `Mathlib.LinearAlgebra` | 向量空间、矩阵、张量积 |
| 拓扑 | `Mathlib.Topology` | 拓扑空间、连续映射、紧致性 |
| 分析 | `Mathlib.Analysis` | 微积分、测度论、泛函分析 |
| 数论 | `Mathlib.NumberTheory` | 素数、同余、Zeta函数 |
| 代数几何 | `Mathlib.AlgebraicGeometry` | 概形、层、态射 |

### 5.2 查找定理的方法

```lean
-- 使用 #check 查看定理类型
#check Nat.add_comm

-- 使用 #find 模式搜索
#find _ + _ = _ + _

-- 使用 loogle.lean-lang.org 在线搜索
```

---

## 6. 学习资源

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)

---

**适用**：docs/09-形式化证明/
