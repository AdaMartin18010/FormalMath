import Mathlib.Init.Core
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Sum.Basic

/-! 
# 类型论示例

对应的FormalMath文档：
- docs/07-逻辑学/01-命题逻辑-增强版.md
- docs/07-逻辑学/02-谓词逻辑.md
- docs/11-高级数学/15-同伦类型论.md

对应的Mathlib4模块：
- Mathlib.Init.Core
- Mathlib.Logic.Basic
- Mathlib.Data.Sigma.Basic
- Mathlib.Data.Sum.Basic

## 核心概念

Lean基于依赖类型论（Dependent Type Theory），是Martin-Löf类型论的变体。
-/ 

/-! 
## 基本类型

Lean中的基本类型构造。
-/

section BasicTypes

-- 函数类型
example (α β : Type) : Type _ := α → β

-- 积类型（笛卡尔积）
example (α β : Type) : Type _ := α × β

-- 积类型的构造
example (α β : Type) (a : α) (b : β) : α × β := (a, b)

-- 积类型的消去
example (α β : Type) (p : α × β) : α := p.1
example (α β : Type) (p : α × β) : β := p.2

-- 和类型（不交并）
example (α β : Type) : Type _ := α ⊕ β

-- 和类型的构造
example (α β : Type) (a : α) : α ⊕ β := Sum.inl a
example (α β : Type) (b : β) : α ⊕ β := Sum.inr b

-- 和类型的消去（模式匹配）
example (α β γ : Type) (f : α → γ) (g : β → γ) : α ⊕ β → γ := 
  fun x => match x with
    | Sum.inl a => f a
    | Sum.inr b => g b

-- 单位类型
example : Type _ := Unit
example : Unit := ()

-- 空类型
example : Type _ := Empty

-- 不存在空类型的元素
example : ¬Nonempty Empty := by
  intro h
  rcases h with ⟨e⟩
  exact Empty.elim e

end BasicTypes

/-! 
## 依赖类型

依赖类型是Lean的核心特性。
-/

section DependentTypes

-- 依赖函数类型（Π类型）
example (α : Type) (β : α → Type) : Type _ := (a : α) → β a

-- 使用示例：向量类型
example (n : ℕ) : Type _ := Fin n → ℝ

-- 依赖积类型（Σ类型）
example (α : Type) (β : α → Type) : Type _ := Σ a : α, β a

-- Σ类型的构造
example (α : Type) (β : α → Type) (a : α) (b : β a) : Σ a : α, β a := 
  ⟨a, b⟩

-- 使用示例：存在量词就是Σ类型的特殊情况
example (α : Type) (P : α → Prop) : Prop := ∃ a : α, P a

-- 证明存在量词
example : ∃ n : ℕ, n = 0 := ⟨0, rfl⟩

end DependentTypes

/-! 
## 命题即类型

Curry-Howard同构：命题与类型对应，证明与程序对应。
-/

section PropositionsAsTypes

-- 合取（∧）对应积类型
example (P Q : Prop) : Prop := P ∧ Q

-- ∧的构造
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := And.intro hp hq

-- ∧的消去
example (P Q : Prop) (hpq : P ∧ Q) : P := hpq.1
example (P Q : Prop) (hpq : P ∧ Q) : Q := hpq.2

-- 析取（∨）对应和类型
example (P Q : Prop) : Prop := P ∨ Q

-- ∨的构造
example (P Q : Prop) (hp : P) : P ∨ Q := Or.inl hp
example (P Q : Prop) (hq : Q) : P ∨ Q := Or.inr hq

-- 蕴含（→）对应函数类型
example (P Q : Prop) : Prop := P → Q

-- 假命题对应空类型
example : Prop := False

-- 从假命题推出任何命题（ex falso）
example (P : Prop) (h : False) : P := False.elim h

-- 真命题对应单位类型
example : Prop := True
example : True := trivial

-- 否定
example (P : Prop) : Prop := ¬P
example (P : Prop) : ¬P = (P → False) := by rfl

end PropositionsAsTypes

/-! 
## 全称和存在量词

量词的类型论解释。
-/

section Quantifiers

-- 全称量词（∀）对应依赖函数类型
example (α : Type) (P : α → Prop) : Prop := ∀ x : α, P x

-- ∀的构造
example (α : Type) (P : α → Prop) (h : ∀ x, P x) (a : α) : P a := h a

-- 存在量词（∃）对应依赖积类型
example (α : Type) (P : α → Prop) : Prop := ∃ x : α, P x

-- ∃的构造
example (α : Type) (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := 
  ⟨a, h⟩

-- ∃的消去
example (α : Type) (P Q : α → Prop) (h : ∃ x, P x) (f : ∀ x, P x → Q x) : 
    ∃ x, Q x := by
  rcases h with ⟨a, ha⟩
  use a
  apply f
  exact ha

end Quantifiers

/-! 
## 等式

等式的类型论定义。
-/

section Equality

-- 等式类型
example (α : Type) (a b : α) : Prop := a = b

-- 自反性
example (α : Type) (a : α) : a = a := Eq.refl a

-- 对称性
example (α : Type) (a b : α) (h : a = b) : b = a := Eq.symm h

-- 传递性
example (α : Type) (a b c : α) (h1 : a = b) (h2 : b = c) : a = c := 
  Eq.trans h1 h2

-- 替换原理（congr）
example (α β : Type) (f : α → β) (a b : α) (h : a = b) : f a = f b := 
  congr_arg f h

-- 等式的归纳原理（核心！）
example (α : Type) (a : α) (P : α → Prop) (h : P a) (b : α) (hab : a = b) : 
    P b := Eq.subst hab h

-- 使用rewrite的等式证明
example (α : Type) (a b c : α) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

end Equality

/-! 
## 归纳类型

用户自定义归纳类型。
-/

section InductiveTypes

-- 自然数（已定义）
#check ℕ

-- 自然数的归纳原理
example (P : ℕ → Prop) (h0 : P 0) (h1 : ∀ n, P n → P (n + 1)) (n : ℕ) : 
    P n := Nat.rec h0 h1 n

-- 列表类型
inductive MyList (α : Type)
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α

-- 列表的构造
example : MyList ℕ := MyList.nil
example : MyList ℕ := MyList.cons 1 (MyList.cons 2 MyList.nil)

-- 列表的递归函数
def MyList.length {α : Type} : MyList α → ℕ
  | nil => 0
  | cons _ t => 1 + length t

-- 列表长度的性质
example {α : Type} (l : MyList α) : l.length ≥ 0 := by
  cases l <;> simp [MyList.length]
  <;> linarith

-- 二叉树类型
inductive BinTree (α : Type)
  | empty : BinTree α
  | node (left : BinTree α) (value : α) (right : BinTree α) : BinTree α

-- 树的高度
def BinTree.height {α : Type} : BinTree α → ℕ
  | empty => 0
  | node l _ r => 1 + max l.height r.height

end InductiveTypes

/-! 
## 结构体

结构体是单构造子的归纳类型。
-/

section Structures

-- 半群结构
structure Semigroup (α : Type) where
  mul : α → α → α
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

-- 幺半群结构
structure Monoid (α : Type) extends Semigroup α where
  one : α
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

-- 群结构
structure Group (α : Type) extends Monoid α where
  inv : α → α
  mul_left_inv : ∀ a, mul (inv a) a = one

-- 构造群结构实例
example : Group ℤ where
  mul := (· + ·)
  mul_assoc _ _ _ := Int.add_assoc _ _ _
  one := 0
  one_mul _ := Int.zero_add _
  mul_one _ := Int.add_zero _
  inv a := -a
  mul_left_inv _ := Int.neg_add_cancel _

end Structures

/-! 
## 同伦类型论基础

HoTT在Lean中的表示。
-/

section HomotopyTypeTheory

-- 同伦（路径）
example (α : Type) (a b : α) : Type _ := a = b

-- 路径连接（trans）
example (α : Type) (a b c : α) (p : a = b) (q : b = c) : a = c := 
  Eq.trans p q

-- 路径逆（symm）
example (α : Type) (a b : α) (p : a = b) : b = a := Eq.symm p

-- UIP（唯一性证明）在Lean中成立
example (α : Type) (a b : α) (p q : a = b) : p = q := by
  rfl

-- 异质等式
example (α β : Type) (h : α = β) (a : α) : β := h ▸ a

end HomotopyTypeTheory

/-! 
## 宇宙层次

类型的类型。
-/

section Universes

-- Type 0（简写为Type）
example : Type 1 := Type

-- Type 1包含Type 0
example : Type 1 := Type 0

-- 依此类推
example : Type 2 := Type 1

-- 多态宇宙
example (α : Type u) : Type u := α

-- Prop是特殊的宇宙
example : Type := Prop

-- 大宇宙的消除到小宇宙
example (α : Type u) (β : Type v) : Type (max u v) := α → β

end Universes

/-! 
## 示例：类型论证明

展示类型论风格的证明。
-/

section TypeTheoryProofs

-- 使用模式匹配定义逻辑连接词
inductive MyAnd (P Q : Prop) : Prop
  | intro (left : P) (right : Q) : MyAnd P Q

inductive MyOr (P Q : Prop) : Prop
  | inl (p : P) : MyOr P Q
  | inr (q : Q) : MyOr P Q

-- 证明交换律
def and_comm {P Q : Prop} : MyAnd P Q → MyAnd Q P
  | MyAnd.intro p q => MyAnd.intro q p

def or_comm {P Q : Prop} : MyOr P Q → MyOr Q P
  | MyOr.inl p => MyOr.inr p
  | MyOr.inr q => MyOr.inl q

-- 证明分配律
def and_distrib {P Q R : Prop} : 
    MyAnd P (MyOr Q R) → MyOr (MyAnd P Q) (MyAnd P R)
  | MyAnd.intro p (MyOr.inl q) => MyOr.inl (MyAnd.intro p q)
  | MyAnd.intro p (MyOr.inr r) => MyOr.inr (MyAnd.intro p r)

-- 使用函数组合证明蕴含的传递性
def imp_trans {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := 
  fun f g => g ∘ f

end TypeTheoryProofs

/-! 
## 练习

1. 定义一个类型`Vec α n`，表示长度为n的向量。

2. 证明：对于任意类型α，α × Unit ≅ α（同构）。

3. 定义半环（semiring）结构，包含加法幺半群和乘法幺半群。

4. 证明：对于任意命题P,Q,R，有 (P ∧ Q) → R 当且仅当 P → (Q → R)。

5. 定义自然数的加法，并证明加法的结合律。

-/ 

section Exercises

-- 练习1的提示
inductive Vec (α : Type) : ℕ → Type
  | nil : Vec α 0
  | cons {n : ℕ} (head : α) (tail : Vec α n) : Vec α (n + 1)

-- 练习2的框架
def prod_unit_iso {α : Type} : α × Unit → α := 
  fun p => p.1

def prod_unit_iso_inv {α : Type} : α → α × Unit := 
  fun a => (a, ())

-- 练习3的框架
structure Semiring (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  -- 添加所需的公理...

end Exercises
