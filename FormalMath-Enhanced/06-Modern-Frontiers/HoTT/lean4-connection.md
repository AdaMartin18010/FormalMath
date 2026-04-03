---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 同伦类型论与Lean4的联系

> HoTT核心概念在Lean4中的表达、单值公理的实现以及高阶归纳类型的例子

---

## 1. HoTT与Lean4的关系概述

### 1.1 历史背景

**Lean4的设计哲学**:

Lean4由Leonardo de Moura在Microsoft Research开发，其设计深受HoTT影响：

1. **依赖类型**: 核心类型系统基于Martin-Löf类型论
2. **归纳类型**: 支持高阶归纳类型的某些形式
3. **商类型**: 通过类型类机制实现类似商类型的构造
4. **证明相关vs证明无关**: 灵活处理两者

**重要区别**:

| 特性 | HoTT (Cubical Agda) | Lean4 |
|-----|---------------------|-------|
| 基础 | 单值基础 | 经典逻辑 + 选择公理 |
| 等式 | 路径类型 | 归纳等式 |
| 同伦计算 | 原生支持 | 通过经典同伦论 |
| 单值公理 | 可计算 | 不可计算（作为公理） |
| 证明提取 | 构造性 | 经典 |

### 1.2 Lean4中的HoTT思想

**核心联系**:

```lean
-- Lean4中的等式是归纳定义的
inductive Eq {α : Type u} (a : α) : α → Prop where
  | refl : Eq a a

-- 这对应于HoTT中的路径归纳
-- Eq.rec 对应于 path induction
```

**类型作为空间的观点**:

在Lean4中，虽然等式是命题（Prop），但可以通过其他方式获得同伦论的结构：

```lean
-- 使用同构而非相等来表示等价
structure Iso (A B : Type u) where
  toFun : A → B
  invFun : B → A
  left_inv : invFun ∘ toFun = id
  right_inv : toFun ∘ invFun = id
```

---

## 2. 单值公理在Lean4中的实现

### 2.1 单值公理的陈述

**HoTT中的单值公理**:

$$(A =_\mathcal{U} B) \simeq (A \simeq B)$$

即：类型的相等等价于它们之间的等价。

**Lean4中的近似实现**:

```lean
-- 使用类型类实现"等价即相等"的效果
class Univalence (A B : Type u) where
  eqEquivIso : (A = B) ≃ (A ≃ B)

-- 注意：Lean中的 = 是命题等式，不是路径类型
-- 这需要 careful 处理
```

### 2.2 结构继承模式

Lean4通过**结构继承**实现单值公理的效果：

```lean
-- 定义带结构的对象
structure Monoid where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x

-- 同构的Monoid可以视为"相等"
structure MonoidIso (M N : Monoid) where
  toFun : M.carrier → N.carrier
  invFun : N.carrier → M.carrier
  -- ... 保持运算的条件

-- 使用类型类传递结构
instance (M N : Monoid) [MonoidIso M N] : Coe M.carrier N.carrier where
  coe := MonoidIso.toFun
```

### 2.3 具体实现示例

**例：同构类型的结构转移**:

```lean
-- 如果两个类型同构，一个上的结构可以转移到另一个
structure Transportable (F : Type u → Type v) where
  transport {A B : Type u} : A ≃ B → F A → F B
  -- 保持恒等和复合的条件

-- Monoid结构是可转移的
instance : Transportable Monoid where
  transport {A B} e M := {
    carrier := B,
    mul := λ b₁ b₂ => e.toFun (M.mul (e.invFun b₁) (e.invFun b₂)),
    one := e.toFun M.one,
    -- 证明公理保持
    mul_assoc := by ...,
    one_mul := by ...,
    mul_one := by ...
  }
```

### 2.4 与Mathlib4的整合

**Mathlib4中的同构处理**:

```lean
-- Mathlib4广泛使用同构
import Mathlib

-- 同构的定义
#check CategoryTheory.Iso

-- 同构诱导的等价
example (C : Type*) [Category C] (X Y : C) (i : X ≅ Y) : X ≃ Y := ...

-- 结构自动转移
def transportRing {A B : Type*} (e : A ≃ B) [Ring A] : Ring B := ...
```

---

## 3. 高阶归纳类型 (HITs) 在Lean4中的例子

### 3.1 高阶归纳类型回顾

**HIT的一般形式**:

```
HIT T :=
| point_constructors : ...
| path_constructors : ...
| higher_path_constructors : ...
```

**Lean4的限制**:

Lean4的归纳类型不支持路径构造子作为原始概念，但可以通过**商类型**和**束类型**模拟某些HIT。

### 3.2 圆 $S^1$ 的模拟

**HoTT定义**:

```
HIT S¹ :=
| base : S¹
| loop : base = base
```

**Lean4模拟** (使用抽象代数):

```lean
-- 使用自由群模拟圆的基本群
inductive S1Point
  | base

def S1Loop : Type := FreeGroup Unit  -- 对应于 ℤ

-- 圆的覆盖空间结构
def helix : S1Point → Type
  | S1Point.base := ℤ

-- 绕数函数
def windingNumber (p : S1Loop) : ℤ :=
  FreeGroup.lift (λ _ => 1) p
```

**更精确的实现** (使用Mathlib的同伦论):

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid

-- 使用拓扑空间的奇异复形
abbrev S1 := UnitInterval ⧸ (0 ∼ 1)

-- 基本群
example : FundamentalGroup S1 (Quotient.mk _ 0) ≃* Multiplicative ℤ := ...
```

### 3.3 区间 $I$ 的模拟

**HoTT定义**:

```
HIT I :=
| 0_I : I
| 1_I : I
| seg : 0_I = 1_I
```

**Lean4实现** (使用有序类型):

```lean
-- 使用单位区间
def UnitInterval := Set.Icc (0 : ℝ) 1

-- 端点
abbrev I0 : UnitInterval := ⟨0, by norm_num⟩
abbrev I1 : UnitInterval := ⟨1, by norm_num⟩

-- 路径存在性由连通性保证
example : I0 ≠ I1 := by norm_num

-- 使用路径类型（Mathlib）
open Topology
example : Path I0 I1 := {
  toFun := λ t => ⟨t, by ...⟩,
  continuous_toFun := by ...,
  source' := by ...,
  target' := by ...
}
```

### 3.4 商类型的实现

**HoTT中的商**:

```
HIT A/R :=
| [·] : A → A/R
| eq : ∀ x y, R(x,y) → [x] = [y]
| set : isSet(A/R)
```

**Lean4的商类型**:

```lean
-- Lean4有内建的商类型
axiom Quotient {α : Sort u} (s : Setoid α) : Sort u

axiom Quotient.mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s

axiom Quotient.sound {α : Sort u} {s : Setoid α} {a b : α} :
  a ≈ b → Quotient.mk s a = Quotient.mk s b

-- 使用示例
def Integers := Quotient ⟨ℕ × ℕ, intSetoid⟩

-- 证明商类型的泛性质
def Quotient.lift {α : Sort u} {s : Setoid α} {β : Sort v}
  (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) : Quotient s → β := ...
```

### 3.5 截断类型

**HoTT定义** (命题截断):

```
HIT ∥A∥₋₁ :=
| tr : A → ∥A∥₋₁
| path : ∀ x y : ∥A∥₋₁, x = y
```

**Lean4实现** (使用Subsingleton):

```lean
-- 命题截断对应于存在量词
def TruncatedExists {α : Type u} (P : α → Prop) : Prop :=
  ∃ a, P a

-- 或者使用Classical逻辑
open Classical
noncomputable def propositionalTruncation (A : Type u) : Prop :=
  if Nonempty A then True else False

-- 注意：Lean的Prop自动是proposition（最多一个证明）
example (P : Prop) (p q : P) : p = q := proofIrrel p q
```

---

## 4. 与集合论的比较

### 4.1 基础差异

**ZFC集合论 vs HoTT vs Lean4**:

| 特性 | ZFC | HoTT | Lean4 |
|-----|-----|------|-------|
| 元素与集合 | $a \in A$ | $a : A$ | `a : A` |
| 等式 | 本原概念 | 路径类型 | 归纳Prop |
| 商构造 | 等价类 | HIT | 类型类 |
| 选择公理 | 独立公理 | 有计算内容 | 作为公理 |
| 排中律 | 公理 | 选择性假设 | 选择性假设 |
| 构造性 | 否 | 是 | 可选 |

### 4.2 数学实践中的差异

**例：商群**:

```lean
-- 在ZFC风格的形式化中 (如Metamath)
-- 商群定义为陪集的集合

-- 在HoTT风格中 (如Cubical Agda)
-- 使用HIT定义商

-- 在Lean4中
def QuotientGroup (G : Type*) [Group G] (N : Subgroup G) [N.Normal] : Type* :=
  Quotient N.quotientSetoid

instance : Group (QuotientGroup G N) where
  mul := Quotient.lift₂ (λ a b => ⟦a * b⟧) (by ...)
  -- ...
```

**例：实数构造**:

```lean
-- ZFC: 使用Dedekind分割或Cauchy序列的等价类
-- HoTT: 同样方法，但商使用HIT
-- Lean4: 使用Cauchy序列的商

def Real := Quotient (CauchySeq.setoid ℚ)

-- 或者使用Mathlib的定义
#check Mathlib.Data.Real.Basic
```

### 4.3 优势与局限

**HoTT的优势** (在Lean4中的近似):

1. **同构传递**: 通过类型类机制近似实现

   ```lean
   -- 自动的同构传递
   example (G H : Group) [GroupIso G H] : G.carrier ≃ H.carrier := ...
   ```

2. **商构造的自然性**:

   ```lean
   -- 商映射自动是满射
   example {α : Type*} (s : Setoid α) : Function.Surjective (Quotient.mk s) := ...
   ```

3. **高阶结构**: 通过同伦论库实现

   ```lean
   -- 使用Mathlib的代数拓扑
   import Mathlib.AlgebraicTopology.HomotopyGroup
   ```

**Lean4的优势**:

1. **经典数学的便利性**:

   ```lean
   -- 直接使用排中律
   example (P : Prop) : P ∨ ¬P := Classical.em P
   ```

2. **计算效率**:

   ```lean
   -- 高效的编译和计算
   #eval fibonacci 100  -- 快速计算
   ```

3. **庞大的数学库**:
   - Mathlib4是目前最大的形式化数学库

---

## 5. 在Lean4中实现HoTT构造

### 5.1 类型即空间的观点

```lean
-- 使用Mathlib的同伦论实现
def TypeAsSpace (A : Type u) : TopCat :=
  TopCat.of A  -- 赋予离散拓扑

-- 路径类型对应于连续映射
example {A : TopCat} (x y : A) : Path x y ≃ (unitInterval → A) := ...
```

### 5.2 综合同伦论

```lean
-- 证明拓扑空间的同伦不变量
import Mathlib.AlgebraicTopology.FundamentalGroupoid

-- 圆周的基本群是ℤ
theorem pi1_circle : FundamentalGroup S1 base ≅ ℤ := ...

-- 球面的同伦群
theorem pi_n_sphere (n : ℕ) : π_ n (sphere n) ≅ ℤ := ...
```

### 5.3 构造性数学

```lean
-- 选择构造性模式
namespace Constructive

-- 不使用经典公理
-- 不使用选择公理
-- 所有证明都有计算内容

def constructiveReal := CauchySeq ℚ /-(无选择公理)-/

end Constructive
```

---

## 6. 学习路径与资源

### 6.1 Lean4学习资源

**官方资源**:

- **Theorem Proving in Lean4**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Functional Programming in Lean**: https://lean-lang.org/functional_programming_in_lean/
- **Mathlib4文档**: https://leanprover-community.github.io/mathlib4_docs/

**HoTT相关**:

- **HoTT Book**: https://homotopytypetheory.org/book/
- **Cubical Agda文档**: https://agda.readthedocs.io/en/latest/language/cubical.html

### 6.2 从HoTT到Lean4的转换指南

| HoTT概念 | Lean4对应 | 注意事项 |
|---------|----------|---------|
| $A =_\mathcal{U} B$ | `A = B` | 在Prop中，不是Type |
| $A \simeq B$ | `A ≃ B` | 显式等价 |
| 单值公理 | 结构继承 | 近似实现 |
| HIT | 归纳类型 + 商 | 部分支持 |
| 截断 | 类型类 | 灵活处理 |
| 路径类型 | `Path` | 在Mathlib中 |

### 6.3 实践建议

1. **理解差异**: 认识到Lean4和HoTT在基础上的不同
2. **利用Mathlib**: 使用成熟的代数拓扑库
3. **类型类技巧**: 学习使用类型类实现结构转移
4. **证明模式**: 掌握Lean4的tactic系统

---

## 7. 未来展望

### 7.1 可能的发展方向

1. **更强的HIT支持**:
   - Lean4未来版本可能增强对HIT的支持
   - 通过元编程实现某些HIT构造

2. **计算单值基础**:
   - 发展可计算的单值公理近似
   - 与Cubical类型的整合

3. **形式化项目**:
   - HoTT Book中的定理的形式化
   - 综合同伦论的发展

### 7.2 研究机会

| 领域 | 问题 | 难度 |
|-----|------|------|
| 类型理论 | 在Lean4中实现更多HIT | 高 |
| 同伦论 | 形式化综合同伦论结果 | 高 |
| 范畴论 | ∞-范畴与HoTT的联系 | 中 |
| 代数拓扑 | 计算同伦论的形式化 | 中 |

---

*最后更新: 2026年4月 | FormalMath项目*
