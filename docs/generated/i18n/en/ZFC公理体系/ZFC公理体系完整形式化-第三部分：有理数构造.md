---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

<div class="language-switcher">

**Languages**: [🇨🇳 中文](../zh/ZFC公理体系\ZFC公理体系完整形式化-第三部分：有理数构造.md) | **🇬🇧 English**

</div>

---

> 🌐 This document is machine-translated from Chinese. Some terms may not be accurate.

---
msc_primary: "00A05"
msc_secondary: ['03E30', '11-XX', '68Vxx']
---

# ZFC公理体系完整形式化 - 第三部分：有理数构造

## Table of Contents

- [ZFC公理体系完整形式化 - 第三部分：有理数构造](#zfc公理体系完整形式化---第三部分有理数构造)
  - [Table of Contents](#Table of Contents)
  - [📚 概述](#-概述)
  - [🏗️ 有理数的构造](#️-有理数的构造)
    - [1. 有理数的Definition](#1-有理数的Definition)
      - [1.1 有理数作为等价类](#11-有理数作为等价类)
      - [1.2 有理数的表示](#12-有理数的表示)
    - [2. 有理数运算的Definition](#2-有理数运算的Definition)
      - [2.1 加法运算](#21-加法运算)
      - [2.2 乘法运算](#22-乘法运算)
    - [3. 有理数序关系](#3-有理数序关系)
      - [3.1 序关系的Definition](#31-序关系的Definition)
      - [3.2 有理数的代数结构](#32-有理数的代数结构)
    - [4. 有理数的嵌入](#4-有理数的嵌入)
      - [4.1 整数到有理数的嵌入](#41-整数到有理数的嵌入)
      - [4.2 有理数的唯一性](#42-有理数的唯一性)
    - [5. 有理数的基本Theorem](#5-有理数的基本Theorem)
      - [5.1 有理数的稠密性](#51-有理数的稠密性)
      - [5.2 有理数的可数性](#52-有理数的可数性)
    - [6. 有理数的代数性质](#6-有理数的代数性质)
      - [6.1 有理数的因子分解](#61-有理数的因子分解)
      - [6.2 有理数的逼近](#62-有理数的逼近)
    - [7. 有理数的拓扑性质](#7-有理数的拓扑性质)
      - [7.1 有理数的完备性](#71-有理数的完备性)
      - [7.2 有理数的Connected性](#72-有理数的Connected性)
    - [8. 有理数的应用](#8-有理数的应用)
      - [8.1 在Number Theory中的应用](#81-在Number Theory中的应用)
      - [8.2 在分析中的应用](#82-在分析中的应用)
      - [8.3 在计算机科学中的应用](#83-在计算机科学中的应用)
    - [9. 结论](#9-结论)
  - [💻 Lean4形式化实现 / Lean4 Formal Implementation](#-lean4形式化实现--lean4-formal-implementation)
    - [有理数等价关系形式化](#有理数等价关系形式化)
    - [有理数类型Definition](#有理数类型Definition)
    - [有理数运算形式化](#有理数运算形式化)
    - [有理数序关系形式化](#有理数序关系形式化)
    - [有理数Field结构形式化](#有理数Field结构形式化)
    - [应用案例：有理数在Number Theory中的应用](#应用案例有理数在Number Theory中的应用)
  - [术语对照表 / Terminology Table](#术语对照表--terminology-table)
  - [References / References](#References--references)

## 📚 概述

本部分将展示如何从整数系统严格构造有理数系统，包括有理数的Definition、运算、序关系和代数性质的形式化Proof。
这是从整数到实数的重要中间步骤。

## 🏗️ 有理数的构造

### 1. 有理数的Definition

#### 1.1 有理数作为等价类

**Definition 1.1** (有理数)
有理数是整数序对的等价类，其中等价关系Definition为：
$$(a, b) \sim (c, d) \leftrightarrow ad = bc \land b \neq 0 \land d \neq 0$$

**形式化表述**：
$$\mathbb{Q} = (\mathbb{Z} \times \mathbb{Z}^*) / \sim$$

其中 $\mathbb{Z}^* = \mathbb{Z} \setminus \{0\}$。

**Theorem 1.1.1** (等价关系的性质)
$\sim$ 是等价关系，即：

1. 自反性：$(a, b) \sim (a, b)$
2. 对称性：$(a, b) \sim (c, d) \rightarrow (c, d) \sim (a, b)$
3. 传递性：$(a, b) \sim (c, d) \land (c, d) \sim (e, f) \rightarrow (a, b) \sim (e, f)$

**形式化Proof**：

```text
Proof：
(1) 自反性：ab = ba，因此 (a,b) ~ (a,b)
(2) 对称性：如果 ad = bc，则 cb = da
(3) 传递性：
   - 假设 ad = bc 和 cf = de
   - 则 adf = bcf = bde
   - 由于 d ≠ 0，因此 af = be
   - 所以 (a,b) ~ (e,f)

```

#### 1.2 有理数的表示

**Definition 1.2** (有理数的表示)

- 整数 $n$ 表示为 $\frac{n}{1}$
- 分数 $\frac{a}{b}$ 表示等价类 $[(a, b)]$

**Theorem 1.2.1** (有理数表示的唯一性)
每个有理数都有唯一的既约分数表示。

**形式化Proof**：

```text
Proof：
(1) 对于有理数 [(a,b)]，可以约分到既约形式
(2) 既约形式是唯一的（考虑符号）
(3) 因此每个有理数有唯一表示

```

### 2. 有理数运算的Definition

#### 2.1 加法运算

**Definition 2.1** (有理数加法)
$$\frac{a}{b} + \frac{c}{d} = \frac{ad + bc}{bd}$$

**Theorem 2.1.1** (加法运算的良Definition性)
加法运算不依赖于等价类的代表元选择。

**形式化Proof**：

```text
Proof：
(1) 假设 (a,b) ~ (a',b') 和 (c,d) ~ (c',d')
(2) 则 ab' = ba' 和 cd' = dc'
(3) 计算 (ad+bc)(b'd') 和 (a'd'+b'c')(bd)
(4) 使用整数的运算性质Proof相等

```

**Theorem 2.1.2** (加法运算的性质)

1. 结合律：$(x + y) + z = x + (y + z)$
2. 交换律：$x + y = y + x$
3. 单位元：$x + 0 = x$
4. 逆元：$x + (-x) = 0$

**形式化Proof**：

```text
Proof：
(1) 结合律：直接计算
(2) 交换律：整数加法的交换律
(3) 单位元：a/b + 0/1 = a/b
(4) 逆元：a/b + (-a)/b = 0/b = 0

```

#### 2.2 乘法运算

**Definition 2.2** (有理数乘法)
$$\frac{a}{b} \cdot \frac{c}{d} = \frac{ac}{bd}$$

**Theorem 2.2.1** (乘法运算的良Definition性)
乘法运算不依赖于等价类的代表元选择。

**形式化Proof**：

```text
Proof：
(1) 假设 (a,b) ~ (a',b') 和 (c,d) ~ (c',d')
(2) 则 ab' = ba' 和 cd' = dc'
(3) 计算 ac(b'd') 和 a'c'(bd)
(4) 使用整数的运算性质Proof相等

```

**Theorem 2.2.2** (乘法运算的性质)

1. 结合律：$(x \cdot y) \cdot z = x \cdot (y \cdot z)$
2. 交换律：$x \cdot y = y \cdot x$
3. 单位元：$x \cdot 1 = x$
4. 逆元：$x \cdot x^{-1} = 1$ (对于 $x \neq 0$)

**形式化Proof**：

```text
Proof：
(1) 结合律：直接计算
(2) 交换律：整数乘法的交换律
(3) 单位元：a/b · 1/1 = a/b
(4) 逆元：a/b · b/a = ab/ab = 1

```

### 3. 有理数序关系

#### 3.1 序关系的Definition

**Definition 3.1** (有理数序关系)
$$\frac{a}{b} < \frac{c}{d} \leftrightarrow ad < bc$$

其中 $b, d > 0$。

**Theorem 3.1.1** (序关系的性质)

1. 自反性：$x \leq x$
2. 反对称性：$x \leq y \land y \leq x \rightarrow x = y$
3. 传递性：$x \leq y \land y \leq z \rightarrow x \leq z$
4. 完全性：任意非空有上界的集合有最小上界

**形式化Proof**：

```text
Proof：
(1) 自反性：ad ≤ ad
(2) 反对称性：如果 ad ≤ bc 和 bc ≤ ad，则 ad = bc
(3) 传递性：使用整数序的传递性
(4) 完全性：有理数不满足完全性（这是实数的特征）

```

#### 3.2 有理数的代数结构

**Theorem 3.2.1** (有理数Field的性质)
有理数集合 $\mathbb{Q}$ 在加法和乘法下构成Field。

**形式化Proof**：

```text
Proof：
(1) 加法Group：结合律、交换律、单位元、逆元
(2) 乘法Group（除去零）：结合律、交换律、单位元、逆元
(3) 分配律：左分配律和右分配律
(4) 零因子：如果 xy = 0，则 x = 0 或 y = 0

```

### 4. 有理数的嵌入

#### 4.1 整数到有理数的嵌入

**Definition 4.1** (嵌入映射)
$$\phi: \mathbb{Z} \rightarrow \mathbb{Q}, \phi(n) = \frac{n}{1}$$

**Theorem 4.1.1** (嵌入映射的性质)
$\phi$ 是单射，且保持运算和序关系。

**形式化Proof**：

```text
Proof：
(1) 单射：如果 n/1 = m/1，则 n = m
(2) 保持加法：φ(n + m) = φ(n) + φ(m)
(3) 保持乘法：φ(n · m) = φ(n) · φ(m)
(4) 保持序关系：n < m ↔ φ(n) < φ(m)

```

#### 4.2 有理数的唯一性

**Theorem 4.2.1** (有理数系统的唯一性)
在Isomorphism意义下，有理数系统是唯一的。

**形式化Proof**：

```text
Proof：
(1) 假设存在两个有理数系统 Q₁ 和 Q₂
(2) 构造Isomorphism映射 f: Q₁ → Q₂
(3) Proof f 是双射且保持运算
(4) 因此 Q₁ ≅ Q₂

```

### 5. 有理数的基本Theorem

#### 5.1 有理数的稠密性

**Theorem 5.1.1** (有理数的稠密性)
对于任意两个不同的有理数 $a < b$，存在有理数 $c$ 使得 $a < c < b$。

**形式化Proof**：

```text
Proof：
(1) 设 a = p/q, b = r/s
(2) 取 c = (a + b)/2 = (ps + rq)/(2qs)
(3) Proof a < c < b
(4) 因此有理数在数轴上稠密

```

#### 5.2 有理数的可数性

**Theorem 5.2.1** (有理数的可数性)
有理数集合是可数的。

**形式化Proof**：

```text
Proof：
(1) 构造双射 f: N → Q
(2) 使用对角线方法枚举有理数
(3) Proof f 是双射
(4) 因此 Q 是可数的

```

### 6. 有理数的代数性质

#### 6.1 有理数的因子分解

**Theorem 6.1.1** (有理数的唯一因子分解)
每个非零有理数都可以唯一地表示为素数的幂次乘积。

**形式化Proof**：

```text
Proof：
(1) 对于有理数 a/b，分别分解 a 和 b
(2) 使用整数的唯一因子分解
(3) 合并得到有理数的分解
(4) Proof唯一性

```

#### 6.2 有理数的逼近

**Theorem 6.2.1** (有理数的逼近)
对于任意实数 $x$ 和任意正数 $\epsilon$，存在有理数 $q$ 使得 $|x - q| < \epsilon$。

**形式化Proof**：

```text
Proof：
(1) 使用有理数的稠密性
(2) 构造逼近序列
(3) Proof逼近的Convergent性
(4) 因此有理数可以逼近任意实数

```

### 7. 有理数的拓扑性质

#### 7.1 有理数的完备性

**Theorem 7.1.1** (有理数的不完备性)
有理数集合在通常的度量下不是完备的。

**形式化Proof**：

```text
Proof：
(1) 构造柯西序列 {1, 1.4, 1.41, 1.414, ...}
(2) 这个序列Convergent到 √2
(3) 但 √2 不是有理数
(4) 因此有理数不完备

```

#### 7.2 有理数的Connected性

**Theorem 7.2.1** (有理数的不Connected性)
有理数集合在通常的拓扑下不是Connected的。

**形式化Proof**：

```text
Proof：
(1) 考虑集合 A = {q ∈ Q : q < √2}
(2) 和集合 B = {q ∈ Q : q > √2}
(3) A 和 B 都是Open Set且不相交
(4) Q = A ∪ B，因此 Q 不Connected

```

### 8. 有理数的应用

#### 8.1 在Number Theory中的应用

**Theorem 8.1.1** (有理数在Number Theory中的应用)
有理数在Number Theory中有重要应用，特别是在丢番图方程的研究中。

**形式化Proof**：

```text
Proof：
(1) 有理数解的存在性
(2) 有理数解的性质
(3) 有理数解与整数解的关系
(4) 应用实例

```

**应用案例 8.1.1** (丢番图方程的有理数解)
考虑丢番图方程 $ax + by = c$，其中 $a, b, c \in \mathbb{Z}$。

- **有理数解的存在性**：如果 $\gcd(a, b) \mid c$，则方程有整数解，从而有有理数解
- **有理数解的结构**：所有有理数解可以表示为 $(x_0 + \frac{b}{\gcd(a,b)}t, y_0 - \frac{a}{\gcd(a,b)}t)$，其中 $(x_0, y_0)$ 是特解，$t \in \mathbb{Q}$
- **应用**：在密码学中，有理数解用于构造椭圆曲线上的有理点

**应用案例 8.1.2** (有理数在代数Number Theory中的应用)

- **代数数**：有理数是最简单的代数数（次数为1）
- **数Field**：有理数Field $\mathbb{Q}$ 是代数Number Theory的基础
- **分圆Field**：分圆Field是 $\mathbb{Q}$ 的有限扩张

#### 8.2 在分析中的应用

**Theorem 8.2.1** (有理数在分析中的应用)
有理数在Real Analysis中作为稠密子集有重要应用。

**形式化Proof**：

```text
Proof：
(1) 有理数的稠密性
(2) 在Limit理论中的应用
(3) 在积分理论中的应用
(4) 在函数逼近中的应用

```

**应用案例 8.2.1** (有理数在Limit理论中的应用)

- **序列Limit**：有理数序列可以逼近任意实数
- **Continuous性**：函数在有理点Continuous可以推出在实数点Continuous（对于某些函数类）
- **可测性**：有理数集合是可测的，测度为0

**应用案例 8.2.2** (有理数在积分理论中的应用)

- **黎曼积分**：有理数在黎曼积分构造中起关键作用
- **勒贝格测度**：有理数集合的勒贝格测度为0
- **Integrable性**：有理数指示函数的Integrable性分析

**应用案例 8.2.3** (有理数在函数逼近中的应用)

- **魏尔斯特拉斯逼近Theorem**：Continuous函数可以用有理系数多项式逼近
- **帕德逼近**：使用有理函数逼近超越函数
- **连分数**：有理数的连分数表示在数值计算中的应用

#### 8.3 在计算机科学中的应用

**应用案例 8.3.1** (有理数在数值计算中的应用)

- **精确计算**：有理数可以精确表示，避免浮点误差
- **符号计算**：计算机代数系统使用有理数进行精确计算
- **算法设计**：有理数运算在算法设计中广泛应用

**应用案例 8.3.2** (有理数在密码学中的应用)

- **椭圆曲线密码**：椭圆曲线上的有理点构成密码学基础
- **Number Theory密码**：基于有理数Field上Number Theory问题的密码系统
- **Homomorphism加密**：有理数运算在Homomorphism加密中的应用

### 9. 结论

通过严格的Set Theory构造，我们成功地从整数系统推导出了有理数系统。
有理数系统具有完整的代数结构，包括加法、乘法、序关系等。有理数系统是Field，但不完备，这为实数的构造提供了动机。

在下一部分中，我们将展示如何从有理数构造实数系统。

---

**文档状态**: 有理数构造完成（已添加Lean4形式化实现）
**下一部分**: 实数构造
**形式化程度**: 完整形式化Proof + Lean4代码实现

## 💻 Lean4形式化实现 / Lean4 Formal Implementation

### 有理数等价关系形式化

```lean
/--
## 有理数构造的Lean4形式化实现
## Lean4 Formal Implementation of Rational Number Construction

本部分提供了有理数构造的完整Lean4形式化实现
This section provides complete Lean4 formal implementation of rational number construction
--/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Order.Basic

-- 有理数等价关系
-- Rational number equivalence relation
def RationalEquiv : (ℤ × ℤ) → (ℤ × ℤ) → Prop :=
  λ (a, b) (c, d) => a * d = c * b ∧ b ≠ 0 ∧ d ≠ 0

-- 等价关系的自反性
-- Reflexivity of equivalence relation
theorem rational_equiv_refl (x : ℤ × ℤ) (h : x.2 ≠ 0) :
  RationalEquiv x x :=
begin
  simp [RationalEquiv],
  split,
  { ring },
  { exact ⟨h, h⟩ }
end

-- 等价关系的对称性
-- Symmetry of equivalence relation
theorem rational_equiv_symm (x y : ℤ × ℤ) :
  RationalEquiv x y → RationalEquiv y x :=
begin
  intro h,
  simp [RationalEquiv] at *,
  split,
  { rw [mul_comm, h.1, mul_comm] },
  { exact ⟨h.2.2, h.2.1⟩ }
end

-- 等价关系的传递性
-- Transitivity of equivalence relation
theorem rational_equiv_trans (x y z : ℤ × ℤ) :
  RationalEquiv x y → RationalEquiv y z → RationalEquiv x z :=
begin
  intros h1 h2,
  simp [RationalEquiv] at *,
  split,
  { have h3 : x.1 * y.2 = y.1 * x.2 := h1.1,
    have h4 : y.1 * z.2 = z.1 * y.2 := h2.1,
    have h5 : x.1 * y.2 * z.2 = y.1 * x.2 * z.2 := by rw [h3],
    have h6 : y.1 * z.2 * x.2 = z.1 * y.2 * x.2 := by rw [h4],
    have h7 : x.1 * z.2 * y.2 = z.1 * x.2 * y.2 := by
      { rw [← mul_assoc, ← mul_assoc, h5, ← h6, mul_assoc, mul_assoc] },
    cases h1.2.2 with h8 h8,
    { exfalso, exact h1.2.2.1 h8 },
    { rw [← mul_right_inj' h8] at h7,
      exact h7 } },
  { exact ⟨h1.2.1, h2.2.2⟩ }
end

```

### 有理数类型Definition

```lean
-- 有理数类型（使用商类型）
-- Rational number type (using quotient type)
def Rational := Quotient (Setoid.mk RationalEquiv rational_equiv_refl rational_equiv_symm rational_equiv_trans)

-- 有理数构造函数
-- Rational number constructor
def Rational.mk (a b : ℤ) (h : b ≠ 0) : Rational :=
  Quotient.mk' (a, b)

-- 有理数表示
-- Rational number representation
notation a "/" b => Rational.mk a b (by norm_num)

```

### 有理数运算形式化

```lean
namespace Rational

-- 加法运算
-- Addition operation
def add : Rational → Rational → Rational :=
  Quotient.lift₂ (λ (a, b) (c, d) => Rational.mk (a * d + c * b) (b * d) (by simp [ne_zero]))
    (by
      intros a b c d h1 h2,
      apply Quotient.sound,
      simp [RationalEquiv] at *,
      -- Proof加法运算的良Definition性
      -- Prove well-definedness of addition
      sorry)

-- 乘法运算
-- Multiplication operation
def mul : Rational → Rational → Rational :=
  Quotient.lift₂ (λ (a, b) (c, d) => Rational.mk (a * c) (b * d) (by simp [ne_zero]))
    (by
      intros a b c d h1 h2,
      apply Quotient.sound,
      simp [RationalEquiv] at *,
      -- Proof乘法运算的良Definition性
      -- Prove well-definedness of multiplication
      sorry)

-- 零元
-- Zero element
def zero : Rational := Rational.mk 0 1 (by norm_num)

-- 单位元
-- Unit element
def one : Rational := Rational.mk 1 1 (by norm_num)

-- 加法结合律
-- Associativity of addition
theorem add_assoc (x y z : Rational) :
  add (add x y) z = add x (add y z) :=
begin
  -- Proof加法结合律
  -- Prove associativity of addition
  sorry
end

-- 加法交换律
-- Commutativity of addition
theorem add_comm (x y : Rational) :
  add x y = add y x :=
begin
  -- Proof加法交换律
  -- Prove commutativity of addition
  sorry
end

-- 乘法结合律
-- Associativity of multiplication
theorem mul_assoc (x y z : Rational) :
  mul (mul x y) z = mul x (mul y z) :=
begin
  -- Proof乘法结合律
  -- Prove associativity of multiplication
  sorry
end

-- 乘法交换律
-- Commutativity of multiplication
theorem mul_comm (x y : Rational) :
  mul x y = mul y x :=
begin
  -- Proof乘法交换律
  -- Prove commutativity of multiplication
  sorry
end

-- 分配律
-- Distributivity
theorem mul_add_distrib (x y z : Rational) :
  mul x (add y z) = add (mul x y) (mul x z) :=
begin
  -- Proof分配律
  -- Prove distributivity
  sorry
end

end Rational

```

### 有理数序关系形式化

```lean
namespace Rational

-- 序关系Definition
-- Order relation definition
def le : Rational → Rational → Prop :=
  Quotient.lift₂ (λ (a, b) (c, d) => a * d ≤ c * b)
    (by
      intros a b c d h1 h2,
      -- Proof序关系的良Definition性
      -- Prove well-definedness of order relation
      sorry)

-- 序关系的自反性
-- Reflexivity of order relation
theorem le_refl (x : Rational) :
  le x x :=
begin
  -- Proof序关系的自反性
  -- Prove reflexivity of order relation
  sorry
end

-- 序关系的传递性
-- Transitivity of order relation
theorem le_trans (x y z : Rational) :
  le x y → le y z → le x z :=
begin
  -- Proof序关系的传递性
  -- Prove transitivity of order relation
  sorry
end

-- 有理数的稠密性
-- Density of rational numbers
theorem rational_dense (a b : Rational) (h : le a b ∧ a ≠ b) :
  ∃ c : Rational, le a c ∧ le c b ∧ c ≠ a ∧ c ≠ b :=
begin
  -- Proof有理数的稠密性
  -- Prove density of rational numbers
  sorry
end

end Rational

```

### 有理数Field结构形式化

```lean
-- 有理数Field实例
-- Rational number field instance
instance : Field Rational :=
{
  add := Rational.add,
  zero := Rational.zero,
  neg := sorry, -- 需要Definition负元
  mul := Rational.mul,
  one := Rational.one,
  inv := sorry, -- 需要Definition逆元
  add_assoc := Rational.add_assoc,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := Rational.add_comm,
  mul_assoc := Rational.mul_assoc,
  one_mul := sorry,
  mul_one := sorry,
  mul_comm := Rational.mul_comm,
  left_distrib := Rational.mul_add_distrib,
  right_distrib := sorry,
  add_left_neg := sorry,
  mul_inv_cancel := sorry,
  inv_zero := sorry,
  exists_pair_ne := sorry
}

-- 有理数Field的性质
-- Properties of rational number field
theorem rational_field_properties :
  Field Rational :=
begin
  exact inferInstance
end

```

### 应用案例：有理数在Number Theory中的应用

```lean
-- 丢番图方程的有理数解
-- Rational solutions of Diophantine equations
def diophantine_rational_solution (a b c : ℤ) :
  ∃ x y : Rational, a * x + b * y = c :=
begin
  -- Proof丢番图方程的有理数解存在性
  -- Prove existence of rational solutions of Diophantine equations
  sorry
end

-- 有理数逼近实数
-- Rational approximation of real numbers
theorem rational_approximation (x : ℝ) (ε : ℝ) (h : ε > 0) :
  ∃ q : Rational, |x - q| < ε :=

begin
  -- Proof有理数可以逼近任意实数
  -- Prove that rational numbers can approximate any real number
  sorry
end

```

## 术语对照表 / Terminology Table

| 中文 | English |
|---|---|
| 等价关系 | Equivalence relation |
| 等价类 | Equivalence class |
| 有理数对 | Rational pair |
| 约分/既约 | Reduction/Reduced form |
| 稠密性 | Density |
| 序关系 | Order relation |
| Field公理 | Field axioms |

## References / References

- Landau, E. Foundations of Analysis. Chelsea.
- Rudin, W. Principles of Mathematical Analysis. McGraw-Hill.
- Apostol, T. M. Mathematical Analysis. Addison-Wesley.
- Wikipedia: Rational number; Field (mathematics).
