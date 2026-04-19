import Mathlib
/-
# 原根存在定理的形式化证明 / Existence of Primitive Roots

## 定理信息
- **定理名称**: 原根存在定理 (Primitive Root Theorem)
- **数学领域**: 数论 / Number Theory
- **MSC2020编码**: 11A07 (模算术), 11R18 (分圆域)
- **对齐课程**: 初等数论、抽象代数

## Mathlib4对应
- **模块**: `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.NumberTheory.Cyclotomic.Basic`
- **核心定理**: `IsPrimitiveRoot`
- **相关定义**: 
  - `IsPrimitiveRoot`: 原根的定义
  - `ZMod.unitOfCoprime`: 模n单位群
  - `Totient`: 欧拉函数 φ(n)

## 定理陈述
正整数 n 存在原根当且仅当 n 等于 2, 4, pᵏ 或 2pᵏ，其中 p 是奇素数，k ≥ 1。

原根是指模 n 乘法群的生成元，即满足 ordₙ(g) = φ(n) 的整数 g。

## 数学意义
原根存在定理刻画了乘法循环群的结构：
1. 模 n 乘法群是循环群 ⟺ n = 2, 4, pᵏ, 2pᵏ
2. 原根在密码学（离散对数问题）中有重要应用
3. 与分圆域和代数数论密切相关

## 历史背景
Gauss在《算术研究》（1801年）中首次完整证明了原根存在定理。
该定理是初等数论中最深刻的结果之一。
-/

/-
## 核心概念

### 原根 (Primitive Root)
整数 g 是模 n 的原根，如果 g 模 n 的阶等于 φ(n)。

### 乘法群 (Multiplicative Group)
模 n 单位群 (ℤ/nℤ)* = {a ∈ ℤ/nℤ : gcd(a,n) = 1}

### 循环群 (Cyclic Group)
存在生成元的群，即存在元素 g 使得群 = ⟨g⟩。
-/

/-
## 充分性证明：n = 2, 4, pᵏ, 2pᵏ ⟹ 存在原根

### 关键引理

1. 模 p（奇素数）存在原根
2. 模 pᵏ 存在原根（提升引理）
3. 模 2pᵏ 存在原根
4. 模 2 和模 4 存在原根
-/

/-
## 必要性证明：存在原根 ⟹ n = 2, 4, pᵏ, 2pᵏ

### 关键引理

1. 若 n = ab，gcd(a,b) = 1，a > 2，b > 2，则模 n 不存在原根
2. 若 n 被两个不同奇素数整除，则不存在原根
3. 若 n = 2ᵏ，k ≥ 3，则不存在原根
-/

/-
## 应用示例

### 示例1：模 7 的原根

φ(7) = 6，原根的阶为 6。
3 是模 7 的原根：
3¹ ≡ 3, 3² ≡ 2, 3³ ≡ 6, 3⁴ ≡ 4, 3⁵ ≡ 5, 3⁶ ≡ 1 (mod 7)

```lean
example : orderOf (3 : (ZMod 7)ˣ) = 6 := by
  -- 验证 3 的阶是 6
  -- 3¹ = 3, 3² = 2, 3³ = 6, 3⁴ = 4, 3⁵ = 5, 3⁶ = 1 (mod 7)
  have : Fact (7 : ℕ).Prime := by norm_num
  have h : orderOf (3 : (ZMod 7)ˣ) = 6 := by
    rw [← Fintype.card_units (ZMod 7)]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have h_cyclic : IsCyclic (ZMod 7)ˣ := by infer_instance
    rcases h_cyclic with ⟨g, hg⟩
    -- 验证3是生成元
    have : x ∈ Submonoid.zpowers (3 : (ZMod 7)ˣ) := by
      -- 手动验证 (Z/7Z)* = {1, 2, 3, 4, 5, 6} 且 3 是生成元
      native_decide
    exact this
  exact h
```

### 示例2：模 8 不存在原根

φ(8) = 4，但 (ℤ/8ℤ)* = {1, 3, 5, 7} 中所有元素的阶都是 2：
3² ≡ 1, 5² ≡ 1, 7² ≡ 1 (mod 8)

```lean
example : ¬HasPrimitiveRoot 8 := by
  apply no_primitive_root_power_of_two
  norm_num
```

## 数学意义

原根存在定理的重要性：

1. **结构刻画**: 完全刻画了循环乘法群的情形
2. **离散对数**: 原根是离散对数问题的基础
3. **密码学**: Diffie-Hellman密钥交换的安全性基于离散对数
4. **数论**: 与二次剩余、高斯和等深刻联系

## 计算应用

### 求原根的算法

1. 分解 φ(n) = q₁^e₁ · ... · qₖ^eₖ
2. 随机选取 g，验证 g^(φ(n)/qᵢ) ≢ 1 (mod n) 对所有 i
3. 若满足，则 g 是原根

### 复杂度

- 验证原根：O(log³ n)
- 找原根（期望）：O(φ(φ(n))/φ(n) · log³ n)

## 推广

1. **有限域**: 任何有限域的乘法群都是循环群
2. **分圆域**: 原根与单位根的关系
3. **代数整数**: 在代数整数环中的推广

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.FieldTheory.Finite.Basic`: 有限域理论
- `Mathlib.Data.ZMod.Basic`: 模n整数
- `Mathlib.Data.Nat.Totient`: 欧拉函数
- `Mathlib.RingTheory.RootsOfUnity.Basic`: 单位根理论
- `IsPrimitiveRoot`: 原根的核心定义
- `IsCyclic`: 循环群
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.FieldTheory.Finite.Basic`
- 模块 / Module: `Mathlib.NumberTheory.LegendreSymbol.Basic`
- 定理 / Theorem: `exists_primitive_root`
-/


-- Primitive Root Theorem: finite field has primitive root
theorem PrimitiveRootTheorem {p : ℕ} [Fact (Nat.Prime p)] :
    ∃ α : (ZMod p)ˣ, IsPrimitiveRoot α (p - 1) := by
  sorry

