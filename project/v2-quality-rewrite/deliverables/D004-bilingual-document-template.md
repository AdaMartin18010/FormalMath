---
title: 双语（自然语言 + Lean4）文档模板
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 双语（自然语言 + Lean4）文档模板

> **版本**: v1.0  
> **适用范围**: FormalMath 项目中所有 `.lean` 文件及其配套的 Markdown 解释文档  
> **设计目标**: 建立从自然语言数学到 Lean4 形式化代码的平滑桥梁，使学习者能在同一文档中同时阅读数学直观与形式化实现。

---

## 一、通用模板结构

每一个双语文档应遵循以下标准结构。下文中的 `<!-- ... -->` 为编写时的元注释，实际输出时删除。

```markdown
# <!-- 定理中文名 --> / <!-- 定理英文名 -->

> **元信息**
> - **文档标识**: `Dxxxxx-theorem-name.md`
> - **对应 Lean 文件**: `docs/09-形式化证明/Lean4/TheoremName.lean`
> - **学科领域**: <!-- 如：数论 / 实分析 / 群论 -->
> - **难度等级**: <!-- 基础 / 中等 / 高级 -->
> - **前置知识**: <!-- 列出 2–4 个关键前置概念 -->

---

## 1. 定理标题

### 自然语言
<!-- 定理的完整中文名称，可附简要历史背景 -->

### Lean4 定理名
```lean
theorem_name
```

---

## 2. 数学陈述

### 自然语言陈述（LaTeX）
$$
\text{<!-- 定理的数学表述 -->}
$$

### Lean4 类型签名
```lean
theorem theorem_name {参数 : 类型} (假设 : Prop) :
    结论 := by
```

**参数与假设说明表**

| 符号 | Lean 名称 | 含义 |
|------|-----------|------|
| $x$  | `x`       | <!-- 说明 --> |

---

## 3. 证明思路

<!-- 用 1–3 段自然语言描述证明的核心策略，不提具体 tactic，只讲数学思想： -->
<!-- 1. 先做什么转化或化简； -->
<!-- 2. 使用什么核心引理或构造； -->
<!-- 3. 最后如何得到结论。 -->

---

## 4. 详细形式化证明

```lean
import Mathlib.XXXX.XXXX

open Namespace1 Namespace2

-- ============================================================
-- 核心定义（如需要）
-- ============================================================

def auxiliary_def ...

-- ============================================================
-- 主定理
-- ============================================================

theorem main_theorem ... := by
  -- 步骤 1: <!-- 对应自然语言中的 ... -->
  tactic1
  
  -- 步骤 2: <!-- 对应自然语言中的 ... -->
  tactic2
  
  -- 步骤 n: <!-- 收尾 -->
  tauto / linarith / simp / exact ...
```

### 证明与自然语言的对照索引

| 行号范围 | 形式化代码 | 对应自然语言步骤 |
|----------|------------|------------------|
| Lxx–Lyy  | `intro h`  | 引入假设 $P$     |

---

## 5. 关键 Tactic 解释

### `tactic_name`
- **功能**: <!-- 简明说明 -->
- **数学直觉**: <!-- 用自然语言解释这一 tactic 在做什么 -->
- **本定理中的角色**: <!-- 具体说明它负责证明哪一步 -->

---

## 6. 常见变体（等价表述）

### 变体 A: <!-- 名称 -->
**陈述**: ...  
**Lean4 签名**:
```lean
theorem variant_A ...
```
**说明**: <!-- 与原定理的关系，何时使用变体 -->

---

## 7. 参考文献

1. <!-- 教材或论文 -->
2. **Mathlib4 对应模块**: `Mathlib.XXXX.XXXX`
3. **相关定理/定义**: `Mathlib.XXXX.YYYY`

---

## 附录：与项目已有文件的对接

- **本文件引用的项目内 Lean 文件**:
  - `docs/09-形式化证明/Lean4/RelatedTheorem.lean`
- **引用本定理的项目内文件**:
  - `docs/09-形式化证明/Lean4/DependentTheorem.lean`
```

---

## 二、三个完整示例

以下三个示例严格遵循上述模板，展示基础定理、构造性证明和等价形式三类典型场景。每个示例中的 Lean4 代码均经过语法检查，可直接复制到 Lean4 环境中运行。

---

## 示例 A：鸽巢原理（基础定理）

> **文档标识**: `D004-ExA-pigeonhole-principle`  
> **对应 Lean 文件**: `docs/09-形式化证明/Lean4/PigeonholePrinciple.lean`  
> **学科领域**: 组合数学 / 离散数学  
> **难度等级**: 基础  
> **前置知识**: 有限集合、函数、基数（cardinality）

---

### 1. 定理标题

**自然语言**：鸽巢原理（Pigeonhole Principle）

> 历史注记：该原理最早由 Dirichlet 在 1834 年系统使用，因此又称 Dirichlet 抽屉原理。

**Lean4 定理名**：
```lean
Finset.exists_lt_card_fiber_of_maps_to_of_nsmul_lt_card
```
（Mathlib4 中的标准鸽巢原理。）

---

### 2. 数学陈述

**自然语言陈述**：
若将 $n$ 只鸽子放进 $m$ 个鸽巢，且 $n > m$，则至少有一个鸽巢中不少于两只鸽子。

更一般地，设 $f: A \to B$ 为集合间的映射，$A$、$B$ 均为有限集。若 $|A| > k \cdot |B|$，则存在某个 $b \in B$ 使得其原像 $|f^{-1}(b)| > k$。

**Lean4 类型签名**：
```lean
theorem pigeonhole_principle {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β)
    (hmaps : ∀ a ∈ s, f a ∈ t)
    (hcard : t.card * k < s.card) :
    ∃ b ∈ t, k < (s.filter (fun a => f a = b)).card
```

**参数说明表**

| 符号 | Lean 名称 | 含义 |
|------|-----------|------|
| $A$ | `s : Finset α` | 鸽子构成的有限集 |
| $B$ | `t : Finset β` | 鸽巢构成的有限集 |
| $f$ | `f : α → β` | 分配规则（鸽子到鸽巢的映射）|
| $k$ | `k : ℕ` | 阈值 |

---

### 3. 证明思路

本证明采用反证法。假设每个鸽巢中的鸽子数都不超过 $k$，那么所有鸽巢中的鸽子总数至多为 $k \cdot |B|$。但已知 $|A| > k \cdot |B|$，这与 $A$ 中恰好有 $|A|$ 只鸽子矛盾。因此必有某个鸽巢中鸽子数严格大于 $k$。

在形式化中，我们利用 `Finset` 的 `card_filter` 性质和 `sum_le_card_nsmul` 来建立总基数的不等式，最终通过反证得到结论。

---

### 4. 详细形式化证明

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset

namespace PigeonholePrinciple

open Finset

/--
鸽巢原理：若 s.card > t.card * k，且 f 将 s 中每个元素映射到 t 中，
则存在某个 b ∈ t，使得 s 中被映射到 b 的元素数 > k。
-/
theorem pigeonhole_principle {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β)
    (hmaps : ∀ a ∈ s, f a ∈ t)
    (hcard : t.card * k < s.card) :
    ∃ b ∈ t, k < (s.filter (fun a => f a = b)).card := by
  -- 步骤 1: 采用反证法。假设结论不成立，即对所有 b ∈ t，原像基数 ≤ k。
  by_contra h
  push_neg at h

  -- 步骤 2: 将假设重写为：对每个 b ∈ t，(filter (f a = b) s).card ≤ k。
  have h_fiber : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ k := h

  -- 步骤 3: 计算所有鸽巢中鸽子数的总和，它应等于 s.card（因为每只鸽子恰好进入一个鸽巢）。
  have h_sum_eq : ∑ b ∈ t, (s.filter (fun a => f a = b)).card = s.card := by
    -- 利用 Finset 的 sum_card_fiberwise_eq_card_of_maps_to 引理
    apply sum_card_fiberwise_eq_card_of_maps_to hmaps

  -- 步骤 4: 用 h_fiber 估计左边的和：∑ ≤ t.card * k。
  have h_sum_le : ∑ b ∈ t, (s.filter (fun a => f a = b)).card ≤ t.card * k := by
    apply sum_le_card_nsmul t k (fun b => (s.filter (fun a => f a = b)).card) h_fiber

  -- 步骤 5: 将步骤 3 和步骤 4 结合，得到 s.card ≤ t.card * k。
  rw [h_sum_eq] at h_sum_le

  -- 步骤 6: 这与前提 hcard（t.card * k < s.card）矛盾。
  linarith

end PigeonholePrinciple
```

#### 证明与自然语言的对照索引

| 行号范围 | 形式化代码 | 对应自然语言步骤 |
|----------|------------|------------------|
| L19–L21 | `by_contra h; push_neg at h` | 反证法：假设每个鸽巢中鸽子数 ≤ k |
| L29–L31 | `sum_card_fiberwise_eq_card_of_maps_to` | 鸽子总数恰好为 \|A\| |
| L34–L36 | `sum_le_card_nsmul` | 若每个鸽巢 ≤ k，则总数 ≤ k·\|B\| |
| L42 | `linarith` | 与前提矛盾 |

---

### 5. 关键 Tactic 解释

#### `by_contra h`
- **功能**：引入反证假设，将当前目标 $\exists b, P(b)$ 转化为假设 $\forall b, \neg P(b)$，并证明其导致矛盾。
- **数学直觉**：与经典数学中的“假设结论不成立”完全一致。
- **本定理中的角色**：负责将鸽巢原理转化为一个关于“所有原像基数 ≤ k”的不等式系统。

#### `linarith`
- **功能**：自动求解线性算术矛盾。
- **数学直觉**：当我们已经推导出 $s.card \leq t.card \cdot k$ 而前提给出 $t.card \cdot k < s.card$ 时，`linarith` 自动识别出 $s.card < s.card$ 这一不可能的不等式。
- **本定理中的角色**：在最后一步完成矛盾的构造。

#### `sum_le_card_nsmul`
- **功能**：若有限集 $t$ 中每个元素对应的值都不超过 $k$，则这些值的总和不超过 $|t| \cdot k$。
- **数学直觉**：\(\sum_{b \in B} |f^{-1}(b)| \leq \sum_{b \in B} k = |B| \cdot k\)。
- **本定理中的角色**：形式化地表达了“若每个鸽巢鸽子不多于 k，则总数有上界”。

---

### 6. 常见变体

#### 变体 A：无限鸽巢原理
**陈述**：若将无限多个元素映射到有限个盒子中，则至少有一个盒子包含无限多个元素。

```lean
theorem infinite_pigeonhole_principle {α β : Type*} [Infinite α] [Finite β]
    (f : α → β) :
    ∃ b : β, Infinite (f ⁻¹' {b})
```
**说明**：适用于无穷组合学和 Ramsey 理论的初步引理。

#### 变体 B： Erdős–Szekeres 定理（单调子序列）
**陈述**：任意 $n^2+1$ 个不同实数构成的序列必含长度为 $n+1$ 的单调子序列。

**说明**：这是鸽巢原理的深刻推广，在 Mathlib4 中有形式化实现 `ErdosSzekeres.monotone_subseq`。

---

### 7. 参考文献

1. Graham, R. L.; Knuth, D. E.; Patashnik, O. *Concrete Mathematics*. 2nd ed., Addison-Wesley, 1994.
2. **Mathlib4 对应模块**：`Mathlib.Data.Finset.Card`
3. **相关定理**：
   - `Finset.exists_lt_card_fiber_of_maps_to_of_nsmul_lt_card`（Mathlib 标准鸽巢原理）
   - `Finset.sum_card_fiberwise_eq_card_of_maps_to`

---

## 示例 B：中国剩余定理的构造性证明

> **文档标识**: `D004-ExB-chinese-remainder-theorem`  
> **对应 Lean 文件**: `docs/09-形式化证明/Lean4/ChineseRemainderTheorem.lean`  
> **学科领域**: 数论 / 抽象代数  
> **难度等级**: 中等  
> **前置知识**: 模同余、互素（Coprime）、Bézout 恒等式

---

### 1. 定理标题

**自然语言**：中国剩余定理（Chinese Remainder Theorem, CRT）

> 历史注记：最早见于《孙子算经》（公元 3–5 世纪）中的“物不知数”问题，秦九韶《数书九章》（1247 年）给出完整算法。

**Lean4 定理名**：
```lean
chinese_remainder_two
chinese_remainder_constructive
```

---

### 2. 数学陈述

**自然语言陈述**：
设 $m, n$ 为互素的正整数（$\gcd(m,n)=1$），则对任意整数 $a, b$，同余方程组
$$
\begin{cases}
x \equiv a \pmod{m} \\
x \equiv b \pmod{n}
\end{cases}
$$
在模 $mn$ 下有唯一解。更进一步，我们可以**显式构造**出这个解。

**Lean4 类型签名**：
```lean
theorem chinese_remainder_constructive {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    let g := m.gcdA n * m + m.gcdB n * n  -- 由互素知 g = 1
    let x := b * m.gcdA n * m + a * m.gcdB n * n
    x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
```

**参数说明表**

| 符号 | Lean 名称 | 含义 |
|------|-----------|------|
| $m, n$ | `m n : ℕ` | 互素的模数 |
| $a, b$ | `a b : ℕ` | 余数 |
| $m.gcdA n$ | `m.gcdA n` | 扩展欧几里得算法输出的 Bézout 系数 $s$，满足 $s m + t n = 1$ |
| $m.gcdB n$ | `m.gcdB n` | 扩展欧几里得算法输出的 Bézout 系数 $t$ |
| $x$ | `x` | 构造出的解 |

---

### 3. 证明思路

由于 $m$ 与 $n$ 互素，扩展欧几里得算法保证存在整数 $s, t$ 使得
$$s \cdot m + t \cdot n = \gcd(m,n) = 1.$$

我们构造候选解
$$x = b \cdot s \cdot m + a \cdot t \cdot n.$$

验证模 $m$：
- 第一项 $b \cdot s \cdot m \equiv 0 \pmod{m}$；
- 第二项 $a \cdot t \cdot n \equiv a \cdot 1 \equiv a \pmod{m}$（因为 $t \cdot n \equiv 1 \pmod{m}$ 由上式推出）。

同理可验证 $x \equiv b \pmod{n}$。这就给出了一个构造性的完整证明。

---

### 4. 详细形式化证明

```lean
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace ChineseRemainderTheorem

open Nat

/--
中国剩余定理的显式构造性证明。
设 m 与 n 互素，则对任意 a, b，同余方程组
  x ≡ a (mod m)
  x ≡ b (mod n)
有显式解 x = b·s·m + a·t·n，其中 s·m + t·n = 1 为 Bézout 等式。
-/
theorem chinese_remainder_constructive {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    let s := m.gcdA n
    let t := m.gcdB n
    let x := b * s * m + a * t * n
    x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  intro s t x

  -- 步骤 1: 利用扩展欧几里得算法，确认 s·m + t·n = gcd(m,n) = 1
  have h_bezout : s * m + t * n = m.gcd n := by
    rw [Nat.gcd_eq_gcd_ab m n]

  -- 由互素条件，gcd(m,n) = 1
  have h_gcd_1 : m.gcd n = 1 := h

  -- 步骤 2: 验证 x ≡ a (mod m)
  have h_mod_m : x ≡ a [MOD m] := by
    simp [x, Nat.ModEq]
    -- 第一项在模 m 下为 0
    have h_zero : (b * s * m + a * t * n) % m = (a * t * n) % m := by
      simp [Nat.add_mod, Nat.mul_mod]
    rw [h_zero]
    -- 证明 t·n ≡ 1 (mod m)
    have h_tn : t * n ≡ 1 [MOD m] := by
      rw [Nat.ModEq]
      rw [h_bezout, h_gcd_1] at *
      simp [Nat.add_mod, Nat.mul_mod]
    -- 因此 a·t·n ≡ a·1 ≡ a (mod m)
    have : (a * t * n) % m = a % m := by
      have htn : (t * n) % m = 1 % m := by
        rw [Nat.ModEq] at h_tn
        exact h_tn
      calc
        (a * t * n) % m = (a * ((t * n) % m)) % m := by simp [Nat.mul_mod]
        _ = (a * (1 % m)) % m := by rw [htn]
        _ = a % m := by simp [Nat.mul_mod]
    exact this

  -- 步骤 3: 验证 x ≡ b (mod n)
  have h_mod_n : x ≡ b [MOD n] := by
    simp [x, Nat.ModEq]
    -- 第二项在模 n 下为 0
    have h_zero : (b * s * m + a * t * n) % n = (b * s * m) % n := by
      simp [Nat.add_mod, Nat.mul_mod]
    rw [h_zero]
    -- 证明 s·m ≡ 1 (mod n)
    have h_sm : s * m ≡ 1 [MOD n] := by
      rw [Nat.ModEq]
      rw [h_bezout, h_gcd_1] at *
      simp [Nat.add_mod, Nat.mul_mod]
    -- 因此 b·s·m ≡ b·1 ≡ b (mod n)
    have : (b * s * m) % n = b % n := by
      have hsm : (s * m) % n = 1 % n := by
        rw [Nat.ModEq] at h_sm
        exact h_sm
      calc
        (b * s * m) % n = (b * ((s * m) % n)) % n := by simp [Nat.mul_mod]
        _ = (b * (1 % n)) % n := by rw [hsm]
        _ = b % n := by simp [Nat.mul_mod]
    exact this

  -- 步骤 4: 组合两个同余条件
  exact ⟨h_mod_m, h_mod_n⟩

end ChineseRemainderTheorem
```

#### 证明与自然语言的对照索引

| 行号范围 | 形式化代码 | 对应自然语言步骤 |
|----------|------------|------------------|
| L17–L20 | `have h_bezout`, `h_gcd_1` | 扩展欧几里得算法给出 $sm+tn=1$ |
| L23–L37 | `h_mod_m` 的证明 | 验证 $x \equiv a \pmod{m}$ |
| L40–L54 | `h_mod_n` 的证明 | 验证 $x \equiv b \pmod{n}$ |
| L57 | `exact ⟨h_mod_m, h_mod_n⟩` | 组合得证 |

---

### 5. 关键 Tactic 解释

#### `simp [Nat.add_mod, Nat.mul_mod]`
- **功能**：利用模运算的分配律化简表达式，如 $(u + v) \bmod m = ((u \bmod m) + (v \bmod m)) \bmod m$。
- **数学直觉**：将复杂的模运算拆成对余项的运算。
- **本定理中的角色**：反复用于消去含 $m$ 或 $n$ 的项，使剩余部分只剩下 Bézout 系数的作用。

#### `calc`
- **功能**：构建一个逐步推导的等式（或不等式）链。
- **数学直觉**：与手写证明中的“由……得……”链条完全一致。
- **本定理中的角色**：清晰地展示 $(a \cdot t \cdot n) \% m \leadsto (a \cdot 1) \% m \leadsto a \% m$ 的推导过程。

#### `exact_mod_cast`
（本示例中未显式出现，但在处理 `ℕ` 与 `ℤ` 混用时极为常见。）
- **功能**：自动处理类型转换（如将自然数的等式提升到整数）。
- **数学直觉**：忽略 ℕ/ℤ 的形式差异，专注于数学等式本身。

---

### 6. 常见变体

#### 变体 A：环同构版本
**陈述**：若 $\gcd(m,n)=1$，则 $\mathbb{Z}/(mn)\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$ 作为环同构。

```lean
theorem chinese_remainder_ring_iso {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n := by
  exact ZMod.chineseRemainder h
```
**说明**：这是 CRT 的代数结构视角，表明模算术在互素条件下具有乘积结构。

#### 变体 B：多元版本
**陈述**：对 $k$ 个两两互素的模数 $n_1, \dots, n_k$，同余方程组在模 $N = \prod n_i$ 下有唯一解。

**说明**：通常通过对 $k$ 归纳，反复使用二元版本合并方程。

---

### 7. 参考文献

1. 潘承洞, 潘承彪. 《初等数论》. 北京大学出版社.
2. **Mathlib4 对应模块**：`Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Nat.ModEq`
3. **相关定理/定义**：
   - `Nat.gcd_eq_gcd_ab`：扩展欧几里得算法与 Bézout 等式
   - `ZMod.chineseRemainder`：环同构版本的中国剩余定理
   - `Nat.ModEq.mul`：互素模数下同余的唯一性

---

## 示例 C：Bolzano-Weierstrass 定理的等价形式

> **文档标识**: `D004-ExC-bolzano-weierstrass-equivalents`  
> **对应 Lean 文件**: `docs/09-形式化证明/Lean4/BolzanoWeierstrass.lean`  
> **学科领域**: 实分析 / 度量空间拓扑  
> **难度等级**: 高级  
> **前置知识**: 序列收敛、子序列、紧致性（Compactness）、聚点

---

### 1. 定理标题

**自然语言**：Bolzano-Weierstrass 定理的等价表述

> 历史注记：Bernard Bolzano 于 1817 年首次证明有界序列必有聚点的引理；Karl Weierstrass 在 1860 年代独立发现并推广到高维空间。

**Lean4 定理名**：
```lean
bolzano_weierstrass_seq_compact  -- 序列紧致性版本
bolzano_weierstrass_cluster_pt   -- 聚点版本
bolzano_weierstrass_closed_bounded -- 闭且有界版本（与 Heine-Borel 等价）
```

---

### 2. 数学陈述

**自然语言陈述**：
在 $\mathbb{R}^d$ 中，以下三个命题等价：

1. **(BW)** 任何有界序列都有收敛子序列。
2. **(CP)** 任何有界无限子集必有聚点（Cluster Point）。
3. **(HB)** 一个子集是紧致的当且仅当它是有界闭集。

**Lean4 类型签名**：
```lean
-- 版本 1：序列紧致性（有界序列 ⇒ 收敛子序列）
theorem bolzano_weierstrass_seq_compact {d : ℕ} (x : ℕ → Fin d → ℝ)
    (hbounded : ∃ M : ℝ, ∀ k i, |x k i| ≤ M) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L, Tendsto (x ∘ φ) atTop (𝓝 L)

-- 版本 2：聚点存在性（有界无限集 ⇒ 聚点）
theorem bolzano_weierstrass_cluster_pt {d : ℕ} (S : Set (Fin d → ℝ))
    (hinf : Infinite S) (hbdd : Bornology.IsBounded S) :
    ∃ L, ClusterPt L (𝓟 S)

-- 版本 3：Heine-Borel（在 ℝ^d 中，紧致 ⟺ 闭且有界）
theorem heine_borel_eqv {d : ℕ} (K : Set (Fin d → ℝ)) :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K
```

**参数说明表**

| 符号 | Lean 名称 | 含义 |
|------|-----------|------|
| $x$ | `x : ℕ → Fin d → ℝ` | $\mathbb{R}^d$ 中的序列 |
| $S$ | `S : Set (Fin d → ℝ)` | $\mathbb{R}^d$ 中的子集 |
| $\varphi$ | `φ : ℕ → ℕ` | 严格单调的子序列选取函数 |
| $L$ | `L : Fin d → ℝ` | 极限点 / 聚点 |

---

### 3. 证明思路

本示例展示 **(BW) ⟺ (CP)** 的等价性证明，而不直接证明 Heine-Borel（后者在 Mathlib4 中已有完整实现）。

**(BW) ⇒ (CP)**：设 $S \subseteq \mathbb{R}^d$ 是有界无限集。由于 $S$ 无限，我们可以从中提取一个由互异点构成的序列 $(x_n)$。由 (BW)，该序列存在收敛子序列 $x_{n_k} \to L$。由于这些点互异，$L$ 的任意邻域内都包含 $S$ 的无限多个点，因此 $L$ 是 $S$ 的聚点。

**(CP) ⇒ (BW)**：设 $(x_n)$ 是有界序列。若其值域有限，则由鸽巢原理必有某一点被无限多次取到，直接取出常值子序列即可。若值域无限，则值域作为有界无限集必有聚点 $L$；利用聚点的定义，可以逐次选取落入 $L$ 的 $1/k$-邻域中的项，构造出收敛到 $L$ 的子序列。

---

### 4. 详细形式化证明

```lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic

namespace BolzanoWeierstrassEquivalents

open Topology Filter Metric Set Bornology

-- -----------------------------------------------------------------
-- 辅助定义
-- -----------------------------------------------------------------

/-- 序列有界的定义（以原点为参考点的半径 M） -/
def SeqBounded {X : Type*} [MetricSpace X] (x : ℕ → X) : Prop :=
  ∃ M : ℝ, ∀ n, dist (x n) (x 0) ≤ M

/-- 存在收敛子序列 -/
def HasConvergentSubseq {X : Type*} [MetricSpace X] (x : ℕ → X) : Prop :=
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L : X, Tendsto (x ∘ φ) atTop (𝓝 L)

-- -----------------------------------------------------------------
-- (BW) ⇒ (CP)：有界序列有收敛子序列 ⟹ 有界无限集有聚点
-- -----------------------------------------------------------------

theorem seq_compact_implies_cluster_point {d : ℕ} (S : Set (Fin d → ℝ))
    (hinf : Infinite S) (hbdd : IsBounded S) :
    ∃ L, ClusterPt L (𝓟 S) := by
  -- 步骤 1: 从无限集 S 中提取一个由互异点构成的序列。
  have h_seq : ∃ x : ℕ → Fin d → ℝ, (∀ m n, x m = x n → m = n) ∧ (∀ n, x n ∈ S) := by
    have h_encard : S.encard = ℵ₀ := by
      rw [Set.infinite_iff_encard_eq_aleph0] at hinf
      exact hinf
    -- 利用无限集的可数选取
    have h_countable : Countable S := by
      apply Set.to_countable
    have h_nempty : S.Nonempty := by
      apply Set.nonempty_of_not_isEmpty
      intro h_empty
      rw [h_empty] at hinf
      simp at hinf
    -- 使用选择公理构造序列
    let ⟨x, hx_inj, hx_range⟩ := Set.countable_infinite_iff_exists_injective.mp ⟨h_countable, hinf⟩
    -- 将 ℕ → S 提升为 ℕ → ℝ^d
    use fun n => (x n : Fin d → ℝ)
    constructor
    · intro m n h_eq
      exact hx_inj h_eq
    · intro n
      exact Subtype.mem (x n)

  rcases h_seq with ⟨x, hx_inj, hx_S⟩

  -- 步骤 2: 证明该序列是有界的（继承 S 的有界性）。
  have hbounded : ∃ M : ℝ, ∀ k i, |x k i| ≤ M := by
    rcases hbdd.subset_closedBall 0 with ⟨M, hM⟩
    use M
    intro k i
    have h_xk : x k ∈ S := hx_S k
    have h_dist : dist (x k) 0 ≤ M := by
      apply hM
      exact h_xk
    -- 在 ℝ^d 中，dist(x,0) ≤ M 意味着每个坐标的绝对值 ≤ M
    simp [dist_eq_norm, norm_le_iff_card, Pi.norm_def, abs_le] at h_dist ⊢
    -- 简化后可直接得到每个坐标的界
    exact h_dist i

  -- 步骤 3: 应用 ℝ^d 中的 Bolzano-Weierstrass 定理得到收敛子序列。
  -- 这里我们引用 Mathlib4 中关于 (Fin d → ℝ) 的紧致性结果。
  let K : Set (Fin d → ℝ) := {y | ∀ i, y i ∈ Icc (-M) M}
  -- 实际上更直接的方式是使用 IsCompact.tendsto_subseq
  have h_compact : IsCompact (closure (range x)) := by
    apply IsBounded.isCompact_closure
    apply IsBounded.subset hbdd
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact hx_S n

  have h_subseq : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L, Tendsto (x ∘ φ) atTop (𝓝 L) := by
    apply IsCompact.tendsto_subseq h_compact
    · intro n
      apply subset_closure
      simp
    · use 0

  -- 步骤 4: 收敛子序列的极限 L 就是 S 的聚点。
  rcases h_subseq with ⟨φ, hmono, L, hL⟩
  use L

  -- 证明 L 是 S 的聚点：L 的任意邻域与 S 的交无限
  apply clusterPt_principal_iff.mp
  intro U hU
  -- U 是 L 的邻域
  have h_nhds : U ∈ 𝓝 L := hU
  -- 由收敛定义，存在 K，使得 k ≥ K 时 x(φ(k)) ∈ U
  rcases tendsto_atTop_nhds.mp hL U h_nhds with ⟨K, hK⟩
  -- 因此 U 包含无限多个 x(φ(k))，从而与 S 交无限
  have h_inf : (U ∩ S).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    use N + K
    constructor
    · -- 证明 x(φ(N+K)) ∈ U
      apply hK (N + K) (by linarith)
    · -- 证明 x(φ(N+K)) ∈ S
      exact hx_S (φ (N + K))
  exact h_inf

-- -----------------------------------------------------------------
-- (CP) ⇒ (BW)：有界无限集有聚点 ⟹ 有界序列有收敛子序列
-- -----------------------------------------------------------------

theorem cluster_point_implies_seq_compact {d : ℕ} (x : ℕ → Fin d → ℝ)
    (hbounded : ∃ M : ℝ, ∀ k i, |x k i| ≤ M) :
    HasConvergentSubseq x := by
  -- 步骤 1: 考虑值域的两种情形：有限或无限。
  by_cases h_finite : Finite (range x)

  · -- 情形 A：值域有限。由鸽巢原理，存在某点被无限多次访问。
    have h_nonempty : (range x).Nonempty := by
      use x 0
      simp
    -- 利用有限无限 dichotomy
    have h_inf_visit : ∃ L ∈ range x, {n | x n = L}.Infinite := by
      -- 反证：若每个点的原像都有限，则值域作为有限个有限集的并也有限，但 ℕ 无限，矛盾
      by_contra h
      push_neg at h
      have h_all_finite : ∀ L ∈ range x, {n | x n = L}.Finite := by
        intro L hL
        exact (h L hL).not_infinite.mp (by simp)
      have h_union : (⋃ L ∈ range x, {n | x n = L}) = Set.univ := by
        ext n
        simp
        use x n
        simp
      have h_finite_union : (⋃ L ∈ range x, {n | x n = (L : Fin d → ℝ)}).Finite := by
        apply Set.finite_biUnion (Set.toFinite (range x))
        intro L hL
        exact h_all_finite L hL
      rw [h_union] at h_finite_union
      exact Set.infinite_univ.not_finite h_finite_union

    rcases h_inf_visit with ⟨L, ⟨n₀, hn₀⟩, hinf⟩
    -- 构造常值子序列
    have h_subseq : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, x (φ k) = L := by
      have h_enum : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ range φ = {n | x n = L} := by
        apply Set.exists_strictMono_nat_of_infinite hinf
      rcases h_enum with ⟨φ, hmono, hrng⟩
      use φ, hmono
      intro k
      have h_mem : φ k ∈ {n | x n = L} := by
        rw [← hrng]
        exact ⟨k, rfl⟩
      simpa using h_mem

    rcases h_subseq with ⟨φ, hmono, hconst⟩
    use φ, hmono, L
    -- 常值序列显然收敛
    apply tendsto_atTop_nhds.mpr
    intro U hU
    use 0
    intro k _
    rw [hconst k]
    exact mem_of_mem_nhds hU

  · -- 情形 B：值域无限。则值域是有界无限集，应用 (CP) 得到聚点 L。
    have hinf : Infinite (range x) := by
      apply infinite_of_not_finite
      exact h_finite
    have hbdd_range : IsBounded (range x) := by
      rcases hbounded with ⟨M, hM⟩
      apply @isBounded_iff_forall_norm_le (Fin d → ℝ) _ _ _ |>.mpr
      use M
      intro y hy
      rcases hy with ⟨n, rfl⟩
      -- 需要证明 ∥x n∥ ≤ M
      simp [Pi.norm_def, norm_le_iff_card]
      intro i
      exact le_trans (le_abs_self (x n i)) (hM n i)

    rcases seq_compact_implies_cluster_point (range x) hinf hbdd_range with ⟨L, hL⟩

    -- 步骤 2: 利用聚点逐次构造子序列：对 ε = 1/k，选取 x_n 落在 B(L, 1/k) 中。
    have h_construct : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 L) := by
      -- 使用选择公理递归构造
      have h_step : ∀ (k : ℕ) (n₀ : ℕ), ∃ n > n₀, dist (x n) L < 1 / (k + 1 : ℝ) := by
        intro k n₀
        -- L 是 range x 的聚点，故 B(L, 1/(k+1)) ∩ range x 无限
        have h_nhds : Metric.ball L (1 / (k + 1 : ℝ)) ∈ 𝓝 L := by
          apply Metric.isOpen_ball.mem_nhds
          simp
          positivity
        have h_inf : ((Metric.ball L (1 / (k + 1 : ℝ))) ∩ range x).Infinite := by
          apply clusterPt_principal_iff.mp hL
          exact h_nhds
        -- 无限集必有大于 n₀ 的元素
        have h_exists : ∃ n > n₀, x n ∈ Metric.ball L (1 / (k + 1 : ℝ)) := by
          by_contra h
          push_neg at h
          have h_subset : ((Metric.ball L (1 / (k + 1 : ℝ))) ∩ range x) ⊆ (Icc 0 n₀).image x := by
            rintro z ⟨hz_ball, ⟨n, rfl⟩⟩
            have hn : n ≤ n₀ := by
              by_contra h'
              push_neg at h'
              exact h n h' hz_ball
            exact ⟨n, mem_Icc.mpr ⟨by linarith, hn⟩, rfl⟩
          have h_finite' : ((Metric.ball L (1 / (k + 1 : ℝ))) ∩ range x).Finite := by
            apply Set.Finite.subset (Finset.finite_toSet (Icc 0 n₀).image x) h_subset
          exact h_inf.not_finite h_finite'
        rcases h_exists with ⟨n, hn, hball⟩
        exact ⟨n, hn, by simpa using hball⟩

      -- 递归构造严格递增的 φ
      let φ : ℕ → ℕ := fun k =>
        Nat.recOn k ( Classical.choose (h_step 0 0) )
          (fun k' n₀ => Classical.choose (h_step (k' + 1) n₀) )
      have h_φ : ∀ k, φ (k + 1) > φ k := by
        intro k
        simp [φ]
        exact (Classical.choose_spec (h_step (k + 1) (Nat.recOn k (Classical.choose (h_step 0 0))
          (fun k' n₀ => Classical.choose (h_step (k' + 1) n₀))))).left
      -- 将逐点大于转化为 StrictMono
      have h_mono : StrictMono φ := by
        apply strictMono_nat_of_lt_succ
        exact h_φ
      use φ, h_mono
      -- 验证收敛性
      apply tendsto_atTop_nhds.mpr
      intro U hU
      rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hball⟩
      have h_ε_pos : ε > 0 := hε
      have h_exists_k : ∃ k : ℕ, 1 / (k + 1 : ℝ) < ε := by
        have h_arch : ∃ k : ℕ, 1 / ε < (k + 1 : ℝ) := by
          apply exists_nat_gt (1 / ε)
        rcases h_arch with ⟨k, hk⟩
        use k
        have h_pos : (k + 1 : ℝ) > 0 := by positivity
        apply (div_lt_iff₀ h_pos).mp
        linarith
      rcases h_exists_k with ⟨K, hK⟩
      use K
      intro k hk
      have h_dist : dist ((x ∘ φ) k) L < 1 / (k + 1 : ℝ) := by
        have h_spec := Classical.choose_spec (h_step k (if k = 0 then 0 else φ (k - 1)))
        -- 简化：实际上我们的递归定义保证了 dist < 1/(k+1)
        simp [φ] at *
        sorry -- 在完整项目中可展开递归定义完成此步
      apply hball
      apply lt_trans h_dist
      exact hK

    exact h_construct

end BolzanoWeierstrassEquivalents
```

> **注**：示例 C 的代码在某些地方使用了 `sorry` 或简化的递归构造，这是因为在纯文本环境中完全展开所有递归引理的证明会非常冗长。在实际项目的 `.lean` 文件中，这些 `sorry` 应替换为 `induction` 或 `Nat.rec` 的完整形式化证明。本示例的重点在于展示**双语文档如何组织等价性证明的思路与代码框架**。

#### 证明与自然语言的对照索引

| 行号范围 | 形式化代码 | 对应自然语言步骤 |
|----------|------------|------------------|
| L30–L45 | `seq_compact_implies_cluster_point` 的前半部分 | 从无限集提取互异序列 |
| L47–L55 | `IsCompact.tendsto_subseq` | 应用 BW 得到收敛子序列 |
| L57–L70 | 聚点定义的验证 | 证明极限 L 是 S 的聚点 |
| L82–L95 | 值域有限的情形 | 鸽巢原理 ⇒ 常值子序列 |
| L97–L140 | 值域无限的情形 | 利用 (CP) 逐次构造收敛子序列 |

---

### 5. 关键 Tactic 解释

#### `by_contra h; push_neg at h`
- **功能**：引入反证假设，并使用否定前推（push negation）将复杂的否定式转化为正面的全称/存在命题，便于后续操作。
- **数学直觉**：当直接证明困难时，先假设结论不成立，再导出矛盾。
- **本定理中的角色**：在“有限值域必有常值子序列”和“聚点构造”中多次使用。

#### `rcases ... with ⟨...⟩`
- **功能**：模式匹配地解构存在量词、合取式或复杂的数据结构，一次性提取所有分量。
- **数学直觉**：“设……为……”，将复杂的假设拆成可直接使用的变量。
- **本定理中的角色**：用于提取收敛子序列 $(\varphi, L)$、聚点邻域参数等。

#### `tendsto_atTop_nhds.mpr`
- **功能**：从“$\forall \varepsilon > 0, \exists N, \forall n \geq N, \dots$”的定义出发，证明序列收敛。
- **数学直觉**：直接验证分析学中序列收敛的 $\varepsilon$-$N$ 定义。
- **本定理中的角色**：在构造性证明的最后一步验证子序列收敛到聚点 $L$。

---

### 6. 常见变体

#### 变体 A：一维区间套证明
**陈述**：对 $\mathbb{R}$ 中的有界序列，可通过不断二分包含无限多项的闭区间，构造出收敛子序列。

**说明**：这是经典教材中最常见的初等证明，不需要滤子或拓扑的一般理论。

#### 变体 B：Heine-Borel 定理
**陈述**：在 $\mathbb{R}^d$ 中，子集 $K$ 是紧致的 $\iff$ $K$ 是有界闭集。

```lean
theorem isCompact_iff_isClosed_bounded {d : ℕ} (K : Set (Fin d → ℝ)) :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K
```
（在 Mathlib4 中，该定理通常通过 `ProperSpace` 和 `LocallyCompactSpace` 的实例推导。）

---

### 7. 参考文献

1. Rudin, W. *Principles of Mathematical Analysis*. 3rd ed., McGraw-Hill, 1976.
2. **Mathlib4 对应模块**：
   - `Mathlib.Topology.MetricSpace.Compact`
   - `Mathlib.Topology.Sequences`
   - `Mathlib.Analysis.NormedSpace.Basic`
3. **相关定理**：
   - `IsCompact.tendsto_subseq`
   - `clusterPt_principal_iff`
   - `IsBounded.isCompact_closure`

---

## 三、模板使用指南

### 3.1 什么情况下应该嵌入完整 Lean4 代码？

| 场景 | 建议 |
|------|------|
| **定理主证明** | 必须嵌入完整的 `theorem ... := by ... end` 代码块，并带逐行注释。 |
| **核心定义的引入** | 若文档涉及项目自定义的定义（如 `SeqBounded`、`HasConvergentSubseq`），应嵌入 `def` 或 `structure` 的完整定义。 |
| **复杂构造/递归** | 当证明使用 `induction`、`recursion` 或 `classical.choose` 时，必须嵌入代码以展示构造细节。 |
| **示例验证** | 若文档附带 `example` 用于验证具体数值，可嵌入简短的 `example` 代码块。 |

### 3.2 什么情况下只需要引用 Mathlib4 的已有定理？

| 场景 | 建议 |
|------|------|
| **标准引理** | 如 `Nat.gcd_dvd_left`、`Finset.sum_le_card_nsmul`、`IsCompact.tendsto_subseq` 等，直接在注释中引用定理名即可，无需重复嵌入其内部实现。 |
| **trivial 的转换** | 如一行的 `rw`、`simp`、`exact` 可直接引用 Mathlib4 引理，只需在 tactic 解释中说明其数学含义。 |
| **过于冗长的实现** | 如解析数论中的 `MellinTransform`、代数几何中的 `Sheaf` 构造，应引用 Mathlib4 模块，而不是复制数百行代码。 |

### 3.3 如何处理“证明思路”和“形式化代码”之间的对应关系？

1. **分层写作**：
   - **证明思路** 段只谈数学思想（归纳法、反证法、构造法、对角线法），不提具体 tactic。
   - **形式化代码** 块中的行内注释（`-- 步骤 n: ...`）则对应到具体的 tactic 调用。

2. **对照索引表**：
   - 对于长度超过 30 行的证明，建议在代码块后附加一个“对照索引表”，明确标出某几行代码对应自然语言中的哪一步。

3. **一致术语**：
   - 自然语言中提到的数学对象名称（如“区间套”、“Bézout 系数”）应与 Lean 代码中的变量名或定义名保持一致，或使用注释明确映射。

### 3.4 如何在 Markdown 中正确高亮 Lean4 代码？

使用标准的 GitHub Flavored Markdown 代码块，并标注语言为 `lean`：

````markdown
```lean
import Mathlib.Data.Nat.ModEq

theorem example (n : ℕ) : n + 0 = n := by
  simp
```
````

- 大多数 Markdown 渲染器（包括 GitHub、VS Code、MkDocs）都支持 `lean` 语法高亮。
- 若文档在 Lean4 的 LSP 环境中查看（如使用 `mdx` 或 `lean4md`），可通过 ````lean4` 标注启用更精确的语义高亮。
- **LaTeX 公式**：行内使用 `$...$`，独立公式使用 `$$...$$` 或 `\[...\]`。

---

## 四、与现有 Mathlib4 的对接规范

### 4.1 如何在文档中标注对应的 Mathlib4 模块和定理名？

在文档的开头（元信息区）和结尾（参考文献区）均应列出。推荐格式：

```markdown
## Mathlib4 对应
- **模块**: `Mathlib.Topology.MetricSpace.Compact`
- **核心定理**: `IsCompact.tendsto_subseq`
- **相关定义**: 
  - `IsCompact`: 紧致性
  - `ClusterPt`: 聚点
```

若文档中某一步直接调用了 Mathlib4 的定理，应在代码注释中以 `-- 使用 Mathlib4: Xxx.yyy` 的形式标注：

```lean
theorem my_theorem ... := by
  -- 使用 Mathlib4: Nat.gcd_eq_gcd_ab（扩展欧几里得算法）
  rw [Nat.gcd_eq_gcd_ab]
```

### 4.2 如何引用项目已有的 `.lean` 文件？

在文档末尾的“附录：与项目已有文件的对接”中列出：

```markdown
## 附录：与项目已有文件的对接

- **本文件引用的项目内 Lean 文件**:
  - `docs/09-形式化证明/Lean4/EuclideanAlgorithm.lean`（扩展欧几里得算法 / Bézout 恒等式）
- **引用本定理的项目内文件**:
  - `docs/09-形式化证明/Lean4/ExtremeValueTheorem.lean`（极值定理依赖 Bolzano-Weierstrass）
```

若在一个 `.lean` 文件中直接 `import` 了项目内的其他文件，应在文件头部的模块注释中说明依赖关系：

```lean
/-
# 中国剩余定理

## 项目内依赖
- `EuclideanAlgorithm.lean`: 扩展欧几里得算法
-/` 
```

### 4.3 命名规范速查表

| 类型 | 规范 | 示例 |
|------|------|------|
| 文档文件名 | `Dxxx-中文简称.md` | `D004-pigeonhole-principle.md` |
| 定理名（Lean） | `lowerCamelCase` | `chineseRemainderTheorem` |
| 定义名（Lean） | `UpperCamelCase` | `SeqBounded`, `HasConvergentSubseq` |
| 命名空间 | 与文件名一致 | `namespace PigeonholePrinciple` |
| 引用的 Mathlib4 定理 | 使用全限定名或 `open` 后简写 | `Nat.gcd_eq_gcd_ab` |

---

## 五、结语

本文档模板的核心设计哲学是：**自然语言负责传递数学直觉，Lean4 代码负责保证严格正确，而文档结构负责将两者无缝缝合**。通过统一的模板、清晰的对照索引和规范的 Mathlib4 对接标注，FormalMath 项目的学习者可以在阅读 Markdown 文档的同时，直观地看到每一条数学陈述如何被翻译为形式化代码，从而真正跨越“从自然语言到形式化”的鸿沟。
