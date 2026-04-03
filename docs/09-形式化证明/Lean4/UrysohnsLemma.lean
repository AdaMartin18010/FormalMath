/-
# 乌雷松引理的形式化证明 / Urysohn's Lemma

## 领域
一般拓扑学 (General Topology)

## Mathlib4对应
- **模块**: `Mathlib.Topology.UrysohnsLemma`
- **核心定理**: `exists_continuous_zero_one_of_isClosed`
- **相关定义**:
  - `NormalSpace`
  - `IsClosed`
  - `Continuous`

## MSC2020编码
- **Primary**: 54D15
- **Secondary**: 54C05

## 对齐课程
- MIT 18.901 (Introduction to Topology)
- Harvard Math 131 (Topology I)
- Princeton MAT 365 (Topology)
- ETH 401-3050-00L (Topology)

## 定理陈述
设 X 是正规拓扑空间，A 和 B 是 X 中两个不相交的闭集。
则存在连续函数 f : X → [0, 1]，使得：
- f(x) = 0 对所有 x ∈ A
- f(x) = 1 对所有 x ∈ B

## 数学意义
乌雷松引理是正规空间的重要刻画，也是证明Tietze扩张定理和Urysohn度量化定理的关键工具。

## 历史背景
由Pavel Urysohn在1925年证明，是点集拓扑学中最优美的结果之一。
-/

import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Separation
import Mathlib.Data.Real.Basic

universe u

namespace UrysohnsLemma

open Topology Set Real

/-
## 核心概念

### 正规空间 (Normal Space)
拓扑空间 X 是正规的，如果：
1. X 是 T₁ 空间（单点集是闭的）
2. 任意两个不相交闭集可以被不相交开集分离

### 乌雷松函数
连接两个不相交闭集的连续函数，取值于[0,1]。
-/

variable {X : Type u} [TopologicalSpace X] [NormalSpace X]

-- 乌雷松引理：核心定理
theorem urysohns_lemma {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ f : X → ℝ, Continuous f ∧ EqOn f (fun _ => 0) A ∧ EqOn f (fun _ => 1) B ∧
    ∀ x, f x ∈ Icc 0 1 := by
  /- 使用Mathlib4的乌雷松引理 -/
  exact exists_continuous_zero_one_of_isClosed hA hB hAB

-- 乌雷松引理的变体：f(A)=0, f(B)=1，且 0 ≤ f ≤ 1
theorem urysohns_lemma' {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ f : C(X, ℝ), (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1) ∧
    ∀ x, f x ∈ Icc 0 1 := by
  /- 构造连续映射 f : X → ℝ -/
  rcases exists_continuous_zero_one_of_isClosed hA hB hAB with ⟨f, hf_cont, hfA, hfB, hf_range⟩
  exact ⟨⟨f, hf_cont⟩, hfA, hfB, hf_range⟩

-- 完全正则空间的刻画
theorem completely_regular_of_normal (x : X) {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : C(X, ℝ), f x = 0 ∧ (∀ y ∉ U, f y = 1) ∧ ∀ y, f y ∈ Icc 0 1 := by
  /- 正规空间是完全正则的 -/
  have h_closed : IsClosed Uᶜ := hU.isClosed_compl
  have h_disj : Disjoint {x} Uᶜ := by
    simp [hx]
  rcases exists_continuous_zero_one_of_isClosed isClosed_singleton h_closed h_disj with
    ⟨f, hf_cont, hfx, hfU, hf_range⟩
  exact ⟨⟨f, hf_cont⟩, by simpa using hfx, by simpa using hfU, hf_range⟩

/-
## 应用：正规空间的函数分离性

乌雷松引理表明正规空间中的闭集可以被连续实函数分离。
-/

theorem closed_sets_separated_by_function {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ f : C(X, ℝ), f '' A ⊆ {0} ∧ f '' B ⊆ {1} := by
  rcases urysohns_lemma' hA hB hAB with ⟨f, hfA, hfB, -⟩
  exact ⟨f, by simp [hfA], by simp [hfB]⟩

end UrysohnsLemma

/-
## 应用示例

### Tietze扩张定理的证明

乌雷松引理是证明Tietze扩张定理的关键步骤。通过反复应用乌雷松引理，
可以将闭集上的有界连续函数扩张到整个空间。

### Urysohn度量化定理

正规且具有可数基的空间可以嵌入到Hilbert立方体 [0,1]^ℕ 中，从而是可度量化的。

## 数学意义

乌雷松引理的重要性：

1. **正规空间刻画**: 连续函数分离闭集的能力
2. **Tietze定理基础**: 函数扩张的核心工具
3. **度量化定理**: Urysohn度量化定理的关键
4. **分析学应用**: 在测度论和泛函分析中有广泛应用

## 与其他定理的关系

- **Tietze扩张定理**: 乌雷松引理的强化
- **Urysohn度量化定理**: 正规+第二可数 ⟹ 可度量化
- **Riesz表示定理**: 与连续函数空间的对偶相关

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.UrysohnsLemma`: 乌雷松引理
- `exists_continuous_zero_one_of_isClosed`: 核心实现
- `Mathlib.Topology.Separation`: 分离公理
- `NormalSpace`: 正规空间定义
-/
