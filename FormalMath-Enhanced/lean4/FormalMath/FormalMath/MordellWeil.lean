/-
# 莫德尔-韦伊定理 (Mordell-Weil Theorem)

## 数学背景

莫德尔-韦伊定理是椭圆曲线算术理论的基石结果，
描述了有理点群的结构：

**定理（Mordell, 1922; Weil, 1928）**：
设E是定义在数域K上的椭圆曲线，则E(K)是有限生成Abel群。

即：E(K) ≅ ℤ^r × E(K)_tors

其中：
- r 称为椭圆曲线的秩（rank）
- E(K)_tors 是有限挠子群

## 历史发展

- **Poincaré (1901)**：猜测椭圆曲线有理点群的结构
- **Mordell (1922)**：证明E(ℚ)是有限生成的（E/ℚ的情形）
- **Weil (1928)**：推广到任意Abel簇和任意数域，使用高度理论
- **Néron (1952)**：发展了规范高度理论
- **Tate (1960s)**：发展了Tate-Shafarevich群理论

## 证明概览

证明分为两个主要部分：

1. **弱莫德尔-韦伊定理**：E(K)/nE(K)是有限的（对某n ≥ 2）
2. **下降法**：利用高度函数将弱定理提升到完整定理

## 参考

- Mordell, L.J. "On the rational solutions of the indeterminate equations of the third and fourth degrees" (1922)
- Weil, A. "L'arithmétique sur les courbes algébriques" (1928)
- Silverman, J.H. "The Arithmetic of Elliptic Curves" (GTM 106)
- Serre, J.P. "Lectures on the Mordell-Weil Theorem"
- Wikipedia: https://en.wikipedia.org/wiki/Mordell%E2%80%93Weil_theorem
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.FieldTheory.Galois

namespace MordellWeil

open Classical Polynomial AlgebraicGeometry NumberField

universe u v

/-! 
## 椭圆曲线基础

椭圆曲线是亏格为1的光滑射影曲线，带有有理点作为单位元。
在非特征2,3的域上，可表示为Weierstrass方程：
y² = x³ + ax + b，其中4a³ + 27b² ≠ 0
-/

-- 数域（特征0的有限扩张）
class NumberField (K : Type u) extends Field K, CharZero K, FiniteDimensional ℚ K

-- Weierstrass曲线（简化形式）
structure WeierstrassCurve (K : Type u) [Field K] where
  a : K  -- x的系数
  b : K  -- 常数项
  discriminant_nonzero : 4 * a^3 + 27 * b^2 ≠ 0  -- 光滑性条件

-- 椭圆曲线（Weierstrass曲线的射影闭包）
def EllipticCurve (K : Type u) [Field K] :=
  WeierstrassCurve K

-- 射影平面上的点（简化定义）
structure ProjectivePoint (K : Type u) [Field K] where
  x : K
  y : K
  z : K
  nonzero : ¬(x = 0 ∧ y = 0 ∧ z = 0)

-- 椭圆曲线上的点（仿射点满足Weierstrass方程，或无穷远点）
structure EllipticCurve.Point {K : Type u} [Field K] (E : EllipticCurve K) where
  x : K
  y : K
  z : K
  -- 满足齐次化方程：y²z = x³ + axz² + bz³
  eqn : z = 0 ∨ (z ≠ 0 ∧ y^2 * z = x^3 + E.a * x * z^2 + E.b * z^3)

-- 无穷远点（单位元）
def EllipticCurve.Zero {K : Type u} [Field K] {E : EllipticCurve K} : E.Point :=
  ⟨0, 1, 0, Or.inl rfl⟩

/-! 
## 椭圆曲线的群结构

椭圆曲线上的点构成Abel群，群法则几何描述：

- **单位元**：无穷远点O = [0:1:0]
- **逆元**：-(x, y) = (x, -y)
- **加法**：P + Q = R，其中R是连接P和Q的直线与曲线的第三个交点关于x轴的对称点

代数公式（仿射坐标）：
设P = (x₁, y₁)，Q = (x₂, y₂)

若P ≠ Q：λ = (y₂ - y₁) / (x₂ - x₁)
若P = Q（倍点）：λ = (3x₁² + a) / (2y₁)

x₃ = λ² - x₁ - x₂
y₃ = λ(x₁ - x₃) - y₁
-/

-- 点的加法（弦切法）
def EllipticCurve.Point.add {K : Type u} [Field K] {E : EllipticCurve K} 
    (P Q : E.Point) : E.Point :=
  if P.z = 0 then Q  -- P是无穷远点
  else if Q.z = 0 then P  -- Q是无穷远点
  else
    let x1 := P.x / P.z
    let y1 := P.y / P.z
    let x2 := Q.x / Q.z
    let y2 := Q.y / Q.z
    if x1 = x2 then
      if y1 = -y2 then E.Zero  -- P = -Q，结果为无穷远点
      else
        -- 倍点公式
        let slope := (3 * x1^2 + E.a) / (2 * y1)
        let x3 := slope^2 - 2 * x1
        let y3 := slope * (x1 - x3) - y1
        ⟨x3, y3, 1, Or.inr ⟨by simp, by field_simp; nlinarith⟩⟩
    else
      -- 普通加法公式
      let slope := (y2 - y1) / (x2 - x1)
      let x3 := slope^2 - x1 - x2
      let y3 := slope * (x1 - x3) - y1
      ⟨x3, y3, 1, Or.inr ⟨by simp, by field_simp; nlinarith⟩⟩

-- 点的取反
def EllipticCurve.Point.neg {K : Type u} [Field K] {E : EllipticCurve K} 
    (P : E.Point) : E.Point :=
  ⟨P.x, -P.y, P.z, by
    rcases P.eqn with h | h
    · -- 无穷远点
      rw [h]
      left
      rfl
    · -- 仿射点
      right
      constructor
      · exact h.1
      · -- y²z = x³ + axz² + bz³ 变为 (-y)²z = x³ + axz² + bz³
        nlinarith [h.2]
  ⟩

instance {K : Type u} [Field K] {E : EllipticCurve K} : Zero E.Point where
  zero := E.Zero

instance {K : Type u} [Field K] {E : EllipticCurve K} : Neg E.Point where
  neg P := P.neg

instance {K : Type u} [Field K] {E : EllipticCurve K} : Add E.Point where
  add P Q := P.add Q

instance {K : Type u} [Field K] {E : EllipticCurve K} : Sub E.Point where
  sub P Q := P + (-Q)

-- 椭圆曲线的群公理（框架表述）
theorem elliptic_curve_group_axioms {K : Type u} [Field K] (E : EllipticCurve K) :
    (∀ P : E.Point, 0 + P = P) ∧  -- 左单位元
    (∀ P : E.Point, P + 0 = P) ∧  -- 右单位元
    (∀ P : E.Point, P + (-P) = 0) ∧  -- 逆元
    (∀ P Q R : E.Point, (P + Q) + R = P + (Q + R)) := by
  constructor
  · -- 证明 0 + P = P
    intro P
    simp [Zero.zero, Add.add, EllipticCurve.Point.add]
  constructor
  · -- 证明 P + 0 = P
    intro P
    simp [Zero.zero, Add.add, EllipticCurve.Point.add]
  constructor
  · -- 证明 P + (-P) = 0
    intro P
    simp [Neg.neg, EllipticCurve.Point.neg, Add.add, EllipticCurve.Point.add, Zero.zero]
    split_ifs with h1 h2 h3
    · -- 无穷远点的情况
      rfl
    · -- 无穷远点的情况
      rfl
    · -- 一般情况：x坐标相同，y坐标相反
      simp [EllipticCurve.Zero]
    · -- 其他情况
      sorry -- 需要详细证明
  · -- 证明结合律 (P + Q) + R = P + (Q + R)
    intros P Q R
    -- 结合律的证明需要使用椭圆曲线的几何性质
    -- 这是Abel群结构的核心性质
    sorry -- 需要详细证明（这是复杂的代数计算）

-- 椭圆曲线构成Abel群（框架）
instance {K : Type u} [Field K] (E : EllipticCurve K) : AddCommGroup E.Point :=
  {
    zero := E.Zero
    add := EllipticCurve.Point.add
    neg := EllipticCurve.Point.neg
    zero_add := by
      intro P
      simp [Zero.zero, Add.add, EllipticCurve.Point.add]
    add_zero := by
      intro P
      simp [Zero.zero, Add.add, EllipticCurve.Point.add]
    neg_add_cancel := by
      intro P
      simp [Neg.neg, EllipticCurve.Point.neg, Add.add, EllipticCurve.Point.add]
      sorry -- 需要详细证明
    add_assoc := by
      intros P Q R
      sorry -- 需要详细证明
    add_comm := by
      intros P Q
      simp [Add.add, EllipticCurve.Point.add]
      sorry -- 需要详细证明
    nsmul := nsmulRec
    zsmul := zsmulRec
  }

/-! 
## 高度理论 (Height Theory)

高度函数是证明莫德尔-韦伊定理的核心工具，度量点的算术复杂性。

**Weil高度**：对于P = [x₀:x₁:...:xₙ] ∈ ℙⁿ(ℚ)，
h(P) = Σ_v log max_i |x_i|_v

**规范高度**（Néron-Tate）：
ĥ(P) = lim_{n→∞} h(2ⁿP) / 4ⁿ

规范高度是二次型，满足ĥ(nP) = n²ĥ(P)。
-/

-- Weil高度（简化定义）
def WeilHeight {K : Type u} [NumberField K] (α : K) : ℝ :=
  -- h(α) = (1/[K:ℚ]) Σ_v n_v log max(1, |α|_v)
  -- 简化：仅考虑绝对值的对数
  if α = 0 then 0
  else Real.log (max 1 ‖α‖)
  where
    -- 范数的占位符定义
    ‖α‖ : ℝ := 1  -- 需要实际的范数定义

-- 射影空间的Weil高度
def ProjectiveWeilHeight {K : Type u} [NumberField K] {n : ℕ}
    (P : Fin (n+1) → K) : ℝ :=
  -- h(P) = Σ_v log max_i |x_i|_v
  -- 简化定义
  if ∃ i, P i ≠ 0 then
    let max_val := Finset.sup (Finset.univ) (fun i => ‖P i‖)
    Real.log max_val
  else 0

-- 椭圆曲线上的Weil高度
def EllipticCurve.WeilHeight {K : Type u} [NumberField K] {E : EllipticCurve K}
    (P : E.Point) : ℝ :=
  -- 使用x坐标的Weil高度
  if P.z = 0 then 0  -- 无穷远点高度为0
  else WeilHeight (P.x / P.z)

-- 规范高度（Néron-Tate高度）
def CanonicalHeight {K : Type u} [NumberField K] {E : EllipticCurve K}
    (P : E.Point) : ℝ :=
  -- ĥ(P) = lim_{n→∞} h(2ⁿP) / 4ⁿ
  -- 这是一个极限定义，在实际计算中使用其他方法
  if P = 0 then 0
  else
    -- 简化：使用Weil高度作为近似
    E.WeilHeight P

-- 规范高度的性质（框架表述）
theorem canonical_height_properties {K : Type u} [NumberField K] {E : EllipticCurve K}
    (P Q : E.Point) (m : ℤ) :
    -- 二次性
    CanonicalHeight (m • P) = m^2 * CanonicalHeight P ∧
    -- 抛物性
    CanonicalHeight (P + Q) + CanonicalHeight (P - Q) = 
      2 * (CanonicalHeight P + CanonicalHeight Q) := by
  constructor
  · -- 证明 ĥ(mP) = m²ĥ(P)
    -- 这是规范高度的核心性质
    simp [CanonicalHeight]
    sorry -- 需要详细证明
  · -- 证明抛物性
    simp [CanonicalHeight]
    sorry -- 需要详细证明

-- 规范高度为零当且仅当点是挠点
theorem canonical_height_zero_iff_torsion {K : Type u} [NumberField K] 
    {E : EllipticCurve K} (P : E.Point) :
    CanonicalHeight P = 0 ↔ ∃ n > 0, n • P = 0 := by
  constructor
  · -- 若 ĥ(P) = 0，则 P 是挠点
    intro h
    -- 使用Kronecker定理：高度为0的点是单位根
    sorry -- 需要详细证明
  · -- 若 P 是挠点，则 ĥ(P) = 0
    rintro ⟨n, hn_pos, hn_eq⟩
    -- 利用规范高度的二次性
    have h1 : CanonicalHeight (n • P) = n^2 * CanonicalHeight P := by
      sorry -- 应用规范高度的性质
    rw [hn_eq] at h1
    simp at h1
    -- n² ≠ 0，所以 ĥ(P) = 0
    have h2 : (n : ℝ) ^ 2 > 0 := by
      exact pow_pos (by exact_mod_cast hn_pos) 2
    have h3 : CanonicalHeight P = 0 := by
      nlinarith
    exact h3

/-! 
## 弱莫德尔-韦伊定理

**定理**：对于n ≥ 2，E(K)/nE(K)是有限的。

**证明思路**（使用下降法）：
1. 构造Kummer配对：E(K)/nE(K) × G_K → E[n]
2. 证明像落在Selmer群Sⁿ(E/K)中
3. 证明Selmer群有限
4. 通过正合序列得到结论

其中E[n] = {P ∈ E(K̄) : nP = 0}是n-挠子群。
-/

-- n-挠子群
def TorsionSubgroup {K : Type u} [Field K] {E : EllipticCurve K} (n : ℕ) : Set E.Point :=
  { P | n • P = 0 }

-- n-挠子群同构于(Z/nZ)²（当char(K)∤n时）（框架）
theorem torsion_subgroup_structure {K : Type u} [Field K] {E : EllipticCurve K}
    (n : ℕ) (h : ringChar K = 0 ∨ ¬(ringChar K ∣ n)) :
    TorsionSubgroup n ≃* (ZMod n) × (ZMod n) := by
  -- 这是椭圆曲线理论的标准结果
  -- E[n] ≅ (ℤ/nℤ)² 当 char(K) ∤ n
  sorry -- 需要详细证明

-- Selmer群（简化定义）
def SelmerGroup {K : Type u} [NumberField K] {E : EllipticCurve K} (n : ℕ) : Type _ :=
  -- Sⁿ(E/K) ⊂ H¹(K, E[n])，在每个位上局部平凡
  -- 简化：定义为有限集合的子集
  {s : Finset K // s.Nonempty}

-- Selmer群是有限集（框架）
instance {K : Type u} [NumberField K] {E : EllipticCurve K} {n : ℕ} : 
    Fintype (SelmerGroup n) :=
  ⟨{⟨{0}, by simp⟩}, by
    intro s
    sorry -- 需要证明所有Selmer群元素都是这个
  ⟩

-- 弱莫德尔-韦伊定理（框架表述）
theorem weak_mordell_weil {K : Type u} [NumberField K] {E : EllipticCurve K}
    (n : ℕ) (hn : n ≥ 2) :
    Finite (E.Point ⧸ (λ (P : E.Point) => n • P)).range := by
  -- 证明依赖于：
  -- 1. Selmer群的有限性
  -- 2. Tate-Shafarevich群的性质
  -- 3. Kummer序列
  -- 简化：断言有限性
  sorry -- 完整证明需要大量的代数几何工具

/-! 
## 下降法 (Descent)

从弱莫德尔-韦伊定理推导完整定理的核心工具是下降法，
它利用高度函数将有限生成性从E(K)/nE(K)提升到E(K)。

**关键步骤**：
1. 选择有限代表系{Q₁,...,Q_m} ⊂ E(K)使得E(K) = ∪(Q_i + nE(K))
2. 证明：若P ∈ E(K)，则存在P'满足nP' = P - Q_i且h(P') < h(P) - C
3. 通过迭代找到有限生成集
-/

-- 下降引理（框架表述）
theorem descent_lemma {K : Type u} [NumberField K] {E : EllipticCurve K}
    (n : ℕ) (hn : n ≥ 2) :
    ∃ (Q : Finset E.Point),
      ∀ P : E.Point, 
        P ∈ ⋃ q ∈ Q, { n • P' + q | P' : E.Point } := by
  -- 利用弱莫德尔-韦伊定理
  -- E(K)/nE(K)有限意味着存在有限代表系
  sorry -- 需要详细证明

-- 高度下降估计（框架表述）
theorem height_descent_estimate {K : Type u} [NumberField K] {E : EllipticCurve K}
    (n : ℕ) (hn : n ≥ 2) :
    ∃ C > 0, ∀ P : E.Point, ∃ P' : E.Point, 
      n • P' = P ∨ 
      (WeilHeight P' < WeilHeight P - C ∧ 
       ∃ i ∈ Finset.range n, n • P' = P - ⟨0, 0, 0, by simp⟩) := by
  -- 利用规范高度的二次性质
  -- ĥ(nP) = n²ĥ(P)
  sorry -- 需要详细证明

/-! 
## 莫德尔-韦伊定理

**完整定理**：设E是定义在数域K上的椭圆曲线，
则E(K)是有限生成Abel群。

即存在整数r ≥ 0和有限挠子群E(K)_tors使得：
E(K) ≅ ℤ^r × E(K)_tors

**证明概要**：
1. 证明弱莫德尔-韦伊：E(K)/nE(K)有限
2. 应用下降法得到有限生成性
3. 挠子群有限由Mazur定理（K=ℚ）或一般理论保证
-/

-- 挠子群的结构
def TorsionSubgroupFull {K : Type u} [Field K] {E : EllipticCurve K} : 
    AddSubgroup E.Point :=
  { carrier := { P | ∃ n > 0, n • P = 0 },
    zero_mem' := ⟨1, by norm_num, by simp⟩,
    add_mem' := by
      intro P Q hP hQ
      rcases hP with ⟨n, hn_pos, hn_eq⟩
      rcases hQ with ⟨m, hm_pos, hm_eq⟩
      use n * m
      constructor
      · -- n*m > 0
        exact mul_pos hn_pos hm_pos
      · -- (n*m)(P+Q) = 0
        have h1 : (n * m : ℕ) • (P + Q) = (n * m : ℕ) • P + (n * m : ℕ) • Q := by
          apply zsmul_add
        rw [h1]
        have h2 : (n * m : ℕ) • P = 0 := by
          rw [show (n * m : ℕ) = m * n by ring]
          rw [mul_zsmul, hn_eq]
          simp
        have h3 : (n * m : ℕ) • Q = 0 := by
          rw [mul_comm]
          rw [mul_zsmul, hm_eq]
          simp
        rw [h2, h3]
        simp,
    neg_mem' := by
      intro P hP
      rcases hP with ⟨n, hn_pos, hn_eq⟩
      use n
      constructor
      · exact hn_pos
      · -- n(-P) = -(nP) = 0
        rw [zsmul_neg]
        rw [hn_eq]
        simp }

-- 挠子群有限（框架表述）
theorem torsion_subgroup_finite {K : Type u} [NumberField K] {E : EllipticCurve K} :
    (TorsionSubgroupFull : Set E.Point).Finite := by
  -- 利用约化理论和素理想性质
  -- 这是Nagell-Lutz定理和约化理论的结果
  sorry -- 需要详细证明

-- 莫德尔-韦伊定理的主表述（框架）
theorem mordell_weil_theorem {K : Type u} [NumberField K] {E : EllipticCurve K} :
    -- E(K)是有限生成Abel群
    ∃ (r : ℕ) (basis : Fin r → E.Point) (tors : Finset E.Point),
      (∀ P : E.Point, ∃! (n : Fin r → ℤ) (t ∈ tors), 
        P = ∑ i, n i • basis i + t) := by
  -- 完整证明：
  -- 1. 弱莫德尔-韦伊定理
  -- 2. 下降法
  -- 3. 挠子群有限性
  sorry -- 这是极其复杂的证明，需要大量准备

-- 秩的定义（Mordell-Weil群的自由秩）
def Rank {K : Type u} [NumberField K] (E : EllipticCurve K) : ℕ :=
  -- 使得E(K) ≅ ℤ^r × E(K)_tors的整数r
  -- 简化：使用挠子群的指数定义
  sorry -- 需要定义

-- 秩的等价刻画（框架）
theorem rank_characterization {K : Type u} [NumberField K] {E : EllipticCurve K} :
    Rank E = 
      FiniteDimensional.finrank ℝ 
        (Submodule.span ℝ (Set.range (CanonicalHeight : E.Point → ℝ))) := by
  -- 这是规范高度与秩的关系
  sorry -- 需要详细证明

/-! 
## Mazur挠定理（K = ℚ的情形）

当K = ℚ时，挠子群的结构被Mazur完全确定：

**定理（Mazur, 1977）**：E(ℚ)_tors同构于以下15个群之一：
- ℤ/nℤ，其中n = 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12
- ℤ/2ℤ × ℤ/2nℤ，其中n = 1, 2, 3, 4

这是椭圆曲线算术理论中最深刻的结果之一。
-/

-- Mazur定理可能的挠群结构
inductive MazurTorsionGroup
  | cyclic (n : ℕ)  -- ℤ/nℤ
  | product2 (n : ℕ)  -- ℤ/2ℤ × ℤ/2nℤ

-- Mazur定理（框架表述）
theorem mazur_torsion_theorem {E : EllipticCurve ℚ} :
    ∃ g : MazurTorsionGroup,
      (g = MazurTorsionGroup.cyclic 1 ∨
       g = MazurTorsionGroup.cyclic 2 ∨
       g = MazurTorsionGroup.cyclic 3 ∨
       g = MazurTorsionGroup.cyclic 4 ∨
       g = MazurTorsionGroup.cyclic 5 ∨
       g = MazurTorsionGroup.cyclic 6 ∨
       g = MazurTorsionGroup.cyclic 7 ∨
       g = MazurTorsionGroup.cyclic 8 ∨
       g = MazurTorsionGroup.cyclic 9 ∨
       g = MazurTorsionGroup.cyclic 10 ∨
       g = MazurTorsionGroup.cyclic 12 ∨
       g = MazurTorsionGroup.product2 1 ∨
       g = MazurTorsionGroup.product2 2 ∨
       g = MazurTorsionGroup.product2 3 ∨
       g = MazurTorsionGroup.product2 4) := by
  -- Mazur通过深刻的模曲线理论证明
  -- 使用了Kamienny、Kenku等人的工作
  sorry -- 这是极其复杂的定理

/-! 
## 计算方法与应用

### 计算秩的方法
1. **2-下降法**：计算E(K)/2E(K)的结构
2. **Heegner点**：构造高阶点
3. **BSD猜想**：L(E,1)与秩的联系

### 应用
1. **同余数问题**：判断一个数是否为同余数
2. **Diophantine方程**：如x⁴ + y⁴ = z²的整数解
3. **密码学**：椭圆曲线密码体系（ECC）
4. **费马大定理**：Wiles证明的核心
-/

-- 2-下降法计算秩（框架）
def ComputeRankBy2Descent {K : Type u} [NumberField K] (E : EllipticCurve K) : ℕ :=
  -- 计算dim_{𝔽₂} Sel₂(E/K) - dim_{𝔽₂} Ш(E/K)[2]
  sorry -- 需要定义

-- Heegner点构造（框架）
def HeegnerPoint {E : EllipticCurve ℚ} (D : ℤ) (hD : D < 0) : E.Point :=
  -- 利用虚二次域的类域论构造点
  sorry -- 需要定义

-- Gross-Zagier公式（框架）
theorem gross_zagier_formula {E : EllipticCurve ℚ} (D : ℤ) (hD : D < 0) :
    -- 连接L'(E,1)和规范高度
    CanonicalHeight (HeegnerPoint D hD) > 0 ↔ Rank E > 0 := by
  -- Gross-Zagier (1986)
  sorry -- 需要详细证明

/-! 
## 推广到Abel簇

Weil将莫德尔定理推广到任意Abel簇：

**定理**：设A是定义在数域K上的Abel簇，则A(K)是有限生成Abel群。

证明使用相同的策略：弱定理+下降法+高度理论。
-/

-- Abel簇的莫德尔-韦伊定理（框架）
theorem mordell_weil_abelian_variety {K : Type u} [NumberField K] 
    (A : Type v) [AddCommGroup A] [Module ℚ A] :  -- Abel簇结构
    -- A(K)是有限生成Abel群
    ∃ (r : ℕ) (basis : Fin r → A) (tors : Finset A),
      (∀ x : A, ∃! (n : Fin r → ℤ) (t ∈ tors), 
        x = ∑ i, n i • basis i + t) := by
  -- Weil的推广证明
  sorry -- 极其复杂的证明

/-! 
## 总结

莫德尔-韦伊定理是椭圆曲线算术理论的基石：

1. **结构定理**：E(K) ≅ ℤ^r × E(K)_tors
2. **证明方法**：弱定理 + 下降法 + 高度理论
3. **计算问题**：秩的计算仍具挑战性（BSD猜想）
4. **几何意义**：连接代数几何与数论

这个定理展示了Diophantine几何的强大方法，
为后续的算术几何发展奠定了基础。
-/

end MordellWeil
