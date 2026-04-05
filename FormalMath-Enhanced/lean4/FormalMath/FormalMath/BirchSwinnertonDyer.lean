/-
# 伯奇-斯温纳顿-戴尔猜想 (Birch-Swinnerton-Dyer Conjecture)

## 数学背景

BSD猜想是椭圆曲线理论的核心猜想，
也是Clay数学研究所七大千禧年大奖问题之一。

### 问题陈述

对于有理数域上的椭圆曲线E/Q，
L函数L(E,s)在s=1处的零点阶等于E的有理点群E(Q)的秩。

即：ord_{s=1} L(E,s) = rank E(Q)

### 椭圆曲线基础

椭圆曲线E/Q由Weierstrass方程给出：
y² = x³ + ax + b，其中a, b ∈ Q，4a³ + 27b² ≠ 0

**群结构**: E(Q)是有限生成阿贝尔群：
E(Q) ≅ E(Q)_tors × ℤ^r

其中r = rank E(Q)是秩，E(Q)_tors是挠子群。

### L-函数

E的Hasse-Weil L-函数：
L(E,s) = ∏_p (1 - a_p p^{-s} + ε(p) p^{1-2s})^{-1}

其中：
- a_p = p + 1 - #E(F_p) （Frobenius迹）
- ε(p) = 0 若p | Δ（坏约化），否则为1

### 重要性
BSD猜想连接了：
- **解析对象**: L-函数的解析性质
- **算术对象**: 椭圆曲线的有理点
- **几何对象**: Tate-Shafarevich群、调节子、周期

### 已知结果
- Coates-Wiles (1977): 对于具有复乘的椭圆曲线，r=0 ⟹ L(1)≠0
- Gross-Zagier (1986): Heegner点与L-函数的导数
- Kolyvagin (1988): 使用Euler系统，对于rank 0,1的情况
- Bhargava-Shankar: 平均秩的有界性结果

## 参考
- Birch, B.J. & Swinnerton-Dyer, H.P.F. (1965). "Notes on elliptic curves. II"
- Silverman, J.H. "The Arithmetic of Elliptic Curves"
- Diamond & Shurman. "A First Course in Modular Forms"
- Washington, L.C. "Elliptic Curves: Number Theory and Cryptography"
- Rubin, K. "Euler Systems"
- Darmon, H. "Rational Points on Modular Elliptic Curves"

## 历史里程碑
- 1965: Birch和Swinnerton-Dyer提出猜想
- 1977: Coates-Wiles定理（复乘情形）
- 1977: Mazur挠子群分类
- 1983: Gross-Zagier公式
- 1988: Kolyvagin的Euler系统
- 1991: Rubin: 虚二次域上的BSD
- 2000: Conrad: Euler系统的系统发展
- 2011: Bhargava-Shankar关于平均秩的结果
- 2015: Bhargava-Skinner-Zhang: 大多数椭圆曲线满足BSD
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine

namespace BirchSwinnertonDyer

open Complex Real BigOperators Finset Classical

universe u

/-! 
## 椭圆曲线的基本定义

椭圆曲线是亏格1的光滑射影曲线，带有有理点。
-/ 

/-- 椭圆曲线的Weierstrass形式

椭圆曲线E/Q由方程给出：
y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆

或简化形式（特征≠2,3）：
y² = x³ + ax + b

**判别式条件**: Δ ≠ 0 确保曲线非奇异（光滑）。

**有理点**: E(Q) = {(x,y) ∈ Q² : y² = x³ + ax + b} ∪ {O}
其中O是无穷远点（群的单位元）。 -/
structure EllipticCurve where
  a4 : ℚ  -- x的系数
  a6 : ℚ  -- 常数项
  -- 假设特征≠2,3，使用简化形式y² = x³ + a₄x + a₆
  discriminant_ne_zero : 4 * a4^3 + 27 * a6^2 ≠ 0  -- 光滑性条件
deriving Repr

/-- 判别式 -/
def Discriminant (E : EllipticCurve) : ℚ :=
  4 * E.a4^3 + 27 * E.a6^2

/-- 椭圆曲线上的有理点群

E(Q)带有自然的阿贝尔群结构：
- 单位元：无穷远点O
- 逆元：-(x,y) = (x,-y)
- 加法：三点共线之和为零（P + Q + R = O若P,Q,R共线）

**Mordell定理**: E(Q)是有限生成阿贝尔群。
E(Q) ≅ E(Q)_tors × ℤ^r

其中r = rank E(Q)称为曲线的秩。 -/
def RationalPoints (E : EllipticCurve) : Type :=
  Option {p : ℚ × ℚ // p.2^2 = p.1^3 + E.a4 * p.1 + E.a6}

/-- 无穷远点 -/
def PointAtInfinity (E : EllipticCurve) : RationalPoints E :=
  none

/-- 有理点上的加法（弦切线法）-/
def addPoints (E : EllipticCurve) (P Q : RationalPoints E) : RationalPoints E :=
  match P, Q with
  | none, Q => Q  -- O + Q = Q
  | P, none => P  -- P + O = P
  | some P', some Q' =>
    let (x₁, y₁) := P'.val
    let (x₂, y₂) := Q'.val
    if x₁ = x₂ then
      if y₁ = -y₂ then
        none  -- P + (-P) = O
      else
        -- 倍点公式
        let m := (3 * x₁^2 + E.a4) / (2 * y₁)
        let x₃ := m^2 - 2 * x₁
        let y₃ := m * (x₁ - x₃) - y₁
        some ⟨(x₃, y₃), by
          -- 验证点在曲线上
          sorry⟩
    else
      -- 点加法公式
      let m := (y₂ - y₁) / (x₂ - x₁)
      let x₃ := m^2 - x₁ - x₂
      let y₃ := m * (x₁ - x₃) - y₁
      some ⟨(x₃, y₃), by
        -- 验证点在曲线上
        sorry⟩

/-- 有理点的逆元 -/
def negPoint (E : EllipticCurve) (P : RationalPoints E) : RationalPoints E :=
  match P with
  | none => none
  | some P' => some ⟨P'.val.1, -P'.val.2, by
    -- 验证点在曲线上
    sorry⟩

/-- E(Q)的阿贝尔群结构 -/
instance (E : EllipticCurve) : AddCommGroup (RationalPoints E) where
  add := addPoints E
  zero := PointAtInfinity E
  neg := negPoint E
  add_assoc := sorry  -- 验证结合律
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  neg_add_cancel := sorry

/-! 
## 椭圆曲线的秩与挠子群

秩是BSD猜想的核心对象。
-/ 

/-- 挠子群的定义 -/
def TorsionSubgroup (E : EllipticCurve) : Subgroup (RationalPoints E) where
  carrier := {p | ∃ n > 0, n • p = 0}
  one_mem' := ⟨1, by norm_num, by simp⟩
  mul_mem' := sorry
  inv_mem' := sorry

/-- Mazur挠子群分类定理 (1977)

E(Q)_tors的可能结构被完全分类：
- 循环群：ℤ/nℤ，其中n ∈ {1,2,3,4,5,6,7,8,9,10,12}
- 直和：ℤ/2ℤ × ℤ/2nℤ，其中n ∈ {1,2,3,4} -/
theorem mazur_torsion_theorem (E : EllipticCurve) :
    let T := TorsionSubgroup E
    (∃ n ∈ ({1,2,3,4,5,6,7,8,9,10,12} : Set ℕ), Nonempty (T ≃* Multiplicative (ZMod n))) ∨
    (∃ n ∈ ({1,2,3,4} : Set ℕ), Nonempty (T ≃* Multiplicative (ZMod 2 × ZMod (2*n)))) := by
  -- Mazur挠子群分类定理
  sorry

/-- 椭圆曲线的秩

rank E(Q) = E(Q) / E(Q)_tors 的自由秩

即E(Q)中无限阶独立点的最大个数。

**BSD猜想**: 秩等于L-函数在s=1处零点的阶。 -/
def Rank (E : EllipticCurve) : ℕ :=
  sorry  -- 需要有限生成阿贝尔群的秩

/-- Mordell定理：E(Q)是有限生成阿贝尔群 -/
theorem mordell_theorem (E : EllipticCurve) :
    AddGroup.FG (RationalPoints E) := by
  -- Mordell-Weil定理
  sorry

/-- 弱Mordell-Weil定理：E(Q)/nE(Q)有限 -/
theorem weak_mordell_weil (E : EllipticCurve) (n : ℕ) (hn : n > 0) :
    Fintype (RationalPoints E ⧸ (nsmul n ⊤)) :=
  sorry

/-! 
## L-函数与Hasse-Weil猜想

椭圆曲线的L-函数是BSD猜想的核心。
-/ 

/-- 坏素数的定义 -/
def badPrimes (E : EllipticCurve) : Finset ℕ :=
  {p : ℕ | Nat.Prime p ∧ p ∣ (4 * E.a4^3 + 27 * E.a6^2).natAbs}

/-- 有限域上椭圆曲线的点数 -/
def ellipticCurvePointCount (E : EllipticCurve) (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  -- 计算y² = x³ + a₄x + a₆在F_p上的解数
  sorry

/-- Frobenius迹 a_p = p + 1 - #E(F_p) -/
def FrobeniusTrace (E : EllipticCurve) (p : ℕ) (hp : Nat.Prime p) : ℤ :=
  let N_p := ellipticCurvePointCount E p hp
  p + 1 - N_p

/-- Hasse界 |a_p| ≤ 2√p -/
theorem hasse_bound (E : EllipticCurve) (p : ℕ) (hp : Nat.Prime p)
    (h_good : p ∉ badPrimes E) :
    |FrobeniusTrace E p hp| ≤ 2 * Real.sqrt p := by
  -- Hasse界
  sorry

/-- 椭圆曲线的L-函数

Hasse-Weil L-函数：
L(E,s) = ∏_p L_p(p^{-s})^{-1}

Euler因子：
- 好素数：L_p(T) = 1 - a_p T + p T²
- 坏素数：L_p(T) = 1 - a_p T（乘法约化）或1（加法约化）

**Hasse-Weil猜想**:
L(E,s)可解析延拓到全平面，满足函数方程。

这是Wiles证明的模性定理的推论。 -/
def EllipticCurveLFunction (E : EllipticCurve) (s : ℂ) : ℂ :=
  ∏ p in (Finset.Ico 2 (bound E s)), 
    let ap := FrobeniusTrace E p (sorry)
    let lp := if p ∈ badPrimes E then 1 - ap * (p : ℂ)^(-s) 
              else 1 - ap * (p : ℂ)^(-s) + p * (p : ℂ)^(-2*s)
    lp^(-1 : ℤ)
where
  bound (E : EllipticCurve) (s : ℂ) : ℕ := sorry  -- 截断参数

/-- 零点阶的定义 -/
def orderOfZero (f : ℂ → ℂ) (z₀ : ℂ) : ℕ :=
  -- 计算函数在z₀处零点的阶
  sorry

/-- 主导系数的定义 -/
def leadingCoefficient (f : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) : ℂ :=
  -- L(f,s)在s=z₀处n阶零点的主导系数
  sorry

/-- 权k的Eisenstein级数 -/
structure EisensteinSeries (k N : ℕ) where
  weight : k
  level : N
  -- 其他性质
  sorry

/-- 模形式的L-函数 -/
def ModularLFunction (f : EisensteinSeries 2 N) (s : ℂ) : ℂ :=
  sorry

/-- 模性定理 (Wiles, Taylor-Wiles, Breuil-Conrad-Diamond-Taylor)

每条有理椭圆曲线都是模的。

即存在权2的模形式f_E使得L(E,s) = L(f_E,s)。

**意义**:
- 证明了Fermat大定理
- 证明了L-函数的解析延拓和函数方程
- 提供了计算L-函数的有力工具
- 是BSD猜想的先决条件 -/
theorem modularity_theorem (E : EllipticCurve) :
    ∃ (N : ℕ) (f : EisensteinSeries 2 N), 
      EllipticCurveLFunction E s = ModularLFunction f s := by
  -- 模性定理
  sorry

/-- 导子（conductor）-/
def Conductor (E : EllipticCurve) : ℕ :=
  sorry

/-! 
## BSD猜想的主陈述

伯奇-斯温纳顿-戴尔猜想。
-/ 

/-- BSD猜想的主陈述

**弱BSD**: ord_{s=1} L(E,s) = rank E(Q)

**强BSD**: L*(E,1)的精确公式包含多个算术不变量。

**精确公式**（强BSD）：
lim_{s→1} L(E,s)/(s-1)^r = 
  (Ω_E · Reg_E · |Ш(E/Q)| · ∏_p c_p) / |E(Q)_tors|²

其中：
- Ω_E: 实周期
- Reg_E: 调节子（Néron-Tate高度配对的行列式）
- Ш(E/Q): Tate-Shafarevich群
- c_p: Tamagawa数
- E(Q)_tors: 挠子群 -/
structure BSDConjecture (E : EllipticCurve) : Prop where
  -- 零点阶等于秩
  order_of_vanishing : 
    orderOfZero (EllipticCurveLFunction E) 1 = Rank E
  -- 精确公式（强BSD）
  exact_formula : 
    let r := Rank E
    let leading_coeff := leadingCoefficient (EllipticCurveLFunction E) 1 r
    let Ω := RealPeriod E
    let Reg := Regulator E
    let Sha := TateShafarevichGroup E
    let Tamagawa := ∏ p in badPrimes E, TamagawaNumber E p
    let tors := Fintype.card (TorsionSubgroup E)
    leading_coeff = (Ω * Reg * Nat.card Sha * Tamagawa) / (tors ^ 2 : ℚ)

/-- BSD猜想的完整陈述 -/
def BSDConjectureFull : Prop :=
  ∀ (E : EllipticCurve), BSDConjecture E

/-! 
## BSD猜想中的关键不变量

强BSD公式中的各项。
-/ 

/-- 最大实根 -/
def greatestRealRoot (f : ℝ → ℝ) : ℝ :=
  sorry

/-- 实周期

Ω_E = ∫_{E(R)} |dx/y|

这是椭圆曲线实点上的不变微分的积分。

对于简化Weierstrass方程：
Ω_E = ∫_{α}^{∞} dx/√(x³ + ax + b)
其中α是x³ + ax + b的最大实根。 -/
def RealPeriod (E : EllipticCurve) : ℝ :=
  -- 计算实周期积分
  let α := greatestRealRoot (fun x ↦ x^3 + E.a4 * x + E.a6)
  ∫ x in Set.Ioi α, 1 / Real.sqrt (x^3 + E.a4 * x + E.a6)

/-- Néron-Tate高度

典范高度（canonical height）：
ĥ(P) = lim_{n→∞} h(2^n P) / 4^n

其中h是Weil高度。

**性质**:
- ĥ是E(Q) ⊗ ℝ上的正定二次型
- ĥ(P) = 0 ⟺ P是挠点
- 用于定义调节子

**高度配对**: ⟨P,Q⟩ = 1/2(ĥ(P+Q) - ĥ(P) - ĥ(Q)) -/
def CanonicalHeight (E : EllipticCurve) (P : RationalPoints E) : ℝ :=
  -- 定义典范高度
  sorry

/-- E(Q)的一组基 -/
def basisOfRationalPoints (E : EllipticCurve) (hr : Rank E > 0) : 
    Fin (Rank E) → RationalPoints E :=
  sorry

/-- 调节子

Reg_E = det(⟨P_i, P_j⟩)_{i,j=1..r}

其中P₁,...,P_r是E(Q)的一组基。

这是高度配对矩阵的行列式。

**意义**: 调节子度量了有理点群的"大小"，
类似于数域的调节子。 -/
def Regulator (E : EllipticCurve) : ℝ :=
  let r := Rank E
  if hr : r = 0 then 1
  else
    let basis := basisOfRationalPoints E (by omega)
    let height_matrix := Matrix.of (fun (i j : Fin r) ↦ 
      let Pi := basis i
      let Pj := basis j
      let heightSum := CanonicalHeight E (Pi + Pj)
      let heightPi := CanonicalHeight E Pi
      let heightPj := CanonicalHeight E Pj
      (heightSum - heightPi - heightPj) / 2)
    height_matrix.det

/-- Tate-Shafarevich群

Ш(E/Q) = ker(H¹(G_Q, E) → ∏_v H¹(G_{Q_v}, E))

这是BSD猜想中最神秘的群。

**性质**:
- 猜测是有限群（尚未证明）
- 若有限，其阶是平方数（Cassels-Tate配对）
- 度量了Hasse原则的失效
- 类似于数域的类群

**重要**: Ш的有限性是强BSD的一部分。 -/
def TateShafarevichGroup (E : EllipticCurve) : Type :=
  -- Galois上同调定义
  sorry

instance {E : EllipticCurve} : Fintype (TateShafarevichGroup E) :=
  sorry  -- 假设有限

/-- Tamagawa数

c_p = [E(Q_p) : E₀(Q_p)]

其中E₀(Q_p)是约化到非奇异点的点。

**意义**: 度量了p进局部点的行为。
对于好素数，c_p = 1。

**计算**: 可通过Kodaira类型显式计算。
- I_n类型（乘法约化）: c_p = n
- 加法约化: c_p ≤ 4 -/
def TamagawaNumber (E : EllipticCurve) (p : ℕ) : ℕ :=
  if p ∉ badPrimes E then 1
  else
    -- 计算Tamagawa数
    sorry

/-! 
## BSD猜想的已知结果

尽管BSD猜想尚未完全解决，有许多重要的部分结果。
-/ 

/-- 虚二次域 -/
structure ImaginaryQuadraticField where
  d : ℤ
  hd : d < 0 ∧ Squarefree d

/-- 复乘椭圆曲线 -/
class HasComplexMultiplication (E : EllipticCurve) : Prop where
  -- 具有复乘
  exists_cm_field : ∃ (K : ImaginaryQuadraticField), 
    sorry

/-- 自同态环 -/
def EndomorphismRing (E : EllipticCurve) : Type :=
  -- End(E)
  sorry

/-- Coates-Wiles定理 (1977)

对于具有复乘的椭圆曲线，
若rank E(Q) > 0，则L(E,1) = 0。

**逆否命题**: 若L(E,1) ≠ 0，则rank E(Q) = 0。

这是第一个重要的BSD结果。
**方法**: 使用类域理论和Iwasawa理论。

**限制**: 仅适用于具有复乘的曲线。 -/
theorem coates_wiles_theorem 
    (E : EllipticCurve) (h_cm : HasComplexMultiplication E) :
    Rank E > 0 → EllipticCurveLFunction E 1 = 0 := by
  -- Coates-Wiles定理
  sorry

/-- Heegner条件 -/
def HeegnerCondition (E : EllipticCurve) (K : ImaginaryQuadraticField) : Prop :=
  sorry

/-- Heegner点 -/
def HeegnerPoint (E : EllipticCurve) (K : ImaginaryQuadraticField) : 
    RationalPoints E :=
  sorry

/-- Gross-Zagier常数 -/
def GrossZagierConstant (E : EllipticCurve) (K : ImaginaryQuadraticField) : ℝ :=
  sorry

/-- Gross-Zagier公式 (1986)

对于秩为1的椭圆曲线，
L'(E,1)与Heegner点的高度相关。

**公式**: L'(E,1) = C · ĥ(P_K)

其中P_K是Heegner点。

**意义**: 这是BSD猜想的导数形式（rank = 1情形）。
建立了L-函数的导数与算术点高度的精确联系。 -/
theorem gross_zagier_formula 
    (E : EllipticCurve) (h_rank1 : Rank E = 1) (K : ImaginaryQuadraticField)
    (h_heegner : HeegnerCondition E K) :
    let P_K := HeegnerPoint E K
    let h := CanonicalHeight E P_K
    deriv (EllipticCurveLFunction E) 1 = GrossZagierConstant E K * h := by
  -- Gross-Zagier公式
  sorry

/-- Kolyvagin定理 (1988)

使用Euler系统，Kolyvagin证明了：

若L(E,1) ≠ 0，则rank E(Q) = 0且Ш有限。

若L'(E,1) ≠ 0且存在Heegner点条件，
则rank E(Q) = 1且Ш有限。

**方法**: Euler系统提供了控制Selmer群和上同调群的有力工具。

**重要性**: 这是对一般椭圆曲线的第一个BSD结果。
（不限制复乘条件） -/
theorem kolyvagin_theorem_rank0 
    (E : EllipticCurve) (h_L1 : EllipticCurveLFunction E 1 ≠ 0) :
    Rank E = 0 ∧ Finite (TateShafarevichGroup E) := by
  -- Kolyvagin定理（rank 0情形）
  sorry

theorem kolyvagin_theorem_rank1 
    (E : EllipticCurve) (K : ImaginaryQuadraticField)
    (h_L1 : EllipticCurveLFunction E 1 = 0)
    (h_L1' : deriv (EllipticCurveLFunction E) 1 ≠ 0)
    (h_heegner : HeegnerCondition E K) :
    Rank E = 1 ∧ Finite (TateShafarevichGroup E) := by
  -- Kolyvagin定理（rank 1情形）
  sorry

/-! 
## 平均结果与统计BSD

Bhargava等人的工作提供了关于BSD的统计理解。
-/ 

/-- 椭圆曲线的高度 -/
def Height (E : EllipticCurve) : ℝ :=
  max |E.a4.num| |E.a4.den| * max |E.a6.num| |E.a6.den|

/-- Bhargava-Shankar平均秩定理

当椭圆曲线按高度排序时，
平均秩是有界的（实际上趋近于1/2）。

**结果**: lim sup_{H→∞} (Σ_{H(E)≤H} rank E(Q)) / #{E : H(E)≤H} ≤ 0.5

**重要性**: 支持了rank通常很小的猜想。
大多数曲线的rank为0或1。

**方法**: 计算2-Selmer群的平均大小。 -/
theorem bhargava_shankar_average_rank :
    Tendsto (fun H ↦ 
      (∑ E in {E : EllipticCurve | Height E ≤ H}, Rank E) / 
      {E : EllipticCurve | Height E ≤ H}.ncard)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  -- Bhargava-Shankar平均秩定理
  sorry

/-- Selmer群 -/
def SelmerGroup (E : EllipticCurve) (n : ℕ) : Type :=
  sorry

/-- 2-Selmer秩与真实秩的关系 -/
theorem selmer_rank_bound (E : EllipticCurve) :
    Rank E ≤ Fintype.card (SelmerGroup E 2) :=
  sorry

/-! 
## 高维推广

BSD猜想可推广到Abel簇。
-/ 

/-- Abel簇的定义 -/
structure AbelVariety (K : Type u) [Field K] (g : ℕ) where
  carrier : Type u
  -- g维Abel簇
  [addCommGroup : AddCommGroup carrier]
  [projective : IsProjective carrier]
  dimension : g

/-- Abel簇的L-函数 -/
def AbelVarietyLFunction {g : ℕ} (A : AbelVariety ℚ g) (s : ℂ) : ℂ :=
  sorry

/-- Abel簇的秩 -/
def AbelVarietyRank {g : ℕ} (A : AbelVariety ℚ g) : ℕ :=
  sorry

/-- Abel簇上的BSD猜想 -/
structure BSDForAbelVariety {g : ℕ} (A : AbelVariety ℚ g) : Prop where
  order_equals_rank : sorry  -- 零点阶等于秩
  exact_formula : sorry  -- 类似公式

/-! 
## 总结

BSD猜想是算术几何的明珠。

**核心问题**: L-函数在s=1处的零点阶等于有理点群的秩。

**已知结果**:
- Rank 0情形（Kolyvagin）
- Rank 1情形（Gross-Zagier + Kolyvagin）
- 复乘情形（Coates-Wiles, Rubin）
- 平均结果（Bhargava-Shankar）

**主要开放问题**:
- 秩≥2的情形
- Tate-Shafarevich群的有限性
- 强BSD的精确公式
- 一般数域上的BSD

**研究工具**:
- Iwasawa理论
- Euler系统
- p进Hodge理论
- 自守形式

**这个问题的解决将**:
- 获得Clay数学研究所的百万美元奖金
- 深刻影响算术几何
- 推动L-函数理论的发展
- 连接算术、几何、分析
-/ 

/-- BSD猜想研究里程碑 -/
def BSDTimeline : List (ℕ × String) := [
  (1965, "Birch和Swinnerton-Dyer提出猜想"),
  (1977, "Coates-Wiles: 复乘情形，rank 0"),
  (1977, "Mazur: 挠子群分类"),
  (1983, "Gross-Zagier公式"),
  (1988, "Kolyvagin: Euler系统，rank 0,1"),
  (1991, "Rubin: 虚二次域上的BSD"),
  (2000, "Conrad: Euler系统的系统发展"),
  (2011, "Bhargava-Shankar: 平均秩结果"),
  (2015, "Bhargava-Skinner-Zhang: 大多数椭圆曲线满足BSD")
]

end BirchSwinnertonDyer
