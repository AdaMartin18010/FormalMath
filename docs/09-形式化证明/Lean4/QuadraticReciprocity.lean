/-
# 二次互反律的形式化证明 / Quadratic Reciprocity

## 领域
代数数论 (Algebraic Number Theory)

## Mathlib4对应
- **模块**: `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
- **核心定理**: `legendreSym.quadratic_reciprocity`
- **相关定义**:
  - `legendreSym`: 勒让德符号
  - `JacobiSym`: 雅可比符号
  - `ZMod`: 模 n 整数环

## MSC2020编码
- **Primary**: 11A15
- **Secondary**: 11R11

## 对齐课程
- MIT 18.781 (Theory of Numbers)
- Harvard Math 223a (Algebraic Number Theory)
- Princeton MAT 419 (Algebraic Number Theory)
- ETH 401-3052-05L (Algebraic Number Theory)

## 定理陈述
设 p, q 为不同的奇素数，则：
(p / q) · (q / p) = (-1)^((p-1)/2 · (q-1)/2)

其中 (p / q) 为勒让德符号。

## 数学意义
二次互反律是代数数论的奠基定理之一，揭示了不同奇素数之间二次剩余的深刻对称性。

## 历史背景
由高斯在1796年首次证明，收录于《算术研究》(Disquisitiones Arithmeticae, 1801)。
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

universe u

namespace QuadraticReciprocityTheorem

open Nat ZMod

/-
## 核心概念

### 勒让德符号 (Legendre Symbol)
对于奇素数 p 和整数 a，勒让德符号 (a / p) 定义为：
- 1  若 a 是模 p 的二次剩余且 p ∤ a
- -1 若 a 是模 p 的二次非剩余
- 0  若 p | a

### 二次剩余 (Quadratic Residue)
整数 a 称为模 p 的二次剩余，如果存在 x 使得 x² ≡ a (mod p)。
-/

-- 勒让德符号的定义（使用Mathlib4的实现）
def LegendreSymbol (a p : ℕ) [Fact p.Prime] : ℤ :=
  legendreSym p a

-- 勒让德符号的基本性质
theorem legendre_sym_mul (a b p : ℕ) [Fact p.Prime] :
    legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  /- 勒让德符号是完全积性的 -/
  rw [legendreSym.mul]

-- 欧拉判别法
theorem euler_criterion {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : ¬p ∣ a) :
    legendreSym p a ≡ a ^ ((p - 1) / 2) [ZMOD p] := by
  /- 使用Mathlib4的欧拉判别法 -/
  exact legendreSym.euler_criterion p ha

/-
## 二次互反律的主证明

**定理**: 设 p, q 为不同的奇素数，则
(p / q) · (q / p) = (-1)^((p-1)/2 · (q-1)/2)

**证明思路**（高斯的第六个证明）:
1. 利用高斯引理计算勒让德符号
2. 通过格点计数证明互反律
3. 关键步骤：考虑矩形 [0, p/2) × [0, q/2) 内的格点
-/

-- 二次互反律：核心定理
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  /- 使用Mathlib4的二次互反律 -/
  rw [legendreSym.quadratic_reciprocity']
  · rfl
  all_goals omega

-- 第一补充律：(-1 / p) = (-1)^((p-1)/2)
theorem first_supplemental_law {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1 : ℤ) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  /- 使用Mathlib4的第一补充律 -/
  rw [legendreSym.at_neg_one]
  all_goals omega

-- 第二补充律：(2 / p) = (-1)^((p²-1)/8)
theorem second_supplemental_law {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (2 : ℤ) = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  /- 使用Mathlib4的第二补充律 -/
  rw [legendreSym.at_two]
  all_goals omega

/-
## 应用：判断二次剩余

**例子**: 判断 3 是否是模 17 的二次剩余。

使用二次互反律：
(3 / 17) = (17 / 3) · (-1)^((3-1)/2 · (17-1)/2) = (17 / 3) · (-1)^8 = (17 / 3)

17 ≡ 2 (mod 3)，所以 (17 / 3) = (2 / 3) = -1。

因此 3 是模 17 的二次非剩余。
-/

-- 判断3是否为模17的二次剩余
example : legendreSym 17 (3 : ℤ) = -1 := by
  /- 使用二次互反律计算 -/
  rw [legendreSym.quadratic_reciprocity']
  all_goals norm_num

-- 判断5是否为模13的二次剩余
example : legendreSym 13 (5 : ℤ) = -1 := by
  /- 使用二次互反律计算 -/
  rw [legendreSym.quadratic_reciprocity']
  all_goals norm_num

/-
## 雅可比符号的推广

二次互反律可以推广到雅可比符号（合数模下的推广）。
-/

-- 雅可比符号的二次互反律
theorem jacobi_quadratic_reciprocity {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hab : a.Coprime b) :
    J(a | b) * J(b | a) = (-1 : ℤ) ^ (((a - 1) / 2) * ((b - 1) / 2)) := by
  /- 使用Mathlib4的雅可比符号二次互反律 -/
  rw [JacobiSym.quadratic_reciprocity']
  all_goals omega

end QuadraticReciprocityTheorem

/-
## 应用示例

### 计算勒让德符号

```lean
-- 计算 (7 / 19)
example : legendreSym 19 (7 : ℤ) = 1 := by
  rw [legendreSym.quadratic_reciprocity']
  all_goals norm_num
```

### 解二次同余

二次互反律可用于判断 x² ≡ a (mod p) 是否有解，从而辅助求解二次同余方程。

## 数学意义

二次互反律的重要性：

1. **结构对称性**：揭示了不同素数模下二次剩余之间的深刻对称关系
2. **计算工具**：提供了一种高效计算勒让德符号的递归算法
3. **高斯整数**：在高斯整数环 ℤ[i] 中可得到更简洁的解释
4. **类域论前奏**：是更一般的阿廷互反律的特例

## 历史发展

| 年份 | 数学家 | 贡献 |
|------|--------|------|
| 1796 | Gauss | 首次证明（19岁） |
| 1801 | Gauss | 《算术研究》发表 |
| 1808 | Gauss | 发表第三、第四个证明 |
| 1831 | Cauchy | 使用高斯整数的证明 |
| 现代 | Artin | 推广为阿廷互反律 |

## 与其他定理的关系

- **费马小定理**: 欧拉判别法的基础
- **高斯引理**: 证明二次互反律的关键工具
- **狄利克雷特征**: 与勒让德符号的解析理论相关

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`: 二次互反律的核心实现
- `legendreSym.quadratic_reciprocity`: 勒让德符号版本的二次互反律
- `JacobiSym.quadratic_reciprocity`: 雅可比符号版本的二次互反律
- `legendreSym.euler_criterion`: 欧拉判别法
- `legendreSym.at_neg_one`: 第一补充律
- `legendreSym.at_two`: 第二补充律
-/
