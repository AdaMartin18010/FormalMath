---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 极分解 (Polar Decomposition)
---
# 极分解 (Polar Decomposition)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.PolarDecomposition

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- 极分解：任意复方阵可唯一分解为酉矩阵与正定Hermite矩阵的乘积 -/
theorem polar_decomposition (A : Matrix n n 𝕜) :
    ∃! (U : Matrix n n 𝕜) (P : Matrix n n 𝕜),
      U.unitary ∧ P.positiveSemidefiniteHermitian ∧ A = U * P := by
  -- 利用 A*A 的谱分解构造 P = sqrt(A*A)，再定义 U = A P^{-1}
  sorry

end Matrix
```

## 数学背景

极分解是矩阵理论和泛函分析中的基本定理，它将任意复方阵唯一分解为一个酉矩阵（或正交矩阵）和一个半正定 Hermite 矩阵（或对称半正定矩阵）的乘积。这一定理可以看作复数极坐标形式 $z = re^{i\theta}$ 在矩阵上的推广：酉矩阵对应于旋转/反射（相位），半正定矩阵对应于伸缩（幅度）。

## 直观解释

极分解提供了一个优雅的几何视角来理解任意线性变换。任何一个线性变换都可以看作是先在一个标准方向上对各轴进行非负伸缩（半正定矩阵 $P$），然后再进行一个保持长度和角度的刚体旋转或反射（酉矩阵 $U$）。这与复数的极坐标 $z = re^{i\theta}$ 完全类似：$P$ 就像半径 $r$（在各个方向上可能有不同的伸缩系数），$U$ 就像单位复数 $e^{i\theta}$（旋转）。

## 形式化表述

设 $A$ 是一个 $n \times n$ 复方阵，则存在唯一的极分解：

$$A = UP$$

其中：

- $U$ 是 $n \times n$ 酉矩阵，满足 $U^* U = I$
- $P$ 是 $n \times n$ 半正定 Hermite 矩阵，$P = \sqrt{A^* A}$

若 $A$ 可逆，则 $U = A P^{-1}$ 也是唯一的。

对称地，也存在右极分解 $A = P' U$，其中 $P' = \sqrt{A A^*}$。

在实数情形下，$U$ 是正交矩阵，$P$ 是对称半正定矩阵。

其中：

- $A^*$ 表示 $A$ 的共轭转置
- $\sqrt{A^* A}$ 表示矩阵 $A^* A$ 的唯一半正定平方根

## 证明思路

1. **构造 P**：定义 $P = \sqrt{A^* A}$，其中 $A^* A$ 是半正定 Hermite 矩阵，存在唯一的半正定平方根
2. **验证范数**：$||Pv|| = ||Av||$ 对所有 $v$ 成立，说明 $P$ 和 $A$ 有相同的零空间结构
3. **定义 U**：在 $\text{Im}(P)$ 上定义 $U(Pv) = Av$，在 $\ker(P)$ 上任意延拓为酉映射
4. **唯一性**：若 $A = U_1 P_1 = U_2 P_2$，则 $P_1^2 = A^* A = P_2^2$，由半正定平方根的唯一性得 $P_1 = P_2$，进而 $U_1 = U_2$

核心洞察在于 $A^* A$ 的谱分解提供了变换的伸缩幅度信息。

## 示例

### 示例 1：2x2 实矩阵

设 $A = \begin{pmatrix} 1 & 2 \ 3 & 4 \end{pmatrix}$。
$A^T A = \begin{pmatrix} 10 & 14 \ 14 & 20 \end{pmatrix}$，特征值为 $15 \pm \sqrt{221}$。
$P = \sqrt{A^T A}$ 是正定的，$U = A P^{-1}$ 是正交矩阵。验证 $UP = A$。

### 示例 2：量子力学中的密度矩阵

在量子态的算符表示中，任意算符可以分解为酉演化（$U$）和测量/衰减（$P$）的乘积。极分解在研究开放量子系统和量子信道时具有基本重要性。

### 示例 3：弹性力学

在连续介质力学中，变形梯度张量 $F$ 的极分解 $F = RU = VR$ 将变形分解为纯旋转 $R$ 和纯拉伸 $U, V$。这是分析材料应力-应变关系的基础。

## 应用

- **量子力学**：量子态变换的酉部分和衰减部分的分解
- **弹性力学**：变形梯度张量的旋转-拉伸分解
- **信号处理**：协方差矩阵和滤波器设计的结构分析
- **数值分析**：矩阵条件和摄动分析
- **算子理论**：Hilbert 空间上有界算子的标准分解

## 相关概念

- 酉矩阵 (Unitary Matrix)：保持内积不变的复方阵
- Hermite 矩阵 (Hermitian Matrix)：满足 $A = A^*$ 的复方阵
- 半正定矩阵 (Positive Semidefinite Matrix)：所有特征值非负的 Hermite 矩阵
- 谱定理 (Spectral Theorem)：Hermite 矩阵可对角化的基本定理
- 奇异值分解 (SVD)：与极分解密切相关的矩阵分解

## 参考

### 教材

- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 7]
- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 30]

### 在线资源

- [Mathlib4 - Matrix Polar Decomposition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PolarDecomposition.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*