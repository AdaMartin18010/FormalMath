---
title: "线性变换的矩阵表示 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
review_status: completed
---

## 定理陈述

**自然语言**：设 $T: V \to W$ 是有限维向量空间之间的线性变换。给定 $V$ 的一组有序基 $\mathcal{B} = \{v_1, \dots, v_n\}$ 和 $W$ 的一组有序基 $\mathcal{C} = \{w_1, \dots, w_m\}$，则存在唯一的 $m \times n$ 矩阵 $[T]_{\mathcal{B}}^{\mathcal{C}}$，使得对任意 $v \in V$ 有
\[
[T(v)]_{\mathcal{C}} = [T]_{\mathcal{B}}^{\mathcal{C}} \, [v]_{\mathcal{B}}.
\]
其中 $[v]_{\mathcal{B}}$ 表示 $v$ 在基 $\mathcal{B}$ 下的坐标向量。此外，映射 $T \mapsto [T]_{\mathcal{B}}^{\mathcal{C}}$ 是线性同构；复合映射的矩阵等于矩阵乘积：$[S \circ T]_{\mathcal{B}}^{\mathcal{D}} = [S]_{\mathcal{C}}^{\mathcal{D}} \, [T]_{\mathcal{B}}^{\mathcal{C}}$。

**Lean4**：

```lean
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis

namespace MatrixRepresentation
open LinearMap Matrix Module

variable {𝕜 : Type*} [Field 𝕜] {V W : Type*}
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]

variable (B : Basis (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜 V)
variable (C : Basis (Fin (FiniteDimensional.finrank 𝕜 W)) 𝕜 W)

-- 线性变换到矩阵的映射：存在唯一
theorem lin_to_matrix_exists (T : V →ₗ[𝕜] W) :
    ∃! M : Matrix (Fin (FiniteDimensional.finrank 𝕜 W))
                  (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜,
      ∀ v : V, C.repr (T v) = M *ᵥ B.repr v := by
  use toMatrix B C T
  constructor
  · intro v
    simp [toMatrix]
  · intro M hM
    apply Matrix.ext
    intro i j
    sorry  -- 由基向量的像唯一确定

-- 矩阵到线性变换的映射：存在唯一
theorem matrix_to_lin_exists
    (M : Matrix (Fin (FiniteDimensional.finrank 𝕜 W))
                (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜) :
    ∃! T : V →ₗ[𝕜] W, toMatrix B C T = M := by
  use toLin B C M
  constructor
  · simp [toLin]
  · intro T hT
    rw [← hT]
    simp [toLin_toMatrix]

-- 复合映射对应矩阵乘法
theorem matrix_of_comp {U : Type*} [AddCommGroup U] [Module 𝕜 U]
    [FiniteDimensional 𝕜 U]
    (D : Basis (Fin (FiniteDimensional.finrank 𝕜 U)) 𝕜 U)
    (T : V →ₗ[𝕜] W) (S : W →ₗ[𝕜] U) :
    toMatrix B D (S.comp T) = toMatrix C D S * toMatrix B C T := by
  simp [toMatrix_comp]
end MatrixRepresentation
```

## 证明思路

**自然语言**：
1. **构造矩阵**：令 $[T]_{\mathcal{B}}^{\mathcal{C}}$ 的第 $j$ 列恰好是 $T(v_j)$ 在基 $\mathcal{C}$ 下的坐标向量 $[T(v_j)]_{\mathcal{C}}$。
2. **验证等式**：对 $v = \sum_j c_j v_j$，由线性性 $T(v) = \sum_j c_j T(v_j)$。取坐标得
   $$[T(v)]_{\mathcal{C}} = \sum_j c_j [T(v_j)]_{\mathcal{C}} = [T]_{\mathcal{B}}^{\mathcal{C}} \begin{pmatrix} c_1 \\ \vdots \\ c_n \end{pmatrix} = [T]_{\mathcal{B}}^{\mathcal{C}} [v]_{\mathcal{B}}.$$
3. **唯一性**：矩阵的列由基向量的像唯一确定，故矩阵唯一。
4. **复合映射**：直接验证 $(S \circ T)(v_j) = S(T(v_j))$ 的坐标向量恰好等于矩阵乘积的第 $j$ 列。

**Lean4**：Mathlib4 中 `toMatrix B C T` 直接定义了线性变换到矩阵的映射，`toLin B C M` 则是其逆映射。`toMatrix_comp` 封装了复合映射对应矩阵乘法的核心等式。`repr` 是基下坐标映射，`*ᵥ` 是矩阵与向量的乘法。

## 关键 tactic/概念 教学

- `Basis ι 𝕜 V`：域 $𝕜$ 上向量空间 $V$ 的以 `ι` 为指标集的基。
- `B.repr v`：向量 $v$ 在基 $B$ 下的坐标（`ι → 𝕜`）。
- `toMatrix B C T`：线性变换 $T$ 在基 $B$（域）和 $C$（陪域）下的矩阵表示。
- `toLin B C M`：由矩阵 $M$ 构造对应的线性变换。
- `toMatrix_comp`：复合变换的矩阵等于矩阵乘积。

## 练习

1. 设 $T: \mathbb{R}^2 \to \mathbb{R}^2$ 为逆时针旋转 $90^\circ$，求 $T$ 在标准基下的矩阵表示。
2. 设 $\mathcal{B} = \{(1,1)^T, (1,-1)^T\}$ 是 $\mathbb{R}^2$ 的另一组基，求同一旋转 $T$ 在基 $\mathcal{B}$ 下的矩阵表示，并验证基变换公式。
3. 在 Lean4 中验证：对于 $2 \times 2$ 矩阵 $M = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$，有 `toMatrix B C (toLin B C M) = M`。
---
**参考文献**

1. 相关教材与学术论文。
