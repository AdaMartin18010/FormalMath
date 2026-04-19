---
title: "复向量空间与 Hermitian 矩阵"
level: "silver"
msc_primary: 15

  - 15A57
target_courses:
  - "MIT 18.06"
references:
  textbooks:
    - title: "Introduction to Linear Algebra"
      author: "Gilbert Strang"
      edition: "4th"
      chapters: "Ch.10"
      pages: "485-510"
review_status: "draft"
---

# 复向量空间与 Hermitian 矩阵

> **对应课程**：MIT 18.06 Linear Algebra, Spring 2010 — Lecture 32–33
> **核心目标**：建立复内积空间的理论，证明 Hermitian 矩阵特征值为实数、可酉对角化，并给出完整自然语言证明。

---

## 1. 复向量空间与内积

### 1.1 复向量空间

**定义 1.1** (复向量空间)
复向量空间 $V$ 是在复数域 $\mathbb{C}$ 上的向量空间，满足向量加法和标量乘法的八条公理。

对 $z \in \mathbb{C}$，其**复共轭**记为 $\bar{z}$，**模**为 $|z| = \sqrt{z \bar{z}}$。

### 1.2 Hermitian 内积

**定义 1.2** (Hermitian 内积)
复向量空间 $V$ 上的**内积**是一个映射 $\langle \cdot, \cdot \rangle: V \times V \to \mathbb{C}$，满足：

1. **共轭对称性**：$\langle u, v \rangle = \overline{\langle v, u \rangle}$
2. **对第一变元的线性性**：$\langle c u + v, w \rangle = c \langle u, w \rangle + \langle v, w \rangle$
3. **正定性**：$\langle v, v \rangle \geq 0$，且 $\langle v, v \rangle = 0 \Leftrightarrow v = 0$

由共轭对称性，内积对第二变元是**共轭线性**的：

$$
\langle u, c v + w \rangle = \bar{c} \langle u, v \rangle + \langle u, w \rangle
$$

在 $\mathbb{C}^n$ 上的标准 Hermitian 内积为：

$$
\langle u, v \rangle = \sum_{i=1}^n u_i \overline{v_i} = v^H u
$$

其中 $v^H = \bar{v}^T$ 称为 $v$ 的**共轭转置** (Hermitian transpose)。

---

## 2. Hermitian 矩阵

### 2.1 定义

**定义 2.1** (Hermitian 矩阵)
方阵 $A \in \mathbb{C}^{n \times n}$ 称为**Hermitian 矩阵**，若

$$
A = A^H
$$

即 $a_{ij} = \overline{a_{ji}}$ 对所有 $i, j$ 成立。当 $A$ 为实矩阵时，Hermitian 矩阵就是**对称矩阵**。

### 2.2 Hermitian 矩阵的特征值为实数

**定理 2.1** (Hermitian 矩阵的特征值为实数)
设 $A$ 是 Hermitian 矩阵，$\lambda$ 是 $A$ 的特征值，$x \neq 0$ 是对应特征向量。则 $\lambda \in \mathbb{R}$。

**证明**：

由 $A x = \lambda x$，考虑内积 $\langle A x, x \rangle$：

$$
\langle A x, x \rangle = \langle \lambda x, x \rangle = \lambda \langle x, x \rangle = \lambda \|x\|^2
$$

另一方面，由 $A = A^H$：

$$
\langle A x, x \rangle = x^H A x = x^H A^H x = (A x)^H x = \langle x, A x \rangle = \overline{\langle A x, x \rangle}
$$

因此 $\langle A x, x \rangle$ 是实数。由于 $\|x\|^2 > 0$，得 $\lambda = \frac{\langle A x, x \rangle}{\|x\|^2} \in \mathbb{R}$。$\square$

### 2.3 不同特征值对应的特征向量正交

**定理 2.2** (Hermitian 矩阵特征向量的正交性)
设 $A$ 是 Hermitian 矩阵，$\lambda_1 \neq \lambda_2$ 是两个不同特征值，$x_1, x_2$ 是对应特征向量。则 $x_1 \perp x_2$（即 $\langle x_1, x_2 \rangle = 0$）。

**证明**：

$$
\lambda_1 \langle x_1, x_2 \rangle = \langle \lambda_1 x_1, x_2 \rangle = \langle A x_1, x_2 \rangle = x_1^H A^H x_2 = x_1^H A x_2 = \langle x_1, \lambda_2 x_2 \rangle = \bar{\lambda}_2 \langle x_1, x_2 \rangle
$$

由于 $\lambda_2 \in \mathbb{R}$（**定理 2.1**），$\bar{\lambda}_2 = \lambda_2$。因此

$$
\lambda_1 \langle x_1, x_2 \rangle = \lambda_2 \langle x_1, x_2 \rangle
$$

即 $(\lambda_1 - \lambda_2) \langle x_1, x_2 \rangle = 0$。由于 $\lambda_1 \neq \lambda_2$，得 $\langle x_1, x_2 \rangle = 0$。$\square$

---

## 3. 酉矩阵与酉对角化

### 3.1 酉矩阵

**定义 3.1** (酉矩阵)
方阵 $U \in \mathbb{C}^{n \times n}$ 称为**酉矩阵** (unitary matrix)，若

$$
U^H U = U U^H = I
$$

即 $U^{-1} = U^H$。实酉矩阵就是**正交矩阵**。

酉矩阵保持内积不变：$\langle U x, U y \rangle = \langle x, y \rangle$。

### 3.2 谱定理：Hermitian 矩阵可酉对角化

**定理 3.1** (谱定理 / Spectral Theorem for Hermitian Matrices)
设 $A \in \mathbb{C}^{n \times n}$ 是 Hermitian 矩阵。则存在酉矩阵 $U$ 和实对角矩阵 $\Lambda$，使得

$$
A = U \Lambda U^H
$$

其中 $\Lambda = \operatorname{diag}(\lambda_1, \ldots, \lambda_n)$，$\lambda_i \in \mathbb{R}$ 是 $A$ 的特征值，$U$ 的列是对应的标准正交特征向量。

**证明**（归纳法）：

**基例** ($n = 1$)：一阶 Hermitian 矩阵本身就是实数，$A = (1)(\lambda)(1)^H$，显然成立。

**归纳假设**：假设对 $n-1$ 阶 Hermitian 矩阵结论成立。

**归纳步骤**：设 $A$ 是 $n$ 阶 Hermitian 矩阵。由**定理 2.1**，$A$ 有实特征值 $\lambda_1$ 和单位特征向量 $u_1$（$\|u_1\| = 1$）。将 $u_1$ 扩充为 $\mathbb{C}^n$ 的标准正交基 $\{u_1, v_2, \ldots, v_n\}$，令酉矩阵 $V = [u_1 \mid v_2 \mid \cdots \mid v_n]$。则

$$
V^H A V = \begin{pmatrix} \lambda_1 & 0 \\ 0 & B \end{pmatrix}
$$

其中 $B$ 是 $(n-1) \times (n-1)$ 矩阵。由于 $(V^H A V)^H = V^H A^H V = V^H A V$，故 $B$ 也是 Hermitian 矩阵。

由归纳假设，存在 $(n-1) \times (n-1)$ 酉矩阵 $W$ 和实对角矩阵 $D$ 使得 $B = W D W^H$。令

$$
U = V \begin{pmatrix} 1 & 0 \\ 0 & W \end{pmatrix}
$$

则 $U$ 是酉矩阵（酉矩阵的乘积仍是酉矩阵），且

$$
U^H A U = \begin{pmatrix} 1 & 0 \\ 0 & W^H \end{pmatrix} V^H A V \begin{pmatrix} 1 & 0 \\ 0 & W \end{pmatrix} = \begin{pmatrix} \lambda_1 & 0 \\ 0 & D \end{pmatrix} = \Lambda
$$

因此 $A = U \Lambda U^H$。$\square$

---

## 4. 正规矩阵

**定义 4.1** (正规矩阵)
方阵 $A \in \mathbb{C}^{n \times n}$ 称为**正规矩阵** (normal matrix)，若

$$
A^H A = A A^H
$$

Hermitian 矩阵（$A^H = A$）、酉矩阵（$A^H = A^{-1}$）、斜 Hermitian 矩阵（$A^H = -A$）和对角矩阵都是正规矩阵。

**定理 4.1** (正规矩阵的谱定理)
矩阵 $A$ 可酉对角化当且仅当 $A$ 是正规矩阵。

**证明概要**：

**($\Rightarrow$)**：若 $A = U \Lambda U^H$，则 $A^H A = U \bar{\Lambda} \Lambda U^H = U \Lambda \bar{\Lambda} U^H = A A^H$。

**($\Leftarrow$)**：可用 Schur 分解 $A = U T U^H$（其中 $T$ 是上三角矩阵），然后由 $A^H A = A A^H$ 推出 $T^H T = T T^H$。对上三角矩阵，这迫使 $T$ 必须是对角矩阵。$\square$

---

## 5. Lean4 形式化嵌入

以下代码展示 Hermitian 矩阵特征值为实数、酉对角化的形式化声明。

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! MIT 18.06 L32-L33: 复向量空间与 Hermitian 矩阵
    对应文档：docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/11-复向量空间与Hermitian矩阵.md
-/ 

section HermitianMatrices

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

-- Hermitian 矩阵的定义
example (A : Matrix n n ℂ) : Prop := A.IsHermitian

-- Hermitian 矩阵的特征值为实数
theorem hermitian_eigenvalues_real (A : Matrix n n ℂ) (hA : A.IsHermitian) (λ : ℂ)
    (hλ : ∃ v : n → ℂ, v ≠ 0 ∧ A.mulVec v = λ • v) :
    λ.im = 0 := by
  -- 利用 ⟨Av, v⟩ = ⟨v, Av⟩ 和 λ 为实数
  sorry

-- 谱定理：Hermitian 矩阵可酉对角化
theorem spectral_theorem_hermitian
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (Λ : n → ℝ),
      Uᴴ * U = 1 ∧
      A = U * (diagonal (fun i => (Λ i : ℂ))) * Uᴴ := by
  -- Mathlib 中有完整的谱定理实现
  sorry

end HermitianMatrices
```

---

## 6. 习题与详细解答

### 习题 1

设 $A = \begin{pmatrix} 2 & i \\ -i & 3 \end{pmatrix}$。验证 $A$ 是 Hermitian 矩阵，并求其特征值和特征向量。

**解答**：

**Step 1**：验证 Hermitian。

$$
A^H = \begin{pmatrix} \overline{2} & \overline{-i} \\ \overline{i} & \overline{3} \end{pmatrix}^T = \begin{pmatrix} 2 & i \\ -i & 3 \end{pmatrix} = A
$$

故 $A$ 是 Hermitian 矩阵。

**Step 2**：求特征值。

$$
\det(A - \lambda I) = (2 - \lambda)(3 - \lambda) - (i)(-i) = \lambda^2 - 5\lambda + 6 - 1 = \lambda^2 - 5\lambda + 5
$$

特征值：$\lambda = \frac{5 \pm \sqrt{25 - 20}}{2} = \frac{5 \pm \sqrt{5}}{2}$。均为实数，符合**定理 2.1**。

**Step 3**：求特征向量。

对 $\lambda_1 = \frac{5 + \sqrt{5}}{2}$：

$$
A - \lambda_1 I = \begin{pmatrix} -\frac{1+\sqrt{5}}{2} & i \\ -i & \frac{1-\sqrt{5}}{2} \end{pmatrix}
$$

由第一行：$-\frac{1+\sqrt{5}}{2} x_1 + i x_2 = 0$，取 $x_1 = 2i$，$x_2 = 1 + \sqrt{5}$。特征向量 $v_1 = \begin{pmatrix} 2i \\ 1 + \sqrt{5} \end{pmatrix}$。

对 $\lambda_2 = \frac{5 - \sqrt{5}}{2}$，类似可得 $v_2 = \begin{pmatrix} 2i \\ 1 - \sqrt{5} \end{pmatrix}$。

验证正交性：

$$
v_1^H v_2 = (-2i)(2i) + (1+\sqrt{5})(1-\sqrt{5}) = 4 + (1 - 5) = 0
$$

特征向量正交。$\square$

---

### 习题 2

设 $U$ 是 $n \times n$ 酉矩阵。证明：

(a) $U$ 的列向量构成 $\mathbb{C}^n$ 的一组标准正交基；
(b) 对任意 $x \in \mathbb{C}^n$，$\|Ux\| = \|x\|$；
(c) 若 $\lambda$ 是 $U$ 的特征值，则 $|\lambda| = 1$。

**解答**：

**(a)** 设 $U = [u_1 \mid \cdots \mid u_n]$。由 $U^H U = I$，其第 $(i, j)$ 元为 $u_i^H u_j = \delta_{ij}$。这说明列向量两两正交且模为 1，即构成标准正交基。

**(b)** 

$$
\|Ux\|^2 = (Ux)^H (Ux) = x^H U^H U x = x^H x = \|x\|^2
$$

故 $\|Ux\| = \|x\|$。

**(c)** 设 $U v = \lambda v$，$v \neq 0$。由 (b)：

$$
\|v\| = \|Uv\| = \|\lambda v\| = |\lambda| \|v\|
$$

由于 $\|v\| > 0$，得 $|\lambda| = 1$。$\square$

---

### 习题 3

设 $A = \begin{pmatrix} 3 & 1+i \\ 1-i & 2 \end{pmatrix}$。

(a) 证明 $A$ 是 Hermitian 矩阵；
(b) 求酉矩阵 $U$ 和实对角矩阵 $\Lambda$ 使得 $A = U \Lambda U^H$。

**解答**：

**(a)** 

$$
A^H = \begin{pmatrix} \overline{3} & \overline{1-i} \\ \overline{1+i} & \overline{2} \end{pmatrix}^T = \begin{pmatrix} 3 & 1+i \\ 1-i & 2 \end{pmatrix} = A
$$

故 $A$ 是 Hermitian 矩阵。

**(b)** 特征多项式：

$$
\det(A - \lambda I) = (3 - \lambda)(2 - \lambda) - (1+i)(1-i) = \lambda^2 - 5\lambda + 6 - 2 = \lambda^2 - 5\lambda + 4 = (\lambda - 4)(\lambda - 1)
$$

特征值：$\lambda_1 = 4, \lambda_2 = 1$。

对 $\lambda_1 = 4$：

$$
A - 4I = \begin{pmatrix} -1 & 1+i \\ 1-i & -2 \end{pmatrix} \sim \begin{pmatrix} 1 & -(1+i) \\ 0 & 0 \end{pmatrix}
$$

取 $v_1 = \begin{pmatrix} 1+i \\ 1 \end{pmatrix}$，单位化得 $u_1 = \frac{1}{\sqrt{3}} \begin{pmatrix} 1+i \\ 1 \end{pmatrix}$。

对 $\lambda_2 = 1$：

$$
A - I = \begin{pmatrix} 2 & 1+i \\ 1-i & 1 \end{pmatrix} \sim \begin{pmatrix} 2 & 1+i \\ 0 & 0 \end{pmatrix}
$$

取 $v_2 = \begin{pmatrix} -(1+i)/2 \\ 1 \end{pmatrix} = \begin{pmatrix} -1-i \\ 2 \end{pmatrix}$（放大 2 倍），单位化得 $u_2 = \frac{1}{\sqrt{6}} \begin{pmatrix} -1-i \\ 2 \end{pmatrix}$。

验证正交性：$u_1^H u_2 = \frac{1}{\sqrt{18}}((1-i)(-1-i) + 1 \cdot 2) = \frac{1}{\sqrt{18}}(-2 + 2) = 0$。

因此

$$
U = \begin{pmatrix} \frac{1+i}{\sqrt{3}} & \frac{-1-i}{\sqrt{6}} \\ \frac{1}{\sqrt{3}} & \frac{2}{\sqrt{6}} \end{pmatrix}, \quad \Lambda = \begin{pmatrix} 4 & 0 \\ 0 & 1 \end{pmatrix}
$$

$\square$

---

## 7. 常见错误模式分析 (L6)

### 7.1 概念混淆：Hermitian vs 对称

**错误**：认为"Hermitian 矩阵就是复对称矩阵"，即认为 $A = A^T$ 在复数域中已足够。

**纠正**：复对称矩阵满足 $A = A^T$，而 **Hermitian 矩阵要求 $A = A^H = \bar{A}^T$**。对复矩阵，转置不变性不足以保证特征值为实数。例如 $A = \begin{pmatrix} 1 & i \\ i & -1 \end{pmatrix}$ 是对称的（$A = A^T$），但不是 Hermitian 的，其特征值为 $0$（重根），且不可对角化。

### 7.2 计算陷阱：复内积中的共轭位置

**错误**：在复内积空间中计算正交性时，忘记对第二个向量取共轭，错误地写成 $\langle u, v \rangle = u^T v$。

**纠正**：标准 Hermitian 内积是 $\langle u, v \rangle = u^H v = \sum_i \overline{u_i} v_i$（或等价地 $v^H u$）。**共轭必须作用于第一个向量**。若写成 $\langle u, v \rangle = \sum_i u_i v_i$，则不满足正定性（例如对 $u = (1, i)^T$，$u^T u = 0$ 但 $u \neq 0$）。

### 7.3 直觉修正：酉矩阵的特征值"在复平面的单位圆上"

**错误**：将酉矩阵与 Hermitian 矩阵混为一谈，认为酉矩阵的特征值也必须是实数。

**纠正**：酉矩阵的特征值满足 $|\lambda| = 1$，但**不一定是实数**。例如旋转矩阵 $R = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ 是正交矩阵（特殊的酉矩阵），其特征值为 $\pm i$。Hermitian 矩阵的特征值才是实数。两者的共同点是都可以酉对角化，因为它们都是正规矩阵。
