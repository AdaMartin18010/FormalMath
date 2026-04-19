---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 矩阵指数定理 (Matrix Exponential)
---
# 矩阵指数定理 (Matrix Exponential)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.Exponential

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- 矩阵指数：exp(A) = Σ_{k=0}^∞ A^k / k! -/
noncomputable def exp (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  ∑' k : ℕ, (1 / k.factorial) • A^k

/-- 矩阵指数的微分性质：d/dt exp(tA) = A exp(tA) -/
theorem deriv_matrix_exponential (A : Matrix n n 𝕜) (t : 𝕜) :
    deriv (fun s => exp (s • A)) t = A * exp (t • A) := by
  -- 利用幂级数在收敛圆盘内的逐项可微性证明
  sorry

end Matrix
```

## 数学背景

矩阵指数是数学分析、线性代数和微分方程理论中的核心概念，它将标量指数函数 $e^x$ 自然地推广到方阵情形。矩阵指数最早由意大利数学家 Giuseppe Peano 和法国数学家 Marie Ennemond Camille Jordan 在19世纪末系统研究。矩阵指数是求解线性常微分方程组、李群李代数理论、控制理论和量子力学的基本工具。

## 直观解释

矩阵指数可以看作是连续复合线性变换的数学表达。想象矩阵 $A$ 描述了一个微小的瞬时变化（如速度场），那么 $e^{tA}$ 就表示经过时间 $t$ 后的累积效应。这与银行存款的复利计算完全类似：标量指数 $e^{rt}$ 表示连续复利增长，而矩阵指数 $e^{tA}$ 则表示多个相互耦合的方向上的连续线性演化。

## 形式化表述

设 $A$ 是一个 $n \times n$ 复方阵，其指数定义为幂级数：

$$e^A = \sum_{k=0}^\infty \frac{A^k}{k!} = I + A + \frac{A^2}{2!} + \frac{A^3}{3!} + \cdots$$

该级数对任意方阵 $A$ 绝对收敛。

基本性质：

1. $e^0 = I$
2. $\frac{d}{dt} e^{tA} = A e^{tA} = e^{tA} A$
3. 若 $AB = BA$，则 $e^{A+B} = e^A e^B$
4. $(e^A)^{-1} = e^{-A}$
5. $\det(e^A) = e^{\text{tr}(A)}$（Liouville 公式）

线性微分方程组 $\frac{dx}{dt} = Ax$，$x(0) = x_0$ 的唯一解为 $x(t) = e^{tA} x_0$。

其中：

- $A^k$ 表示矩阵 $A$ 的 $k$ 次幂
- 级数收敛性由矩阵范数的比较判别法保证

## 证明思路

1. **级数收敛**：利用矩阵范数的次乘性 $||A^k|| \leq ||A||^k$，与标量指数级数比较得绝对收敛
2. **逐项微分**：在收敛域内对幂级数逐项求导，得到 $\frac{d}{dt} e^{tA} = A e^{tA}$
3. **交换性条件**：若 $AB = BA$，通过二项式定理展开 $(A+B)^k$ 证明 $e^{A+B} = e^A e^B$
4. **Liouville 公式**：对 $X(t) = e^{tA}$ 应用行列式导数公式，结合 $\det(e^A) = e^{\text{tr}(A)}$

核心洞察在于矩阵指数的解析性质与标量指数高度平行。

## 示例

### 示例 1：对角矩阵

若 $A = \text{diag}(\lambda_1, \dots, \lambda_n)$，则 $e^A = \text{diag}(e^{\lambda_1}, \dots, e^{\lambda_n})$。这直接验证了矩阵指数是对角元素分别取指数的自然推广。

### 示例 2：Jordan 块

对 $J = \begin{pmatrix} \lambda & 1 \ 0 & \lambda \end{pmatrix}$，有 $e^J = e^\lambda \begin{pmatrix} 1 & 1 \ 0 & 1 \end{pmatrix}$。这说明非对角化矩阵的矩阵指数会出现多项式项。

### 示例 3：旋转矩阵

设 $A = \begin{pmatrix} 0 & -\theta \ \theta & 0 \end{pmatrix}$，则 $e^A = \begin{pmatrix} \cos\theta & -\sin\theta \ \sin\theta & \cos\theta \end{pmatrix}$。这对应于平面上的角度为 $\theta$ 的旋转。

## 应用

- **线性微分方程**：常系数线性 ODE 系统解的显式表示
- **李群与李代数**：矩阵李群（如 $SO(n)$、$SU(n)$）的指数映射
- **控制理论**：线性时不变系统的状态转移矩阵
- **量子力学**：时间演化算符 $U(t) = e^{-iHt/\hbar}$
- **图网络分析**：图上热核和随机游走的连续时间推广

## 相关概念

- 幂级数 (Power Series)：矩阵指数的级数定义基础
- Jordan 标准型 (Jordan Normal Form)：计算矩阵指数的标准方法
- 状态转移矩阵 (State Transition Matrix)：控制系统中的 $\Phi(t) = e^{At}$
- Liouville 公式：$\det(e^A) = e^{\text{tr}(A)}$
- Lie 指数公式 (Lie Product Formula)：$e^{A+B} = \lim_{n \to \infty} (e^{A/n} e^{B/n})^n$

## 参考

### 教材

- [R. A. Horn, C. R. Johnson. Topics in Matrix Analysis. Cambridge, 1991. Chapter 6]
- [L. Perko. Differential Equations and Dynamical Systems. Springer, 3rd edition, 2001. Section 1.3]

### 在线资源

- [Mathlib4 - Exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Exponential.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*