---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Cayley-Hamilton定理 (Cayley-Hamilton Theorem)
---
# Cayley-Hamilton定理 (Cayley-Hamilton Theorem)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace CayleyHamilton

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n R}

/-- Cayley-Hamilton定理 -/
theorem cayley_hamilton :
    A.charpoly.eval A = 0 := by
  -- 利用伴随矩阵
  sorry

/-- 矩阵满足其特征多项式 -/
theorem matrix_annihilates_charpoly :
    aeval A A.charpoly = 0 := by
  -- 多项式求值的零化
  sorry

end CayleyHamilton
```

## 数学背景

Cayley-Hamilton定理是线性代数中最基本、最重要的定理之一，由英国数学家Arthur Cayley于1858年首次陈述（对 $2 \times 2$ 和 $3 \times 3$ 矩阵），并由爱尔兰数学家William Rowan Hamilton在此前对四元数的研究中给出了相关思想。虽然Cayley本人没有给出一般情形的严格证明，但后世数学家逐步完善了这个定理的证明体系，使其成为线性代数的基石。

### 特征多项式的定义

**定义（特征多项式）**：设 $R$ 是交换环，$A \in M_{n \times n}(R)$ 是 $n \times n$ 矩阵。$A$ 的**特征多项式**（characteristic polynomial）定义为：

$$p_A(t) = \det(tI_n - A)$$

其中 $I_n$ 是 $n \times n$ 单位矩阵，$t$ 是未定元。展开后，$p_A(t)$ 是 $R[t]$ 中的首一多项式，次数为 $n$：

$$p_A(t) = t^n + c_{n-1}t^{n-1} + \cdots + c_1 t + c_0$$

系数 $c_i$ 可以用 $A$ 的特征值（在代数闭包中）或主子式来表示。特别地：
- $c_{n-1} = -\text{tr}(A)$（迹的相反数）
- $c_0 = (-1)^n \det(A)$

### 矩阵的多项式求值

**定义（矩阵多项式）**：设 $p(t) = a_m t^m + \cdots + a_1 t + a_0 \in R[t]$ 是多项式，$A \in M_{n \times n}(R)$。定义 $p$ 在 $A$ 处的**求值**为：

$$p(A) = a_m A^m + \cdots + a_1 A + a_0 I_n \in M_{n \times n}(R)$$

注意常数项 $a_0$ 被替换为 $a_0 I_n$，以保证运算在矩阵环中进行。

## Cayley-Hamilton定理的陈述

**定理（Cayley-Hamilton）**：设 $R$ 是交换环，$A \in M_{n \times n}(R)$。则 $A$ 满足其自身的特征多项式：

$$p_A(A) = A^n + c_{n-1}A^{n-1} + \cdots + c_1 A + c_0 I_n = 0$$

即 $p_A(A)$ 是零矩阵。

## 证明

### 证明一：利用伴随矩阵（代数证明）

**引理**：对任意方阵 $A$，有 $(tI_n - A) \cdot \text{adj}(tI_n - A) = \det(tI_n - A) \cdot I_n = p_A(t) I_n$，其中 $\text{adj}$ 表示伴随矩阵（adjugate matrix）。

这是行列式展开的基本性质。注意到 $\text{adj}(tI_n - A)$ 的每个元素都是 $tI_n - A$ 的代数余子式，因此是 $t$ 的次数不超过 $n-1$ 的多项式。我们可以将伴随矩阵写成：

$$\text{adj}(tI_n - A) = B_{n-1}t^{n-1} + B_{n-2}t^{n-2} + \cdots + B_1 t + B_0$$

其中每个 $B_i \in M_{n \times n}(R)$ 是常数矩阵。

将上式代入引理：

$$(tI_n - A)(B_{n-1}t^{n-1} + \cdots + B_0) = p_A(t) I_n$$

展开左边：

$$B_{n-1}t^n + (B_{n-2} - AB_{n-1})t^{n-1} + \cdots + (B_0 - AB_1)t - AB_0$$

而右边为：

$$t^n I_n + c_{n-1}t^{n-1}I_n + \cdots + c_1 t I_n + c_0 I_n$$

比较 $t^k$ 的系数，得到方程组：

$$
\begin{cases}
B_{n-1} = I_n \\
B_{n-2} - AB_{n-1} = c_{n-1}I_n \\
\vdots \\
B_0 - AB_1 = c_1 I_n \\
-AB_0 = c_0 I_n
\end{cases}
$$

将第 $i$ 个方程左乘 $A^{n-i}$ 并相加：

$$A^n B_{n-1} + A^{n-1}(B_{n-2} - AB_{n-1}) + \cdots + A(B_0 - AB_1) + (-AB_0)$$

$$= A^n + c_{n-1}A^{n-1} + \cdots + c_1 A + c_0 I_n = p_A(A)$$

但左边是望远镜求和，全部抵消为 $0$。因此 $p_A(A) = 0$。 $\square$

### 证明二：利用可对角化矩阵的稠密性（分析证明，适用于 $\mathbb{C}$）

设 $A \in M_{n \times n}(\mathbb{C})$。具有 $n$ 个不同特征值的矩阵在 $M_{n \times n}(\mathbb{C})$ 中稠密，且这些矩阵都是可对角化的。

若 $A = PDP^{-1}$ 是可对角化的，其中 $D = \text{diag}(\lambda_1, \ldots, \lambda_n)$，则：

$$p_A(A) = P \cdot p_A(D) \cdot P^{-1} = P \cdot \text{diag}(p_A(\lambda_1), \ldots, p_A(\lambda_n)) \cdot P^{-1}$$

由于每个 $\lambda_i$ 是 $p_A$ 的根，$p_A(\lambda_i) = 0$，因此 $p_A(A) = 0$。

因为可对角化矩阵稠密，且映射 $A \mapsto p_A(A)$ 是连续的（矩阵元素的连续函数），由连续性，$p_A(A) = 0$ 对所有 $A$ 成立。 $\square$

### 证明三：利用模论（结构定理证明）

将 $R^n$ 看作 $R[t]$-模，其中 $t$ 的作用由矩阵 $A$ 给出，即 $t \cdot v = Av$。由结构定理，这个模是挠模，其零化子理想由 $A$ 的极小多项式 $m_A(t)$ 生成。由于 $m_A(t)$ 整除 $p_A(t)$（在域上这是标准结果，在一般交换环上需要更细致的处理），且 $m_A(A) = 0$，可知 $p_A(A) = 0$。 $\square$

## 例子

### 例子1：$2 \times 2$ 矩阵

设 $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$，则特征多项式为：

$$p_A(t) = t^2 - (a+d)t + (ad-bc) = t^2 - \text{tr}(A)t + \det(A)$$

Cayley-Hamilton定理断言：

$$A^2 - (a+d)A + (ad-bc)I_2 = 0$$

直接验证：

$$A^2 = \begin{pmatrix} a^2+bc & ab+bd \\ ca+dc & cb+d^2 \end{pmatrix}$$

$$(a+d)A = \begin{pmatrix} a^2+ad & ab+bd \\ ca+dc & ad+d^2 \end{pmatrix}$$

相减并加上 $(ad-bc)I_2$：

$$A^2 - (a+d)A + (ad-bc)I_2 = \begin{pmatrix} bc-ad+ad-bc & 0 \\ 0 & cb+d^2-ad-d^2+ad-bc \end{pmatrix} = 0$$

### 例子2：幂零矩阵

设 $N$ 是幂零矩阵，$N^k = 0$ 对某个 $k$。$N$ 的特征多项式是 $p_N(t) = t^n$（因为幂零矩阵的所有特征值都是 $0$）。Cayley-Hamilton定理给出 $N^n = 0$，这与幂零性的定义一致。

### 例子3：幂等矩阵

设 $P$ 是幂等矩阵，$P^2 = P$。$P$ 的特征值只能是 $0$ 或 $1$。设 $r = \text{rank}(P)$，则 $p_P(t) = t^{n-r}(t-1)^r = t^n - rt^{n-1} + \cdots$。

由Cayley-Hamilton，$P^n - rP^{n-1} + \cdots = 0$。利用 $P^2 = P$，所有高次幂都等于 $P$，这可以简化为验证 $P(P-I) = 0$，即 $P^2 - P = 0$，这正是幂等性。

## 应用

### 1. 矩阵幂的计算

Cayley-Hamilton定理提供了计算矩阵高次幂的有效方法。由于 $p_A(A) = 0$，有 $A^n = -(c_{n-1}A^{n-1} + \cdots + c_0 I_n)$。这意味着任何 $A^k$（$k \geq n$）都可以约化为次数不超过 $n-1$ 的多项式。利用多项式除法，$A^k = q(A)p_A(A) + r(A) = r(A)$，其中 $\deg r < n$。

例如，要计算 $e^{tA}$，可以将其展开为幂级数，然后利用Cayley-Hamilton定理将高次项约化。

### 2. 矩阵指数与微分方程

在线性常微分方程组 $\frac{dx}{dt} = Ax$ 中，解为 $x(t) = e^{tA}x_0$。利用Cayley-Hamilton定理，$e^{tA}$ 可以表示为 $I, A, \ldots, A^{n-1}$ 的线性组合，系数是 $t$ 的解析函数。这提供了计算矩阵指数的系统方法。

### 3. 控制理论

在可控性分析中，Cayley-Hamilton定理用于证明可控性矩阵的秩条件。例如，对于线性系统 $\dot{x} = Ax + Bu$，可控性矩阵 $[B \ AB \ A^2B \ \cdots]$ 的秩不超过 $n$，因为 $A^n B$ 可以由 $B, AB, \ldots, A^{n-1}B$ 线性表示。

### 4. 极小多项式与特征多项式的关系

Cayley-Hamilton定理表明极小多项式 $m_A(t)$ 整除特征多项式 $p_A(t)$（在域上）。这提供了计算极小多项式的方法：只需检查 $p_A(t)$ 的因子。

### 5. 逆矩阵公式

若 $A$ 可逆，则 $\det(A) \neq 0$。由Cayley-Hamilton：

$$A^n + c_{n-1}A^{n-1} + \cdots + c_1 A + c_0 I_n = 0$$

移项并乘以 $A^{-1}$：

$$A^{-1} = -\frac{1}{c_0}(A^{n-1} + c_{n-1}A^{n-2} + \cdots + c_1 I_n)$$

这为逆矩阵提供了显式的多项式公式。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
