---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Cramer 法则 (Cramer's Rule)
---
# Cramer 法则 (Cramer's Rule)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Cramer 法则：当 A 可逆时，线性方程组 Ax = b 的解为 x_i = det(A_i) / det(A) -/
theorem cramerRule (A : Matrix n n R) (b : n → R) (hA : IsUnit (det A)) (x : n → R)
    (hx : A *ᵥ x = b) (i : n) :
    x i = det (updateCol A i b) / det A := by
  -- 利用伴随矩阵与逆矩阵的关系 A⁻¹ = adj(A) / det(A) 推导
  sorry

end Matrix
```

## 数学背景

Cramer 法则是线性代数中关于线性方程组求解的经典定理，由瑞士数学家 Gabriel Cramer 于1750年系统发表。该法则给出了当系数矩阵可逆时，$n$ 元线性方程组解的显式公式。虽然从计算复杂度角度看，Cramer 法则对于大规模方程组远不如高斯消元法高效，但它在理论分析、符号计算、微分几何和经济学中具有不可替代的价值。

## 直观解释

Cramer 法则提供了一个优雅但计算代价高昂的求解方法。想象一个由 $n$ 个方程和 $n$ 个未知数组成的线性系统，就像一个有 $n$ 个入口和 $n$ 个出口的复杂水管网络。Cramer 法则告诉我们：每个未知数的解，等于将网络中对应入口替换为输出流量后，新网络的体积缩放因子（行列式）与原网络体积缩放因子的比值。虽然这个公式非常优美，但当网络很大时，计算行列式的代价是惊人的。

## 形式化表述

设 $A$ 是域 $\mathbb{F}$ 上的 $n \times n$ 可逆矩阵，$b \in \mathbb{F}^n$。则线性方程组 $Ax = b$ 的唯一解 $x = (x_1, x_2, \dots, x_n)^T$ 满足：

$$x_i = \frac{\det(A_i)}{\det(A)}, \quad i = 1, 2, \dots, n$$

其中 $A_i$ 是将矩阵 $A$ 的第 $i$ 列替换为向量 $b$ 后得到的矩阵：

$$A_i = \begin{pmatrix} a_{11} & \cdots & b_1 & \cdots & a_{1n} \ \vdots & \ddots & \vdots & \ddots & \vdots \ a_{n1} & \cdots & b_n & \cdots & a_{nn} \end{pmatrix}$$

条件：$\det(A) \neq 0$（即 $A$ 可逆）。

## 证明思路

1. **逆矩阵公式**：利用 $x = A^{-1}b$ 和伴随矩阵公式 $A^{-1} = \frac{1}{\det(A)} \text{adj}(A)$
2. **伴随矩阵展开**：$\text{adj}(A)_{ji} = (-1)^{i+j}M_{ij}$，其中 $M_{ij}$ 是余子式
3. **Laplace 展开**：将 $\det(A_i)$ 按第 $i$ 列展开，恰好等于 $(\text{adj}(A) \cdot b)_i$
4. **整理得结论**：$x_i = \frac{(\text{adj}(A) \cdot b)_i}{\det(A)} = \frac{\det(A_i)}{\det(A)}$

核心洞察在于伴随矩阵的列恰好编码了对应列被替换后的行列式变化。

## 示例

### 示例 1：2x2 方程组

设 $A = \begin{pmatrix} 2 & 1 \ 1 & 3 \end{pmatrix}$, $b = \begin{pmatrix} 5 \ 8 \end{pmatrix}$。
$\det(A) = 5$。
$A_1 = \begin{pmatrix} 5 & 1 \ 8 & 3 \end{pmatrix}$, $\det(A_1) = 7$。
$A_2 = \begin{pmatrix} 2 & 5 \ 1 & 8 \end{pmatrix}$, $\det(A_2) = 11$。
因此 $x_1 = 7/5$, $x_2 = 11/5$。
验证：$2(7/5) + 11/5 = 25/5 = 5$ ✓。

### 示例 2：经济模型

在投入产出分析中，Leontief 模型 $x = Ax + d$ 可化为 $(I-A)x = d$。Cramer 法则理论上可以给出各行业产出的显式表达式，尽管实际计算中通常使用数值方法。

### 示例 3：几何应用

求过三点 $(x_1,y_1), (x_2,y_2), (x_3,y_3)$ 的圆的方程可以通过将圆的一般方程系数视为未知数，建立线性方程组后用 Cramer 法则求解。

## 应用

- **符号计算**：计算机代数系统中精确求解小型线性方程组
- **微分几何**：曲线和曲面理论中的参数计算
- **经济学**：投入产出分析和均衡价格的显式表示
- **控制理论**：传递函数和状态空间方程的解析求解
- **插值理论**：多项式插值和样条曲线的系数确定

## 相关概念

- 行列式 (Determinant)：方阵的体积缩放因子和可逆性判别
- 伴随矩阵 (Adjugate Matrix)：由余子式转置构成的矩阵
- 逆矩阵 (Inverse Matrix)：满足 $AA^{-1} = I$ 的唯一矩阵
- 线性方程组 (System of Linear Equations)：$Ax = b$ 形式的方程组
- 高斯消元法 (Gaussian Elimination)：大规模线性方程组的高效数值解法

## 参考

### 教材

- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 5.3]
- [S. Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Section 10C]

### 在线资源

- [Mathlib4 - Matrix Adjugate](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*