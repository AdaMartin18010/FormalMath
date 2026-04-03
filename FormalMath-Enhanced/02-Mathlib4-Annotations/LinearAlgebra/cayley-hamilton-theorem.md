---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 凯莱-哈密顿定理 (Cayley-Hamilton Theorem)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
variable (A : Matrix n n R)

/-- 凯莱-哈密顿定理：矩阵满足其特征方程 -/
theorem cayleyHamilton : eval A (charpoly A) = 0 := by
  -- 经典证明：利用伴随矩阵
  sorry

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
variable (f : V →ₗ[R] V)

/-- 线性变换版本 -/
theorem cayleyHamilton' : aeval f (charpoly f) = 0 := by
  sorry

end LinearMap
```

## 数学背景

凯莱-哈密顿定理由英国数学家阿瑟·凯莱（Arthur Cayley）于1857年首次提出（对 2×2 矩阵），后由爱尔兰数学家威廉·罗文·哈密顿（William Rowan Hamilton）推广。虽然哈密顿首先认识到一般情形，但第一个完整证明由德国数学家费迪南德·乔治·弗罗贝尼乌斯（Ferdinand Georg Frobenius）于1878年给出。该定理是线性代数中最优美和出人意料的结果之一。

## 直观解释

凯莱-哈密顿定理告诉我们：**每个方阵都满足其自身的特征多项式**。也就是说，如果将矩阵 $A$ 代入其特征多项式 $p(\lambda) = \det(A - \lambda I)$ 中的 $\lambda$，得到的结果是零矩阵。

这是惊人的，因为特征多项式是标量多项式，而我们将矩阵代入其中。定理表明矩阵和其特征多项式之间存在深刻的内在联系——矩阵"知道"关于自身的特征值信息，且这种知识足以让它"消灭"自己的特征多项式。

## 形式化表述

设 $A$ 是 $n \times n$ 方阵，$p(\lambda) = \det(\lambda I - A) = \lambda^n + c_{n-1}\lambda^{n-1} + \cdots + c_1\lambda + c_0$ 是其特征多项式，则：

$$p(A) = A^n + c_{n-1}A^{n-1} + \cdots + c_1A + c_0I = 0$$

等价地，若 $\lambda_1, \ldots, \lambda_n$ 是 $A$ 的特征值，则：

$$(A - \lambda_1 I)(A - \lambda_2 I) \cdots (A - \lambda_n I) = 0$$

## 证明思路

### 弗罗贝尼乌斯证明（代数方法）：

1. **伴随矩阵**：考虑 $B(\lambda) = \text{adj}(\lambda I - A)$
2. **基本恒等式**：$(\lambda I - A)B(\lambda) = p(\lambda)I$
3. **多项式矩阵**：$B(\lambda)$ 是 $\lambda$ 的矩阵系数多项式
4. **代入**：将 $\lambda = A$ 代入，左边为 0，故 $p(A) = 0$

### 现代证明（密度论证）：

1. **可对角化矩阵**：对可对角化矩阵直接验证
2. **稠密性**：可对角化矩阵在复矩阵空间中稠密
3. **连续性**：$A \mapsto p(A)$ 是连续的
4. **结论**：由连续性，对所有矩阵成立

## 示例

### 示例 1：2×2 矩阵

$$A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$$

特征多项式：
$$p(\lambda) = \det\begin{pmatrix} \lambda-1 & -2 \\ -3 & \lambda-4 \end{pmatrix} = \lambda^2 - 5\lambda - 2$$

验证：
$$A^2 = \begin{pmatrix} 7 & 10 \\ 15 & 22 \end{pmatrix}$$

$$A^2 - 5A - 2I = \begin{pmatrix} 7 & 10 \\ 15 & 22 \end{pmatrix} - \begin{pmatrix} 5 & 10 \\ 15 & 20 \end{pmatrix} - \begin{pmatrix} 2 & 0 \\ 0 & 2 \end{pmatrix} = \begin{pmatrix} 0 & 0 \\ 0 & 0 \end{pmatrix}$$

### 示例 2：计算矩阵幂

设 $A$ 满足 $A^2 - 3A + 2I = 0$（特征多项式为 $\lambda^2 - 3\lambda + 2 = (\lambda-1)(\lambda-2)$）。

求 $A^{100}$：

由多项式除法，$\lambda^{100} = q(\lambda)(\lambda^2 - 3\lambda + 2) + r(\lambda)$，其中 $\deg r < 2$。

令 $\lambda = 1$：$1 = r(1)$；令 $\lambda = 2$：$2^{100} = r(2)$。

设 $r(\lambda) = a\lambda + b$，解得 $a = 2^{100} - 1$，$b = 2 - 2^{100}$。

因此 $A^{100} = (2^{100} - 1)A + (2 - 2^{100})I$。

### 示例 3：最小多项式

特征多项式的次数为 $n$，但 $A$ 可能满足更低次的多项式（最小多项式整除特征多项式）。

例如单位矩阵 $I$ 的特征多项式为 $(\lambda-1)^n$，但最小多项式仅为 $\lambda - 1$。

## 应用

- **矩阵函数**：通过多项式插值定义 $e^A$、$\sin(A)$ 等
- **控制理论**：能控性和能观性判据
- **差分方程**：常系数线性递推的求解
- **数值分析**：矩阵幂和矩阵指数的快速计算
- **表示理论**：群表示的特征理论

## 相关概念

- [特征多项式 (Characteristic Polynomial)](./characteristic-polynomial.md)：$\det(\lambda I - A)$
- [最小多项式 (Minimal Polynomial)](./minimal-polynomial.md)：使 $p(A) = 0$ 的最低次首一多项式
- [若尔当标准型 (Jordan Normal Form)](./jordan-normal-form.md)：矩阵的相似标准型
- [有理标准型 (Rational Canonical Form)](./rational-canonical-form.md)：不变因子理论
- [伴随矩阵 (Companion Matrix)](./companion-matrix.md)：给定多项式的矩阵实现

## 参考

### 教材

- [Hoffman & Kunze. Linear Algebra. Prentice Hall, 2nd edition, 1971. Section 6.2]
- [Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Chapter 8]

### 历史文献

- [Cayley. A Memoir on the Theory of Matrices. 1858]
- [Frobenius. Über lineare Substitutionen und bilineare Formen. 1878]

### 在线资源

- [Mathlib4 文档 - Charpoly](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
