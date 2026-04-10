---
习题编号: ALG-215
学科: 代数
知识点: 表示论-Schur函子
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Schur 函子

## 题目

**(a)** 定义 Schur 函子 S^λ(V) 并证明其函子性。

**(b)** 证明 Cauchy 公式和 Littlewood-Richardson 规则。

**(c)** 讨论 Schur 多项式和对称函数理论。

## 解答

### (a) Schur 函子

V 向量空间，λ 分拆。S^λ(V) = V^{⊗n} ⊗_{ℂ[S_n]} S^λ。

函子性：Schur 函子多项式，复合 GL(V) 作用。

### (b) Cauchy 公式

$$\sum_\lambda s_λ(x)s_λ(y) = \prod_{i,j} \frac{1}{1-x_iy_j}$$

LR 规则：c^λ_{μν} 是 Littlewood-Richardson 系数，s_μ s_ν = Σ c^λ_{μν} s_λ。

### (c) Schur 多项式

s_λ = det(h_{λ_i-i+j}) = det(e_{λ'_i-i+j})，Jacobi-Trudi 公式。
