---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 中国剩余定理 (Chinese Remainder Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Algebra.Module.Submodule.Basic

namespace Ideal

variable {R : Type*} [CommRing R]

/-- 中国剩余定理：两两互素的理想的交同构于直积 -/
def quotientInfRingEquivPiQuotient (I : ι → Ideal R) (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    (R ⧸ ⨅ i, I i) ≃+* Π i, R ⧸ I i :=
  quotientInfRingEquivPiQuotient_of_coprime I hI

/-- 版本：两个理想的情形 -/
def quotientInfRingEquivPiQuotientTwo (I J : Ideal R) (h : IsCoprime I J) :
    (R ⧸ I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) :=
  quotientInfRingEquivPiQuotient_of_coprime_two I J h

end Ideal
```

## 数学背景

中国剩余定理最早见于中国古代数学著作《孙子算经》（约公元3-5世纪），用于解决同余方程组问题。该定理在古代用于历法计算和军事部署。现代形式由大数学家们（包括高斯和欧拉）发展为环论中的一般定理，成为代数学和数论的基石。

## 直观解释

中国剩余定理解决这样的"古代密码"问题：

> "有物不知其数，三三数之剩二，五五数之剩三，七七数之剩二。问物几何？"

通俗地说，如果我们知道一个数除以几个两两互素的数后的余数，我们就能唯一确定这个数（模这些数的乘积）。

想象几把不同齿数的齿轮同步转动，只要知道每把齿轮的初始位置，就能预测整个系统的状态。

## 形式化表述

### 整数版本

设 $n_1, n_2, \ldots, n_k$ 两两互素，则对任意 $a_1, a_2, \ldots, a_k$，同余方程组：

$$\begin{cases}
x \equiv a_1 \pmod{n_1} \\
x \equiv a_2 \pmod{n_2} \\
\vdots \\
x \equiv a_k \pmod{n_k}
\end{cases}$$

在模 $N = n_1 n_2 \cdots n_k$ 下有唯一解。

### 环论版本
设 $I_1, I_2, \ldots, I_k$ 是交换环 $R$ 的两两互素理想，则：

$$R / (I_1 \cap I_2 \cap \cdots \cap I_k) \cong (R/I_1) \times (R/I_2) \times \cdots \times (R/I_k)$$

## 证明思路

1. **构造映射**：定义 $\varphi: R \to \prod_i (R/I_i)$，$\varphi(r) = (r + I_1, \ldots, r + I_k)$
2. **核的分析**：$\ker(\varphi) = \bigcap_i I_i$
3. **满射性**：利用理想的互素性，通过 Bézout 恒等式构造原像
4. **同构结论**：应用第一同构定理

关键点在于互素理想满足 $I + J = R$，可以构造 $1 = x + y$。

## 示例

### 示例 1：《孙子算经》问题

求解：$x \equiv 2 \pmod{3}$，$x \equiv 3 \pmod{5}$，$x \equiv 2 \pmod{7}$

**解法**：
- 设 $N = 3 \cdot 5 \cdot 7 = 105$
- $N_1 = 35$，$35 \equiv 2 \pmod{3}$，逆元 $y_1 = 2$（因为 $2 \cdot 2 = 4 \equiv 1$）
- $N_2 = 21$，$21 \equiv 1 \pmod{5}$，逆元 $y_2 = 1$
- $N_3 = 15$，$15 \equiv 1 \pmod{7}$，逆元 $y_3 = 1$

解：$x = 2 \cdot 35 \cdot 2 + 3 \cdot 21 \cdot 1 + 2 \cdot 15 \cdot 1 = 140 + 63 + 30 = 233 \equiv 23 \pmod{105}$

答案：**23**

### 示例 2：多项式环

在 $\mathbb{Q}[x]$ 中，设 $I_1 = (x)$，$I_2 = (x-1)$。

对 $f \equiv 1 \pmod{x}$，$f \equiv 2 \pmod{x-1}$，求 $f$。

由 $1 \cdot x + (-1) \cdot (x-1) = 1$，得：
$f = 2 \cdot x + 1 \cdot (-(x-1)) = 2x - x + 1 = x + 1$

### 示例 3：RSA 解密加速

设 $n = pq$，解密时计算 $m \equiv c^d \pmod{n}$。

利用中国剩余定理：
- 分别计算 $m_p \equiv c^d \pmod{p}$ 和 $m_q \equiv c^d \pmod{q}$
- 合并得到 $m \pmod{n}$

速度提升约 4 倍。

## 应用

- **密码学**：RSA 解密加速、秘密共享
- **编码理论**：剩余码（Residue Codes）
- **计算代数**：大整数运算分解
- **分布式系统**：时钟同步

## 相关概念

- [互素理想 (Coprime Ideals)](./coprime-ideals.md)：和为整个环的理想
- [商环 (Quotient Ring)](./quotient-ring.md)：环模理想的商
- [同余 (Congruence)](./congruence.md)：模运算等价关系
- [贝祖恒等式 (Bézout's Identity)](./bezout-identity.md)：线性组合表示最大公因子
- [直积 (Direct Product)](./direct-product.md)：代数结构的笛卡尔积

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 7.6]
- [Ireland & Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 3]

### 历史文献

- [孙子算经. 约公元3-5世纪]
- [Gauss. Disquisitiones Arithmeticae. 1801]

### 在线资源

- [Mathlib4 文档 - Ideal.Quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient.html)
- [Wikipedia - Chinese remainder theorem](https://en.wikipedia.org/wiki/Chinese_remainder_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
