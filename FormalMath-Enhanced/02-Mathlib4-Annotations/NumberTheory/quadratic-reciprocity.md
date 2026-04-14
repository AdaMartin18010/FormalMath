---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 二次互反律 (Quadratic Reciprocity)
---
# 二次互反律 (Quadratic Reciprocity)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace NumberTheory

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpodd : p ≠ 2) (hqodd : q ≠ 2)

/-- 二次互反律 -/
theorem quadraticReciprocity (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * (q - 1) / 2) := by
  -- 高斯的经典证明
  sorry

/-- 补充律 1：$(\frac{-1}{p}) = (-1)^{(p-1)/2}$ -/
theorem legendreSym_neg_one :
    legendreSym p (-1 : ℤ) = (-1) ^ ((p - 1) / 2) := by
  sorry

/-- 补充律 2：$(\frac{2}{p}) = (-1)^{(p^2-1)/8}$ -/
theorem legendreSym_two :
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  sorry

end NumberTheory
```

## 数学背景

二次互反律被誉为"数论中的宝石"，由高斯（Carl Friedrich Gauss）于1796年首次证明，当时他年仅18岁。这一定律建立了两个不同奇素数之间二次剩余性质的深刻对称关系。高斯对此定理极为推崇，称之为"黄金定理"，并给出了八种不同的证明。二次互反律开启了代数数论的发展，是类域论的雏形。

## 直观解释

二次互反律回答这样的问题：**$p$ 是否是模 $q$ 的二次剩余？** 与 **$q$ 是否是模 $p$ 的二次剩余？** 这两个问题的答案通常是相关的。

定律表明，除非 $p$ 和 $q$ 都形如 $4k+3$，否则这两个问题的答案相同。如果都形如 $4k+3$，则答案相反。

想象两个互相"询问"的素数，它们的"回答"遵循特定的对称规律。

## 形式化表述

设 $p, q$ 是不同的奇素数，则：

$$\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$$

其中 $\left(\frac{a}{p}\right)$ 是勒让德符号：

- $+1$ 若 $a$ 是模 $p$ 的二次剩余且 $p \nmid a$
- $-1$ 若 $a$ 是模 $p$ 的二次非剩余
- $0$ 若 $p \mid a$

### 补充律

$$\left(\frac{-1}{p}\right) = (-1)^{\frac{p-1}{2}} = \begin{cases} +1 & p \equiv 1 \pmod{4} \\ -1 & p \equiv 3 \pmod{4} \end{cases}$$

$$\left(\frac{2}{p}\right) = (-1)^{\frac{p^2-1}{8}} = \begin{cases} +1 & p \equiv \pm 1 \pmod{8} \\ -1 & p \equiv \pm 3 \pmod{8} \end{cases}$$

## 证明思路

高斯的第一种证明（利用高斯和）：

1. **高斯和定义**：$g_p = \sum_{a=0}^{p-1} \left(\frac{a}{p}\right) \zeta_p^a$，其中 $\zeta_p = e^{2\pi i / p}$
2. **高斯和性质**：$g_p^2 = \left(\frac{-1}{p}\right) p = (-1)^{(p-1)/2} p$
3. **高斯和计算**：$g_p^{q-1} \equiv \left(\frac{q}{p}\right) \pmod{q}$
4. **互反律推导**：利用 $g_p^{q-1} = (g_p^2)^{(q-1)/2}$ 比较两种计算

## 示例

### 示例 1：计算勒让德符号

计算 $\left(\frac{3}{17}\right)$。

$3 \equiv 3 \pmod{4}$，$17 \equiv 1 \pmod{4}$

由二次互反律：$\left(\frac{3}{17}\right)\left(\frac{17}{3}\right) = (-1)^{1 \cdot 8} = 1$

$\left(\frac{17}{3}\right) = \left(\frac{2}{3}\right) = -1$

因此 $\left(\frac{3}{17}\right) = -1$，即 3 是模 17 的二次非剩余。

### 示例 2：判断可解性

判断 $x^2 \equiv 13 \pmod{17}$ 是否有解。

$\left(\frac{13}{17}\right)\left(\frac{17}{13}\right) = (-1)^{6 \cdot 8} = 1$

$\left(\frac{17}{13}\right) = \left(\frac{4}{13}\right) = \left(\frac{2}{13}\right)^2 = 1$

因此 $\left(\frac{13}{17}\right) = 1$，方程有解（实际解为 $x \equiv \pm 8 \pmod{17}$）。

### 示例 3：素性测试

二次互反律可用于 Lucas-Lehmer 测试等素性判定算法。

## 应用

- **密码学**：RSA 和椭圆曲线密码中的二次剩余判定
- **素性测试**：快速判定二次剩余性质
- **代数数论**：类域论和互反律的推广
- **编码理论**：二次剩余码的构造
- **计算数论**：大整数运算中的平方根计算

## 相关概念

- 勒让德符号 (Legendre Symbol)：二次剩余的记号
- 雅可比符号 (Jacobi Symbol)：勒让德符号的推广
- 高斯和 (Gauss Sum)：指数和与二次特征
- 有限域 (Finite Field)：$\mathbb{F}_p$ 上的二次方程
- 代数整数 (Algebraic Integer)：二次互反律的代数数论视角

## 参考

### 教材

- [Ireland & Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 5]
- [Davenport. The Higher Arithmetic. Cambridge, 8th edition, 2008. Chapter 6]

### 历史文献

- [Gauss. Disquisitiones Arithmeticae. 1801. Articles 131-163]

### 在线资源

- [Mathlib4 文档 - QuadraticReciprocity][https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
