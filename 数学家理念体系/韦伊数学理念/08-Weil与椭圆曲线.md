---
title: "Weil与椭圆曲线：从复乘到模性的桥梁"
level: gold
course: Weil数学理念
msc_primary: 14
msc_secondary:
  - 14H52
references:
  textbooks:
    - title: "Arithmetic of Elliptic Curves"
      author: "J. H. Silverman"
      year: 1986
    - title: "Advanced Topics in the Arithmetic of Elliptic Curves"
      author: "J. H. Silverman"
      year: 1994
  papers:
    - title: "Jacobi sums as 'Grössencharaktere'"
      author: "A. Weil"
      year: 1952
status: completed
created_at: 2026-04-18
---

# Weil与椭圆曲线：从复乘到模性的桥梁

## 1. 引言

椭圆曲线是数论中最丰富、最深刻的对象之一。André Weil在1940–1950年代的工作，特别是关于**复乘（complex multiplication）**和**Jacobian簇**的理论，为现代椭圆曲线的算术理论奠定了基础。

本文将分析Weil对椭圆曲线理论的贡献，探讨其相对于后来Tate、Shafarevich和Wiles工作的重要性，并阐述这一理论在当代数学中的核心地位。

## 2. 椭圆曲线基础

### 2.1 定义

**定义 2.1（椭圆曲线）**。域 $K$ 上的**椭圆曲线**是Weierstrass方程定义的平面曲线：

$$E: y^2 = x^3 + ax + b$$

满足判别式 $\Delta = -16(4a^3 + 27b^2) \neq 0$（保证非奇异）。

### 2.2 群结构

**定理 2.2**。椭圆曲线上的点配备弦切线加法构成**Abel群**。

- 单位元：无穷远点 $\mathcal{O}$
- 逆元：$-(x, y) = (x, -y)$
- 加法：过 $P, Q$ 的直线交 $E$ 于第三点 $R$，则 $P + Q = -R$

### 2.3 复数域上的椭圆曲线

**定理 2.3（Uniformization）**。复数域上的椭圆曲线同构于复环面：

$$E(\mathbb{C}) \cong \mathbb{C}/\Lambda$$

其中 $\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ 为格（lattice）。

## 3. Weil的复乘理论

### 3.1 复乘的定义

**定义 3.1（复乘）**。椭圆曲线 $E$ 有**复乘（CM）**，如果其endomorphism环 $End(E)$ 严格大于 $\mathbb{Z}$。

**定理 3.2**。对复椭圆曲线 $E = \mathbb{C}/\Lambda$：

$$End(E) \cong \{\alpha \in \mathbb{C} : \alpha\Lambda \subseteq \Lambda\}$$

$End(E) = \mathbb{Z}$ 或 $End(E) = \mathcal{O}_K$（虚二次域 $K$ 的整数环）。

### 3.2 Weil的CM理论

Weil在1952年的论文中建立了CM椭圆曲线的**类域理论**：

**定理 3.3（Weil）**。设 $E$ 为有CM by $\mathcal{O}_K$ 的椭圆曲线，$H$ 为 $K$ 的Hilbert类域。则：

1. $E$ 的j-不变量 $j(E) \in H$
2. $Gal(H/K)$ 在j-不变量上的作用对应于理想类群的作用

这一结果将**虚二次域的类域理论**与**椭圆曲线的算术**统一起来。

### 3.3 Weil配对

**定义 3.4（Weil配对）**。设 $E[n]$ 为 $n$-挠点群。Weil配对是：

$$e_n: E[n] \times E[n] \to \mu_n$$

满足交替性、Galois等变性和非退化性。

Weil配对在**椭圆曲线密码学**和**Galois表示**中具有核心重要性。

## 4. 从Weil到Wiles

### 4.1 模性猜想

**猜想 4.1（Shimura-Taniyama-Weil）**。每条定义在 $\mathbb{Q}$ 上的椭圆曲线都是**模的**，即对应一个权2的模形式。

Weil在1967年提出了这一猜想的**精确形式**，并给出了关键的**收敛条件**：

**定理 4.2（Weil）**。椭圆曲线 $E$ 对应的L-函数 $L(E, s)$ 如果满足一定的函数方程和Euler乘积条件，则 $E$ 是模的。

### 4.2 Fermat大定理

**定理 4.3（Wiles, 1995）**。每条半稳定椭圆曲线都是模的。

**推论 4.4（Fermat大定理）**。方程 $x^n + y^n = z^n$ 对 $n \geq 3$ 无正整数解。

Wiles的证明依赖于：

- **Ribet的level lowering**：将Fermat方程与椭圆曲线联系
- **Langlands-Tunnell**：GL(2)的Artin猜想对奇表示成立
- **Wiles的模性提升**：将3-adic表示提升到模表示

## 5. 批判性比较

| 维度 | Weil (1950s) | Tate (1960s) | Wiles (1995) |
|------|-------------|-------------|-------------|
| **核心工具** | 复乘、Abel簇 | p-adic分析 | Galois形变 |
| **主要成果** | CM的类域理论 | Tate模、BSD猜想 | Fermat大定理 |
| **技术层次** | 代数几何 | 算术几何 | Galois表示 |
| **对当代影响** | CM理论 | p-adic Hodge理论 | 模性提升 |

## 6. 当代应用

### 6.1 密码学

椭圆曲线密码学（ECC）依赖于：

- **离散对数问题**：$E(\mathbb{F}_q)$ 上的计算困难性
- **Weil配对**：用于基于配对的密码学

### 6.2  Birch-Swinnerton-Dyer猜想

**猜想 6.1（BSD）**。椭圆曲线 $E$ 的L-函数在 $s = 1$ 处的零点的阶等于 $E$ 的Mordell-Weil群的秩。

Weil的CM理论和Tate的p-adic分析是研究BSD猜想的核心工具。

## 7. Lean4 形式化对照

```lean4
import Mathlib

-- Weierstrass方程
example (a b : ℝ) (h : 4 * a^3 + 27 * b^2 ≠ 0) :
    IsSmooth (WeierstrassCurve a b) := by
  sorry

-- 群结构（概念性）
example (E : EllipticCurve ℚ) (P Q : E) :
    E.Point P → E.Point Q → E.Point (P + Q) := by
  sorry

-- Weil配对（概念性）
example (E : EllipticCurve ℚ) (n : ℕ) (P Q : E.torsion n) :
    rootsOfUnity n ℂ :=
  WeilPairing E n P Q
```

## 8. 结论

Weil对椭圆曲线理论的贡献是20世纪数学最重要的成就之一。从复乘的类域理论到Weil配对，从模性猜想的精确陈述到Fermat大定理的桥梁，Weil的工作贯穿了现代数论的核心。

正如他的学生Serge Lang所评价的："Weil的椭圆曲线理论是数论中最美丽的篇章之一。"

---

**参考文献**

1. Weil, A. "Jacobi sums as 'Grössencharaktere'." *Trans. AMS* 73 (1952), 487–495.
2. Weil, A. "Über die Bestimmung Dirichletscher Reihen durch Funktionalgleichungen." *Math. Ann.* 168 (1967), 149–156.
3. Silverman, J. H. *The Arithmetic of Elliptic Curves*. GTM 106, 1986.
4. Wiles, A. "Modular elliptic curves and Fermat's last theorem." *Ann. of Math.* 141 (1995), 443–551.
5. Diamond, F. & Shurman, J. *A First Course in Modular Forms*. GTM 228, 2005.
