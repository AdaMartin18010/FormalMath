# 狄利克雷定理 (Dirichlet's Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.DirichletTheorem

namespace Nat

variable {a m : ℕ} (ham : a.Coprime m)

/-- 狄利克雷定理：算术级数中有无穷多素数 -/
theorem dirichletTheorem :
    {p : ℕ | p.Prime ∧ p ≡ a [MOD m]}.Infinite := by
  -- 解析数论的深刻结果
  sorry

/-- 素数计数函数 -/
noncomputable def primeCountingMod (a m x : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ p ≤ x ∧ p ≡ a [MOD m]}.ncard

/-- 渐近公式 -/
theorem primeNumberTheoremForAP (x : ℝ) (hx : 0 < x) :
    (primeCountingMod a m ⌊x⌋ : ℝ) ∼[atTop] x / (Nat.totient m * Real.log x) := by
  sorry

end Nat
```

## 数学背景

狄利克雷定理是素数分布理论的重要里程碑，由德国数学家彼得·古斯塔夫·勒热纳·狄利克雷（Peter Gustav Lejeune Dirichlet）于1837年证明。这是首次成功应用解析方法（特别是狄利克雷 $L$-函数）解决数论问题，开创了解析数论的新纪元。该定理推广了欧几里得关于存在无穷多素数的经典结果。

## 直观解释

狄利克雷定理告诉我们：**如果 $a$ 和 $m$ 互素，那么等差数列 $a, a+m, a+2m, a+3m, \ldots$ 中包含无穷多个素数**。

想象一条无限长的数轴，每隔 $m$ 个单位标记一个点（等差数列）。只要起始点 $a$ 与步长 $m$ 没有公因子，这条"虚线"就会无限次穿过素数。

直观上，这样的算术级数中的素数"密度"约为所有素数的 $\frac{1}{\varphi(m)}$，其中 $\varphi$ 是欧拉函数。

## 形式化表述

设 $a, m$ 是互素的正整数，则存在无穷多个形如 $p = a + km$（$k \geq 0$）的素数。

### 渐近分布

若 $\pi_{a,m}(x)$ 表示不超过 $x$ 且满足 $p \equiv a \pmod{m}$ 的素数个数，则：

$$\pi_{a,m}(x) \sim \frac{1}{\varphi(m)} \cdot \frac{x}{\ln x}$$

其中 $\varphi(m)$ 是欧拉函数。

## 证明思路

### 狄利克雷的核心方法：

1. **狄利克雷特征**：定义模 $m$ 的狄利克雷特征 $\chi: (\mathbb{Z}/m\mathbb{Z})^\times \to \mathbb{C}^\times$
2. **$L$-函数**：定义 $L(s, \chi) = \sum_{n=1}^{\infty} \frac{\chi(n)}{n^s}$
3. **非零性证明**：证明对非主特征 $\chi$，$L(1, \chi) \neq 0$
4. **对数导数**：利用 $-\frac{L'(s, \chi)}{L(s, \chi)}$ 提取素数信息
5. **特征正交性**：利用特征的正交性分离特定算术级数

核心是 $L(1, \chi) \neq 0$ 的证明，这保证了相应算术级数中素数的"密度"非零。

## 示例

### 示例 1：模 4 的素数

- $p \equiv 1 \pmod{4}$：5, 13, 17, 29, 37, 41, ...
- $p \equiv 3 \pmod{4}$：3, 7, 11, 19, 23, 31, ...

两类素数都无穷多，密度各约 $1/2$。

注意：$p \equiv 3 \pmod{4}$ 时，$\left(\frac{-1}{p}\right) = -1$（-1 是非剩余）。

### 示例 2：孪生素数的前奏

考虑 $p \equiv -1 \pmod{6}$，即 $p \equiv 5 \pmod{6}$。

这些素数都形如 $6k - 1$。孪生素数（除 3, 5 外）必为 $6k - 1$ 和 $6k + 1$ 形式。

狄利克雷定理保证无穷多 $p \equiv 5 \pmod{6}$ 的素数，但孪生素数是否无穷仍是开放问题。

### 示例 3：特殊形式素数

- **费马素数**：形如 $2^{2^n} + 1$ 的素数（对应 $p \equiv 1 \pmod{2^{n+1}}$）
- **梅森素数**：形如 $2^p - 1$ 的素数（对应 $p \equiv -1 \pmod{2p}$）

狄利克雷定理保证算术级数中有无穷多素数，但特定形式可能只有有限个。

## 应用

- **密码学**：特殊形式素数的生成（安全素数、索菲·热尔曼素数）
- **计算数论**：素数筛法和素性测试
- **代数数论**：分圆域和类域论
- **解析数论**：$L$-函数理论的发展
- **组合数论**：算术级数中的结构定理

## 相关概念

- [狄利克雷特征 (Dirichlet Character)](./dirichlet-character.md)：模 $m$ 的群同态
- [狄利克雷 $L$-函数 (Dirichlet L-function)](./dirichlet-l-function.md)：推广黎曼 $\zeta$ 函数
- [欧拉函数 (Euler's Totient Function)](./euler-totient.md)：$(\mathbb{Z}/m\mathbb{Z})^\times$ 的阶
- [类数公式 (Class Number Formula)](./class-number-formula.md)：$L(1, \chi)$ 的代数解释
- [格林-陶定理 (Green-Tao Theorem)](./green-tao-theorem.md)：任意长素数等差数列

## 参考

### 教材

- [Davenport. Multiplicative Number Theory. Springer, 3rd edition, 2000. Chapter 4]
- [Serre. A Course in Arithmetic. Springer, 1973. Chapter VI]

### 历史文献

- [Dirichlet. Beweis des Satzes, dass jede unbegrenzte arithmetische Progression... 1837]

### 在线资源

- [Mathlib4 文档 - DirichletTheorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletTheorem.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
