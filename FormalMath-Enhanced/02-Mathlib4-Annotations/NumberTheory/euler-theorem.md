---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 欧拉定理 (Euler's Theorem)
---
# 欧拉定理 (Euler's Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Eulerian

namespace NumberTheory

variable {n a : ℕ} (hcoprime : a.Coprime n)

/-- 欧拉定理：若 a 与 n 互素，则 a^{φ(n)} ≡ 1 (mod n) -/
theorem euler_theorem :
    a ^ n.totient ≡ 1 [MOD n] := by
  -- 利用 (Z/nZ)^× 是阶为 φ(n) 的乘法群，应用 Lagrange 定理
  sorry

end NumberTheory
```

## 数学背景

欧拉定理由瑞士数学家莱昂哈德·欧拉（Leonhard Euler）于1763年证明，是数论中最重要的结果之一。该定理是费马小定理的推广，断言：若整数 $a$ 与正整数 $n$ 互素，则 $a^{{\varphi(n)}} \equiv 1 \pmod{n}$，其中 $\varphi(n)$ 是欧拉 totient 函数（表示小于 $n$ 且与 $n$ 互素的正整数的个数）。这一定理深刻揭示了模乘法群的周期性结构，是公钥密码学（尤其是 RSA）的数学基石。

## 直观解释

欧拉定理可以类比为一个旋转对称群的周期现象。想象一个钟面上只有与 $n$ 互素的那些刻度，总共有 $\varphi(n)$ 个。每次将指针向前移动 $a$ 格（因为 $a$ 与 $n$ 互素，所以不会跳过任何有效刻度）。欧拉定理告诉我们：经过恰好 $\varphi(n)$ 次移动后，指针一定会回到起点。这就像在玩一个有 $\varphi(n)$ 个位置的轮盘，每次跳 $a$ 步，最终必然遍历所有位置后回到原点。这种周期性是模运算对称性的体现。

## 形式化表述

设 $a$ 和 $n$ 是互素的正整数（即 $\gcd(a, n) = 1$），$\varphi(n)$ 是欧拉 totient 函数，则：

$$a^{{\varphi(n)}} \equiv 1 \pmod{n}$$

更一般地，对任意整数 $k$：

$$a^k \equiv a^{{k \bmod \varphi(n)}} \pmod{n}$$

当 $n = p$ 为素数时，$\varphi(p) = p - 1$，欧拉定理退化为费马小定理：

$$a^{{p-1}} \equiv 1 \pmod{p}$$

其中：

- $\varphi(n) = |\{k \in \{1, 2, \dots, n\} : \gcd(k, n) = 1\}|$
- $(\mathbb{Z}/n\mathbb{Z})^\times$ 是模 $n$ 的乘法群，其阶为 $\varphi(n)$

## 证明思路

1. **乘法群结构**：考虑乘法群 $G = (\mathbb{Z}/n\mathbb{Z})^\times$，其阶为 $\varphi(n)$
2. **Lagrange 定理**：群 $G$ 中任意元素 $a$ 的阶整除群的阶 $\varphi(n)$
3. **幂运算**：设 $a$ 的阶为 $d$，则 $d | \varphi(n)$，故 $a^{{\varphi(n)}} = (a^d)^{{\varphi(n)/d}} = 1^{{\varphi(n)/d}} = 1$
4. **同态视角**：映射 $a \mapsto a^{{\varphi(n)}}$ 是群自同态，由 Lagrange 定理知其核为整个群

核心洞察在于模乘法群的有限性保证了幂运算的周期性。

## 示例

### 示例 1：RSA 加密

在 RSA 中，选择 $n = pq$（两个大素数的乘积），$\varphi(n) = (p-1)(q-1)$。加密密钥 $e$ 和私钥 $d$ 满足 $ed \equiv 1 \pmod{\varphi(n)}$。欧拉定理保证 $(m^e)^d \equiv m^{{ed}} \equiv m \pmod{n}$，即解密成功。

### 示例 2：快速幂取模

计算 $7^{{100}} \pmod{10}$。因 $\varphi(10) = 4$，由欧拉定理 $7^4 \equiv 1 \pmod{10}$，故 $7^{{100}} = (7^4)^{{25}} \equiv 1 \pmod{10}$。

### 示例 3：素数检验

费马素性检验利用 $a^{{p-1}} \equiv 1 \pmod{p}$（欧拉定理的素数情形）来快速排除合数。虽然存在 Carmichael 数等伪素数，但该检验是 Miller-Rabin 等更强算法的基础。

## 应用

- **RSA 密码体制**：公钥加密和数字签名的数学基础
- **模幂运算**：快速计算大数模幂的算法设计
- **素性检验**：费马检验和 Miller-Rabin 检验的理论依据
- **原根理论**：乘法群的生成元和离散对数问题
- **代数数论**：分圆域和特征标的结构研究

## 相关概念

- 欧拉 totient 函数 (Euler's Totient Function)：小于 $n$ 且与 $n$ 互素的正整数个数
- 费马小定理 (Fermat's Little Theorem)：欧拉定理在素数模下的特例
- 模乘法群 (Multiplicative Group of Integers Modulo n)：$(\mathbb{Z}/n\mathbb{Z})^\times$
- Lagrange 定理 (Lagrange's Theorem)：有限群中元素阶整除群的阶
- Carmichael 数 (Carmichael Number)：通过费马检验的合数

## 参考

### 教材

- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 4]
- [N. Koblitz. A Course in Number Theory and Cryptography. Springer, 1994. Chapter 1]

### 在线资源

- [Mathlib4 - Totient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Totient.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*