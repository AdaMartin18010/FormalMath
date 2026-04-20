---
msc_primary: 94A60
msc_secondary:
  - 11T71
  - 14G50
  - 11A05
concept_type: 应用可视化
visualization_type: 流程图、密钥交换
title: RSA加密算法流程可视化
processed_at: '2026-04-05'
---

# RSA加密算法流程可视化

## 1. 数论基础

**定义 1.1（欧拉函数）**. 对正整数 $n$，欧拉函数 $\varphi(n)$ 定义为小于等于 $n$ 且与 $n$ 互素的正整数个数：
$$\varphi(n) = |\{k : 1 \leq k \leq n, \gcd(k,n) = 1\}|.$$

若 $n = p_1^{e_1} \cdots p_r^{e_r}$ 为素因子分解，则
$$\varphi(n) = n\prod_{i=1}^r\left(1 - \frac{1}{p_i}\right) = p_1^{e_1-1}(p_1-1) \cdots p_r^{e_r-1}(p_r-1).$$
特别地，对素数 $p$ 和 $q$，$\varphi(pq) = (p-1)(q-1)$。

**定理 1.2（Euler 定理）**. 若 $\gcd(a, n) = 1$，则 $a^{\varphi(n)} \equiv 1 \pmod{n}$。

*证明*. 考虑乘法群 $(\mathbb{Z}/n\mathbb{Z})^\times$，其阶为 $\varphi(n)$。由 Lagrange 定理，$a^{\varphi(n)} \equiv 1 \pmod{n}$。$\square$

**推论 1.3**. 在 RSA 条件下，$a^{ed} \equiv a \pmod{n}$ 对所有 $a$ 成立。

*证明*. 由构造 $ed \equiv 1 \pmod{\varphi(n)}$，即 $ed = 1 + k\varphi(n)$。若 $\gcd(a,n) = 1$，由 Euler 定理，$a^{ed} = a \cdot (a^{\varphi(n)})^k \equiv a \pmod{n}$。若 $\gcd(a,n) \neq 1$，不妨设 $p \mid a$。则 $a^{ed} \equiv a \pmod{p}$ 显然成立（两边均为 0）。模 $q$ 由 Euler 定理成立。由中国剩余定理，模 $n = pq$ 成立。$\square$

## 2. RSA 算法

### 2.1 密钥生成

1. 随机选择两个大素数 $p$ 和 $q$（实际应用中为 $1024$ 位或更大）；
2. 计算 $n = pq$ 和 $\varphi(n) = (p-1)(q-1)$；
3. 选择整数 $e$（加密指数）使得 $1 < e < \varphi(n)$ 且 $\gcd(e, \varphi(n)) = 1$；
4. 计算 $d$（解密指数）使得 $ed \equiv 1 \pmod{\varphi(n)}$，使用扩展欧几里得算法；
5. **公钥**：$(n, e)$；**私钥**：$(n, d)$（或仅 $d$，$p, q$ 保密）。

### 2.2 加密与解密

- **加密**：对明文消息 $m$（$0 \leq m < n$），密文 $c = m^e \bmod n$；
- **解密**：$m = c^d \bmod n$。

**正确性**. 由推论 1.3，$c^d = (m^e)^d = m^{ed} \equiv m \pmod{n}$。

### 2.3 具体数值例子

取小素数 $p = 61$，$q = 53$：
- $n = 61 \times 53 = 3233$；
- $\varphi(n) = 60 \times 52 = 3120$；
- 选 $e = 17$（$\gcd(17, 3120) = 1$）；
- 解 $17d \equiv 1 \pmod{3120}$，得 $d = 2753$。

加密消息 $m = 123$：
$$c = 123^{17} \bmod 3233 = 855.$$

解密：
$$m = 855^{2753} \bmod 3233 = 123.$$

## 3. 安全性分析

**定义 3.1（RSA 假设）**. RSA 问题：给定 $(n, e)$ 和 $c = m^e \bmod n$，求 $m$。RSA 假设断言不存在概率多项式时间算法以不可忽略概率解决 RSA 问题。

**定理 3.2（因子分解与 RSA 的关系）**.
- 若能有效分解 $n = pq$，则可有效计算 $\varphi(n)$ 和 $d$，从而破解 RSA；
- 目前未知：破解 RSA 是否等价于分解 $n$（即未知是否可在不分解 $n$ 的情况下求 $e$ 次根模 $n$）。

**实际攻击方式**（需防范）：
- **小指数攻击**：$e$ 太小（如 $e = 3$）且 $m$ 较小时，$m^e < n$，直接在整数上开 $e$ 次方即可；
- **共模攻击**：不同用户共享同一 $n$ 但使用不同 $e$；
- **侧信道攻击**：通过功耗、时间等物理信息推断私钥；
- **因子分解算法**：数域筛法（NFS）是目前最快的通用分解算法，亚指数复杂度。

## 4. 数字签名

RSA 亦可用于数字签名：
- **签名**：对消息哈希值 $h = H(m)$，签名 $\sigma = h^d \bmod n$；
- **验证**：检查 $\sigma^e \equiv h \pmod{n}$ 是否成立。

由 $ed \equiv 1 \pmod{\varphi(n)}}$，验证等式等价于 $h^{ed} \equiv h \pmod{n}$，与解密正确性同理。

## 5. 可视化：RSA 流程

```mermaid
graph TB
    subgraph RSA算法流程
    A[选择大素数 p, q] --> B[计算 n = pq, φ(n) = (p-1)(q-1)]
    B --> C[选择 e, gcd(e, φ(n)) = 1]
    C --> D[计算 d, ed ≡ 1 mod φ(n)]

    D --> E[公钥 (n, e)]
    D --> F[私钥 (n, d)]

    E --> G[加密 c = m^e mod n]
    F --> H[解密 m = c^d mod n]

    G --> I[密文 c]
    I --> H
    end

    style A fill:#e3f2fd
    style E fill:#e8f5e9
    style F fill:#fce4ec
    style G fill:#fff3e0
    style H fill:#f3e5f5
```

## 6. 参考

1. Rivest, R. L., Shamir, A., & Adleman, L. (1978). A Method for Obtaining Digital Signatures and Public-Key Cryptosystems. *Communications of the ACM*, 21(2), 120–126.
2. Boneh, D. (1999). Twenty Years of Attacks on the RSA Cryptosystem. *Notices of the AMS*, 46(2), 203–213.
3. Katz, J., & Lindell, Y. (2014). *Introduction to Modern Cryptography* (2nd ed.). CRC Press.
