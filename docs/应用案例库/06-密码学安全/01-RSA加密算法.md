---
msc_primary: 00A05
msc_secondary:
- 00A99
- 22E47
- 00A99
title: RSA加密算法
processed_at: '2026-04-05'
---
# RSA加密算法

## 概述
- **应用领域**: 密码学/信息安全
- **数学分支**: 数论
- **难度级别**: 中级（研究生）
- **关键词**: RSA、公钥密码学、大整数分解、欧拉定理、模幂运算

---

## 问题背景

RSA算法是1977年由Rivest、Shamir和Adleman提出的公钥加密算法，是目前最广泛使用的非对称加密算法之一。其核心安全性基于大整数分解的困难性——将两个大素数的乘积分解回原始素数在计算上是不可行的。

### 实际应用场景
- HTTPS/TLS安全通信
- 数字签名与身份认证
- 安全电子邮件（PGP/GPG）
- 软件发布签名验证
- 区块链钱包地址生成

---

## 数学建模

### 核心数学问题

**大整数分解问题**: 给定一个合数 $N = p \times q$，其中 $p$ 和 $q$ 是大素数，求出 $p$ 和 $q$。

### 数学基础

**定理 1 (欧拉定理)**: 若 $a$ 和 $n$ 互素，则
$$a^{\phi(n)} \equiv 1 \pmod{n}$$

其中 $\phi(n)$ 是欧拉函数，表示小于 $n$ 且与 $n$ 互素的正整数的个数。

**定理 2**: 若 $n = p \times q$（$p, q$ 为不同素数），则
$$\phi(n) = (p-1)(q-1)$$

---

## 数学方法

### RSA算法步骤

#### 密钥生成

1. **选择素数**: 随机选择两个大素数 $p$ 和 $q$（通常2048位或更长）

2. **计算模数**: 
   $$N = p \times q$$

3. **计算欧拉函数**:
   $$\phi(N) = (p-1)(q-1)$$

4. **选择公钥指数**: 选择 $e$ 满足 $1 < e < \phi(N)$ 且 $\gcd(e, \phi(N)) = 1$
   - 常用值: $e = 65537 = 2^{16} + 1$

5. **计算私钥指数**: 计算 $d$ 满足
   $$e \times d \equiv 1 \pmod{\phi(N)}$$
   - 使用扩展欧几里得算法求解

6. **输出密钥**:
   - 公钥: $(N, e)$
   - 私钥: $(N, d)$ 或 $(p, q, d)$

#### 加密过程

对于明文消息 $m$（$0 \leq m < N$）:
$$c = m^e \mod N$$

#### 解密过程

对于密文 $c$:
$$m = c^d \mod N$$

---

## 求解过程

### 正确性证明

**定理**: RSA解密能正确恢复原始消息。

**证明**:

需要证明: $(m^e)^d \equiv m \pmod{N}$

由密钥生成可知: $ed \equiv 1 \pmod{\phi(N)}$

即存在整数 $k$ 使得: $ed = 1 + k\phi(N) = 1 + k(p-1)(q-1)$

**情况 1**: $\gcd(m, p) = 1$

由费马小定理: $m^{p-1} \equiv 1 \pmod{p}$

因此:
$$(m^e)^d = m^{ed} = m^{1 + k(p-1)(q-1)} = m \cdot (m^{p-1})^{k(q-1)} \equiv m \cdot 1^{k(q-1)} \equiv m \pmod{p}$$

**情况 2**: $\gcd(m, p) = p$（即 $p | m$）

则 $m \equiv 0 \pmod{p}$，显然 $(m^e)^d \equiv 0 \equiv m \pmod{p}$

同理可证: $(m^e)^d \equiv m \pmod{q}$

由中国剩余定理: $(m^e)^d \equiv m \pmod{pq} = m \pmod{N}$ ∎

### 计算优化

#### 模幂运算 - 快速幂算法

```python
def modular_exponentiation(base, exp, mod):
    result = 1
    base = base % mod
    while exp > 0:
        if exp & 1:  # 如果exp是奇数
            result = (result * base) % mod
        exp >>= 1
        base = (base * base) % mod
    return result

```

时间复杂度: $O(\log e)$

#### 扩展欧几里得算法

用于计算私钥 $d$:

```python
def extended_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    x = y1
    y = x1 - (a // b) * y1
    return g, x, y

def mod_inverse(e, phi):
    g, x, _ = extended_gcd(e, phi)
    if g != 1:
        raise ValueError("逆元不存在")
    return (x % phi + phi) % phi

```

---

## 结果分析

### 安全性分析

| 密钥长度 | 预计安全年限 | 应用场景 |
|----------|-------------|----------|
| 1024位 | 已不安全 | 不再使用 |
| 2048位 | 2030年前 | 当前标准 |
| 3072位 | 2040年前 | 高安全需求 |
| 4096位 | 长期安全 | 敏感数据 |

### 已知攻击方式

1. **因数分解攻击**: 分解 $N$ 得到 $p, q$
   - 通用数域筛法(GNFS): 亚指数复杂度
   - Shor算法(量子): 多项式复杂度

2. **侧信道攻击**: 时间分析、功耗分析

3. **选择密文攻击**: 利用解密oracle

4. **共模攻击**: 相同 $N$ 不同 $e$ 的漏洞

### 实际应用注意事项

- **填充方案**: 原始RSA不安全，必须使用OAEP等填充
- **密钥管理**: 私钥必须安全存储
- **前向保密**: 结合Diffie-Hellman实现

---

## 拓展思考

### 理论问题

1. **量子威胁**: Shor算法可在多项式时间内分解大整数，后量子密码学成为研究热点

2. **确定性vs随机性**: RSA是确定性加密，实际应用中需要随机化填充

3. **同态性质**: RSA具有乘法同态性: $E(m_1) \cdot E(m_2) = E(m_1 \cdot m_2)$

### 应用延伸

- **RSA盲签名**: 保护签名者隐私
- **阈值RSA**: 私钥分片存储
- **RSA-OAEP**: 最优非对称加密填充

---

## 参考资源

### 原始论文
- Rivest, R. L., Shamir, A., & Adleman, L. (1978). A method for obtaining digital signatures and public-key cryptosystems. *Communications of the ACM*, 21(2), 120-126.

### 教材
- [1] Katz, J., & Lindell, Y. (2014). *Introduction to Modern Cryptography*. CRC Press.
- [2] Boneh, D., & Shoup, V. (2023). *A Graduate Course in Applied Cryptography*.

### 在线资源
- [RFC 8017](https://tools.ietf.org/html/rfc8017)[需更新][需更新]: RSA Cryptography Specifications Version 2.2
- [NIST SP 800-56B](https://csrc.nist.gov/publications/detail/sp/800-56b/rev-2/final)[需更新][需更新]: Recommendation for Pair-Wise Key Establishment Schemes

### 工具
- OpenSSL: `openssl genrsa`, `openssl rsa`
- Python: `pycryptodome`, `rsa`库
- Mathematica: `PowerMod`函数

---

**案例创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
