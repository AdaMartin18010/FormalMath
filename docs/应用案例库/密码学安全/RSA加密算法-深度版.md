---
msc_primary: 11T71
msc_secondary:
- 94A60
- 11A41
- 68P25
title: RSA加密算法：从数论基础到现代密码学实践（深度教学版）
processed_at: '2026-04-05'
---
# RSA加密算法：从数论基础到现代密码学实践（深度教学版）

---

## 一、历史背景与核心思想

### 1.1 公钥密码学的诞生

1976年，Whitfield Diffie和Martin Hellman在论文《New Directions in Cryptography》中提出了公钥密码学的革命性概念，彻底改变了密码学的发展方向。在此之前，所有加密系统都依赖于**对称密钥**——加密和解密使用相同的密钥，这带来了密钥分发的根本性问题。

1977年，三位MIT的科学家Ron Rivest、Adi Shamir和Leonard Adleman基于大整数分解的困难性，构造出了第一个实用的公钥加密算法——**RSA算法**。这一算法以他们姓氏的首字母命名，并于1978年正式发表。

> **历史意义**: RSA算法不仅解决了密钥分发问题，还首次实现了数字签名功能，为现代互联网安全（HTTPS、数字证书、区块链等）奠定了数学基础。

### 1.2 核心安全假设

RSA的安全性建立在以下**计算困难性假设**之上：

**大整数分解问题 (Integer Factorization Problem)**:
给定一个合数 $N = p \times q$，其中 $p$ 和 $q$ 是两个大素数，求出 $p$ 和 $q$ 在计算上是不可行的。

目前，对于足够大的 $N$（如2048位），即使使用最先进的算法（通用数域筛法GNFS），分解所需的时间也远超宇宙年龄。

---

## 二、数论基础：从欧拉到费马

### 2.1 欧拉函数与欧拉定理

**定义 2.1 (欧拉函数)**: 对于正整数 $n$，欧拉函数 $\phi(n)$ 表示小于或等于 $n$ 且与 $n$ 互素的正整数的个数：

$$\phi(n) = |\{k \in \mathbb{Z} : 1 \leq k \leq n, \gcd(k, n) = 1\}|$$

**定理 2.2 (欧拉函数的计算)**:

1. 若 $p$ 是素数，则 $\phi(p) = p - 1$
2. 若 $p$ 是素数，$k \geq 1$，则 $\phi(p^k) = p^k - p^{k-1} = p^{k-1}(p-1)$
3. 若 $\gcd(m, n) = 1$，则 $\phi(mn) = \phi(m)\phi(n)$（乘性函数）

**推论 2.3**: 若 $n = p \times q$，其中 $p, q$ 为不同素数，则：

$$\boxed{\phi(n) = (p-1)(q-1)}$$

**证明**: 由乘性性质，$\phi(pq) = \phi(p)\phi(q) = (p-1)(q-1)$。∎

**定理 2.4 (欧拉定理)**: 若 $a$ 和 $n$ 互素（即 $\gcd(a, n) = 1$），则：

$$a^{\phi(n)} \equiv 1 \pmod{n}$$

**证明**:

设 $(\mathbb{Z}/n\mathbb{Z})^\times$ 为模 $n$ 的乘法群，其阶为 $\phi(n)$。根据**拉格朗日定理**，群中任意元素的阶整除群的阶，因此：

$$a^{\phi(n)} \equiv 1 \pmod{n}$$ ∎

### 2.2 费马小定理

**定理 2.5 (费马小定理)**: 若 $p$ 是素数且 $p \nmid a$，则：

$$a^{p-1} \equiv 1 \pmod{p}$$

**证明**: 这是欧拉定理的特例，因为当 $n = p$ 为素数时，$\phi(p) = p - 1$。∎

**等价形式**: 对于任意整数 $a$ 和素数 $p$：

$$a^p \equiv a \pmod{p}$$

### 2.3 扩展欧几里得算法

**定理 2.6 (贝祖等式)**: 对于任意整数 $a, b$，存在整数 $x, y$ 使得：

$$\gcd(a, b) = ax + by$$

**算法 2.7 (扩展欧几里得算法)**:

```python
def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    """
    返回 (g, x, y) 使得 ax + by = g = gcd(a, b)
    """
    if b == 0:
        return (abs(a), 1 if a > 0 else -1, 0)

    g, x1, y1 = extended_gcd(b, a % b)
    x = y1
    y = x1 - (a // b) * y1
    return (g, x, y)

def mod_inverse(e: int, phi: int) -> int:
    """
    计算 e 模 phi 的乘法逆元 d
    即找到 d 使得 e*d ≡ 1 (mod phi)
    """
    g, x, _ = extended_gcd(e, phi)
    if g != 1:
        raise ValueError(f"逆元不存在: gcd({e}, {phi}) = {g}")
    return (x % phi + phi) % phi

```

---

## 三、RSA算法的完整数学描述

### 3.1 密钥生成

**算法 3.1 (RSA密钥生成)**:

**输入**: 安全参数 $k$（密钥长度，如2048位）

**输出**: 公钥 $(N, e)$，私钥 $(N, d)$

1. **选择素数**: 随机选择两个不同的 $k/2$ 位素数 $p$ 和 $q$
   - 通常使用Miller-Rabin素性测试

2. **计算模数**:
   $$N = p \times q$$

3. **计算欧拉函数**:
   $$\phi(N) = (p-1)(q-1)$$

4. **选择公钥指数**: 选择 $e$ 满足：
   - $1 < e < \phi(N)$
   - $\gcd(e, \phi(N)) = 1$

   常用值: $e = 65537 = 2^{16} + 1$（Fermat素数，计算高效）

5. **计算私钥指数**: 计算 $d$ 满足：
   $$e \times d \equiv 1 \pmod{\phi(N)}$$

   使用扩展欧几里得算法求解。

6. **输出**:
   - 公钥: $PK = (N, e)$
   - 私钥: $SK = (N, d)$（或包含 $p, q$ 用于加速解密）

### 3.2 加密与解密

**算法 3.2 (RSA加密)**:

**输入**: 公钥 $(N, e)$，明文消息 $m \in [0, N-1]$

**输出**: 密文 $c$

$$c = m^e \mod N$$

**算法 3.3 (RSA解密)**:

**输入**: 私钥 $(N, d)$，密文 $c$

**输出**: 明文 $m$

$$m = c^d \mod N$$

### 3.3 正确性证明

**定理 3.4 (RSA正确性)**: 对于所有 $m \in [0, N-1]$：

$$(m^e)^d \equiv m \pmod{N}$$

**证明**:

由密钥生成可知 $ed \equiv 1 \pmod{\phi(N)}$，即存在整数 $k$ 使得：

$$ed = 1 + k\phi(N) = 1 + k(p-1)(q-1)$$

我们需要证明 $m^{ed} \equiv m \pmod{N}$，即同时证明：
$$m^{ed} \equiv m \pmod{p}$$
$$m^{ed} \equiv m \pmod{q}$$

**情况1**: $\gcd(m, p) = 1$

由费马小定理：$m^{p-1} \equiv 1 \pmod{p}$

因此：
\begin{align*}
m^{ed} &= m^{1 + k(p-1)(q-1)} \\
&= m \cdot (m^{p-1})^{k(q-1)} \\
&\equiv m \cdot 1^{k(q-1)} \\
&\equiv m \pmod{p}
\end{align*}

**情况2**: $\gcd(m, p) = p$（即 $p | m$）

则 $m \equiv 0 \pmod{p}$，显然 $m^{ed} \equiv 0 \equiv m \pmod{p}$

同理可证 $m^{ed} \equiv m \pmod{q}$

由中国剩余定理（CRT）：若 $x \equiv m \pmod{p}$ 且 $x \equiv m \pmod{q}$，则 $x \equiv m \pmod{pq} = m \pmod{N}$

因此 $(m^e)^d \equiv m \pmod{N}$。∎

---

## 四、完整数值例子

### 4.1 小素数演示

让我们使用小素数来完整演示RSA的工作原理：

**步骤1**: 选择素数 $p = 61$，$q = 53$

**步骤2**: 计算模数
$$N = p \times q = 61 \times 53 = 3233$$

**步骤3**: 计算欧拉函数
$$\phi(N) = (61-1)(53-1) = 60 \times 52 = 3120$$

**步骤4**: 选择公钥指数
选择 $e = 17$（满足 $\gcd(17, 3120) = 1$）

**步骤5**: 计算私钥指数
求解 $17d \equiv 1 \pmod{3120}$

使用扩展欧几里得算法：

```

3120 = 183 × 17 + 9
17   = 1   × 9 + 8
9    = 1   × 8 + 1
8    = 8   × 1 + 0

回代:
1 = 9 - 1 × 8
  = 9 - 1 × (17 - 1 × 9) = 2 × 9 - 17
  = 2 × (3120 - 183 × 17) - 17
  = 2 × 3120 - 367 × 17

```

因此 $d = -367 \equiv 2753 \pmod{3120}$

**验证**: $17 \times 2753 = 46801 = 15 \times 3120 + 1 \equiv 1 \pmod{3120}$ ✓

**公钥**: $(N, e) = (3233, 17)$
**私钥**: $(N, d) = (3233, 2753)$

### 4.2 加密与解密演示

**加密消息**: $m = 65$（ASCII 'A' = 65）

$$c = m^e \mod N = 65^{17} \mod 3233$$

使用快速幂算法：

```

65^1   ≡ 65     (mod 3233)
65^2   ≡ 4225 ≡ 992   (mod 3233)
65^4   ≡ 992^2 ≡ 984064 ≡ 1370 (mod 3233)
65^8   ≡ 1370^2 ≡ 1876900 ≡ 2142 (mod 3233)
65^16  ≡ 2142^2 ≡ 4588164 ≡ 1693 (mod 3233)

65^17 = 65^16 × 65^1 ≡ 1693 × 65 = 110045 ≡ 2790 (mod 3233)

```

**密文**: $c = 2790$

**解密**:
$$m = c^d \mod N = 2790^{2753} \mod 3233$$

使用CRT加速（已知 $p = 61, q = 53$）：

计算 $d_p = d \mod (p-1) = 2753 \mod 60 = 53$
计算 $d_q = d \mod (q-1) = 2753 \mod 52 = 49$

$$m_p = 2790^{53} \mod 61 = 4$$
$$m_q = 2790^{49} \mod 53 = 12$$

使用Garner公式或CRT：
$$m = m_p + p \times ((m_q - m_p) \times p^{-1} \mod q)$$

计算 $p^{-1} \mod q = 61^{-1} \mod 53 = 38$

$$m = 4 + 61 \times ((12 - 4) \times 38 \mod 53)$$
$$= 4 + 61 \times (8 \times 38 \mod 53)$$
$$= 4 + 61 \times (304 \mod 53)$$
$$= 4 + 61 \times 39$$
$$= 4 + 2379 = 2383 \equiv 65 \pmod{3233}$$ ✓

---

## 五、Python完整实现

```python
"""
RSA加密算法完整实现
包含密钥生成、加密、解密、以及CRT加速
"""
import random
import secrets
from typing import Tuple, Optional

class RSA:
    def __init__(self, key_size: int = 2048):
        """初始化RSA，生成密钥对"""
        self.key_size = key_size
        self._generate_keys()

    def _miller_rabin(self, n: int, k: int = 40) -> bool:
        """Miller-Rabin素性测试"""
        if n < 2: return False
        if n in (2, 3): return True
        if n % 2 == 0: return False

        # 写成 n-1 = 2^r * d
        r, d = 0, n - 1
        while d % 2 == 0:
            r += 1
            d //= 2

        for _ in range(k):
            a = random.randrange(2, n - 1)
            x = pow(a, d, n)
            if x == 1 or x == n - 1:
                continue
            for _ in range(r - 1):
                x = pow(x, 2, n)
                if x == n - 1:
                    break
            else:
                return False
        return True

    def _generate_prime(self, bits: int) -> int:
        """生成指定位数的素数"""
        while True:
            n = secrets.randbits(bits) | 1 | (1 << (bits - 1))

            if self._miller_rabin(n):
                return n

    def _extended_gcd(self, a: int, b: int) -> Tuple[int, int, int]:
        """扩展欧几里得算法"""
        if b == 0:
            return (a, 1, 0)
        g, x1, y1 = self._extended_gcd(b, a % b)
        x = y1
        y = x1 - (a // b) * y1
        return (g, x, y)

    def _mod_inverse(self, e: int, phi: int) -> int:
        """计算模逆元"""
        g, x, _ = self._extended_gcd(e, phi)
        if g != 1:
            raise ValueError("逆元不存在")
        return (x % phi + phi) % phi

    def _generate_keys(self):
        """生成RSA密钥对"""
        # 选择两个大素数
        p = self._generate_prime(self.key_size // 2)
        q = self._generate_prime(self.key_size // 2)

        self.N = p * q
        self.phi = (p - 1) * (q - 1)

        # 选择公钥指数 (常用 65537)
        self.e = 65537
        while self._extended_gcd(self.e, self.phi)[0] != 1:
            self.e = self._generate_prime(17)

        # 计算私钥指数
        self.d = self._mod_inverse(self.e, self.phi)

        # 保存p, q用于CRT加速
        self.p, self.q = p, q
        self.dp = self.d % (p - 1)
        self.dq = self.d % (q - 1)
        self.qinv = self._mod_inverse(q, p)

    def encrypt(self, message: int) -> int:
        """RSA加密"""
        if not 0 <= message < self.N:
            raise ValueError(f"消息必须在 [0, {self.N}) 范围内")
        return pow(message, self.e, self.N)

    def decrypt(self, ciphertext: int, use_crt: bool = True) -> int:
        """RSA解密，可选使用中国剩余定理加速"""
        if use_crt:
            # 使用CRT加速（约4倍速度提升）
            m1 = pow(ciphertext, self.dp, self.p)
            m2 = pow(ciphertext, self.dq, self.q)
            h = (self.qinv * (m1 - m2)) % self.p
            return m2 + h * self.q
        else:
            return pow(ciphertext, self.d, self.N)

    def sign(self, message: int) -> int:
        """RSA数字签名"""
        return self.decrypt(message)  # 签名 = 用私钥"解密"

    def verify(self, message: int, signature: int) -> bool:
        """验证RSA签名"""
        return self.encrypt(signature) == message  # 验证 = 用公钥"加密"

    @property
    def public_key(self) -> Tuple[int, int]:
        return (self.N, self.e)

    @property
    def private_key(self) -> Tuple[int, int]:
        return (self.N, self.d)


# 演示代码
if __name__ == "__main__":
    print("=" * 60)
    print("RSA加密算法演示")
    print("=" * 60)

    # 使用小密钥便于演示
    print("\n1. 使用小素数演示 (p=61, q=53)")
    rsa_demo = RSA.__new__(RSA)
    rsa_demo.N = 3233
    rsa_demo.e = 17
    rsa_demo.d = 2753
    rsa_demo.p, rsa_demo.q = 61, 53
    rsa_demo.phi = 3120
    rsa_demo.dp = 2753 % 60
    rsa_demo.dq = 2753 % 52
    rsa_demo.qinv = 38

    message = 65  # ASCII 'A'
    print(f"原始消息: {message}")

    ciphertext = rsa_demo.encrypt(message)
    print(f"加密后: {ciphertext}")

    decrypted = rsa_demo.decrypt(ciphertext)
    print(f"解密后: {decrypted}")
    print(f"验证: {'成功' if decrypted == message else '失败'}")

    # 数字签名演示
    print("\n2. 数字签名演示")
    signature = rsa_demo.sign(message)
    print(f"签名: {signature}")
    is_valid = rsa_demo.verify(message, signature)
    print(f"签名验证: {'有效' if is_valid else '无效'}")

    # 实际RSA（大素数）
    print("\n3. 实际RSA-1024位密钥")
    rsa = RSA(1024)
    print(f"N (模数): {rsa.N.bit_length()} 位")
    print(f"公钥指数 e: {rsa.e}")

    test_msg = 12345678901234567890
    ct = rsa.encrypt(test_msg)
    dt = rsa.decrypt(ct)
    print(f"\n测试消息: {test_msg}")
    print(f"加密/解密验证: {'成功' if dt == test_msg else '失败'}")

```

---

## 六、安全性分析

### 6.1 与因数分解的关系

**定理 6.1**: RSA的安全性等价于大整数分解的困难性（在多项式时间内）。

更精确地说：

- **存在性**: 若能分解 $N = pq$，则可计算 $\phi(N) = (p-1)(q-1)$，进而计算私钥 $d = e^{-1} \mod \phi(N)$
- **逆问题**: 若能从 $(N, e)$ 计算出 $d$，则可高效分解 $N$（Miller 1976）

### 6.2 实际参数选择

| 密钥长度 | 预计安全年限 | 应用场景 | 因数分解难度 |
|----------|-------------|----------|-------------|
| 1024位 | 已不安全 | 不再使用 | ~$2^{80}$ 操作 |
| 2048位 | 2030年前 | 当前标准 | ~$2^{112}$ 操作 |
| 3072位 | 2040年前 | 高安全需求 | ~$2^{128}$ 操作 |
| 4096位 | 长期安全 | 敏感数据 | ~$2^{140}$ 操作 |

**NIST建议**: 2030年后使用至少3072位密钥。

### 6.3 攻击方法简介

#### 6.3.1 时序攻击 (Timing Attack)

**原理**: 测量解密操作的时间来推断私钥信息。

RSA解密使用快速幂算法，不同的指数位导致不同的操作序列，从而泄露时间信息。

**防御**:

- **恒定时间算法**: 使所有操作路径时间相同
- **随机延迟**: 添加随机噪声
- **盲化**: 在计算前对密文进行随机化处理

```python
def blinded_decrypt(c, d, N):
    """盲化解密"""
    # 选择随机数 r
    r = random.randrange(2, N)
    # 计算 r^e mod N
    r_e = pow(r, e, N)
    # 盲化: c' = c * r^e mod N
    c_blind = (c * r_e) % N
    # 解密
    m_blind = pow(c_blind, d, N)
    # 去盲: m = m' * r^(-1) mod N
    r_inv = mod_inverse(r, N)
    return (m_blind * r_inv) % N

```

#### 6.3.2 侧信道攻击

包括功耗分析、电磁辐射分析等，通过物理测量推断密钥信息。

#### 6.3.3 选择密文攻击 (CCA)

**攻击场景**: 攻击者可以请求解密任意密文（除目标密文外）。

**防御**: 使用**填充方案**如OAEP (Optimal Asymmetric Encryption Padding)，将确定性RSA转换为概率性加密。

---

## 七、填充方案：从教科书RSA到安全RSA

### 7.1 PKCS#1 v1.5 填充

```

EB = 00 || 02 || PS || 00 || D

```

其中PS是随机非零字节串。

### 7.2 OAEP (Optimal Asymmetric Encryption Padding)

OAEP使用两个哈希函数 $G$ 和 $H$，提供可证明的安全性（IND-CCA2）。

```

EM = maskedSeed || maskedDB

```

**定理 7.1 (可证明安全)**: 在随机预言机模型下，RSA-OAEP是语义安全的（IND-CPA）且能抵抗选择密文攻击（IND-CCA2）。

---

## 八、与其他数学分支的联系

### 8.1 抽象代数

RSA基于**环论**中的 $(\mathbb{Z}/N\mathbb{Z})^\times$ 乘法群结构。

### 8.2 计算复杂性理论

RSA的安全性依赖于**因数分解 ∉ P** 的假设。若P=NP，则RSA不安全（但这对整个密码学是灾难性的）。

### 8.3 量子计算

**Shor算法**可以在多项式时间内分解大整数，对RSA构成根本性威胁：

$$\text{Shor算法时间复杂度: } O((\log N)^3)$$

这推动了**后量子密码学**的发展，如基于格的加密（NTRU、Kyber）和基于编码的加密（McEliece）。

---

## 九、参考资源

### 原始论文

- Rivest, R. L., Shamir, A., & Adleman, L. (1978). "A method for obtaining digital signatures and public-key cryptosystems." *Communications of the ACM*, 21(2), 120-126.

### 标准教材

- [1] Katz, J., & Lindell, Y. (2014). *Introduction to Modern Cryptography* (2nd ed.). CRC Press.
- [2] Boneh, D., & Shoup, V. (2023). *A Graduate Course in Applied Cryptography*. [在线版本](https://toc.cryptobook.us/)
- [3] Menezes, A. J., van Oorschot, P. C., & Vanstone, S. A. (1996). *Handbook of Applied Cryptography*. CRC Press.

### 标准文档

- [RFC 8017](https://tools.ietf.org/html/rfc8017): RSA Cryptography Specifications Version 2.2
- [NIST FIPS 186-5](https://csrc.nist.gov/publications/detail/fips/186/5/final): Digital Signature Standard (DSS)

### 在线资源

- [Cryptool](https://www.cryptool.org/): 密码学教学软件
- [SageMath](https://www.sagemath.org/): 数论和密码学计算

---

**案例创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
**作者**: FormalMath项目组
**数学学科分类**: 11T71 (Algebraic coding theory; cryptography), 94A60 (Cryptography), 11A41 (Primes)
