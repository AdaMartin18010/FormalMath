---
msc_primary: "00A05"
msc_secondary: ['12Exx', '11Axx', '13Cxx']
---

# RSA加密系统的数论基础

## 应用领域

**学科**: 密码学 / 信息安全 / 数论
**具体应用**: 安全通信、数字签名、HTTPS协议、电子邮件加密
**MSC分类**: 94A60 (Cryptography), 11A41 (Primes), 11T71 (Algebraic coding theory)

---

## 数学概念

### 核心数学工具

1. **模运算**: 同余、剩余类环 $\mathbb{Z}_n$
2. **欧拉定理**: $a^{\phi(n)} \equiv 1 \pmod{n}$
3. **素性测试**: Miller-Rabin、AKS测试
4. **扩展欧几里得算法**: 求模逆元
5. **中国剩余定理**: 大模数分解计算

### 关键定理

- **欧拉定理**: 若 $\gcd(a, n) = 1$，则 $a^{\phi(n)} \equiv 1 \pmod{n}$
- **费马小定理**: 若 $p$ 是素数，则 $a^{p-1} \equiv 1 \pmod{p}$

---

## 问题描述

### 公钥密码学需求

**对称加密的局限**: 密钥分发问题

**公钥加密目标**:

- 任何人可以用公钥加密
- 只有私钥持有者可以解密
- 公钥和私钥数学相关，但从公钥推导私钥计算不可行

### RSA核心思想

**单向函数**: 大整数分解的困难性

- **乘法容易**: 给定 $p, q$，计算 $n = pq$ 容易
- **分解困难**: 给定 $n$，找到 $p, q$ 困难（对大的 $n$）

---

## 数学模型

### RSA密钥生成

**步骤1**: 选择两个大素数 $p, q$（通常1024-4096位）

**步骤2**: 计算

$$n = pq, \quad \phi(n) = (p-1)(q-1)$$

**步骤3**: 选择公钥指数 $e$，满足:

- $1 < e < \phi(n)$
- $\gcd(e, \phi(n)) = 1$

常用 $e = 65537 = 2^{16} + 1$（费马素数，加密速度快）

**步骤4**: 计算私钥指数 $d$:

$$d \equiv e^{-1} \pmod{\phi(n)}$$

即求解 $ed \equiv 1 \pmod{\phi(n)}$

**密钥**:

- **公钥**: $(n, e)$
- **私钥**: $(n, d)$

### 加密与解密

**加密**: 对明文 $m \in [0, n-1]$，密文为

$$c \equiv m^e \pmod{n}$$

**解密**:

$$m \equiv c^d \pmod{n}$$

### 正确性证明

**定理**: 对所有 $m \in [0, n-1]$，$(m^e)^d \equiv m \pmod{n}$

**证明**:

需证 $m^{ed} \equiv m \pmod{n}$

由 $ed \equiv 1 \pmod{\phi(n)}$，存在 $k$ 使得 $ed = 1 + k\phi(n)$

**情况1**: $\gcd(m, n) = 1$

由欧拉定理:

$$m^{ed} = m \cdot m^{k\phi(n)} = m \cdot (m^{\phi(n)})^k \equiv m \cdot 1^k = m \pmod{n}$$

**情况2**: $\gcd(m, n) \neq 1$

设 $m$ 被 $p$ 整除但不被 $q$ 整除：

- $m \equiv 0 \pmod{p}$，所以 $m^{ed} \equiv 0 \equiv m \pmod{p}$
- 由欧拉定理 $m^{q-1} \equiv 1 \pmod{q}$，所以 $m^{ed} \equiv m \pmod{q}$

由中国剩余定理: $m^{ed} \equiv m \pmod{n}$ ∎

---

## 求解过程

### 步骤1：素数生成

**随机素数生成算法**:

1. 随机生成奇数 $k$（指定比特长度）
2. 小素数试除（前1000个素数）
3. Miller-Rabin概率测试（迭代t次，错误概率 $4^{-t}$）
4. 通过则返回 $k$，否则返回步骤1

### 步骤2：扩展欧几里得算法

**目标**: 求 $d$ 使得 $ed \equiv 1 \pmod{\phi(n)}$

**算法**: 给定 $a = e, b = \phi(n)$，求 $x, y$ 使得 $ax + by = \gcd(a,b) = 1$

```

extended_gcd(a, b):
    if b = 0: return (a, 1, 0)
    else:
        (g, x', y') = extended_gcd(b, a mod b)
        return (g, y', x' - floor(a/b) * y')

```

则 $d = x \mod \phi(n)$

### 步骤3：快速模幂运算

**目标**: 高效计算 $m^e \mod n$

**平方-乘算法**:

将指数表示为二进制：$e = (e_k e_{k-1}...e_1 e_0)_2$

```

powmod(m, e, n):
    result = 1
    base = m mod n
    while e > 0:
        if e is odd:
            result = (result * base) mod n
        base = (base * base) mod n
        e = e / 2
    return result

```

复杂度: $O(\log e)$ 次乘法

### 步骤4：中国剩余定理加速解密

**预处理**: 计算

$$d_p = d \mod (p-1), \quad d_q = d \mod (q-1)$$
$$q_{inv} = q^{-1} \mod p$$

**解密**:

$$m_p = c^{d_p} \mod p, \quad m_q = c^{d_q} \mod q$$
$$h = q_{inv}(m_p - m_q) \mod p$$
$$m = m_q + hq$$

速度提升约4倍。

---

## 结果分析

### 安全强度

| 模数长度 | 估计安全性 | 推荐用途 |
|----------|-----------|----------|
| 1024位 | ~80位 | 遗留系统 |
| 2048位 | ~112位 | 当前标准（2020+） |
| 3072位 | ~128位 | 高安全需求 |
| 4096位 | ~140位 | 长期安全 |

### 已知攻击

| 攻击类型 | 条件 | 防御措施 |
|----------|------|----------|
| **因数分解** | 通用攻击 | 足够大的 $n$ |
| **共模攻击** | 相同 $n$，不同 $e$ | 每个用户独立密钥 |
| **低指数攻击** | $e$ 太小，广播场景 | $e \geq 65537$，随机填充 |
| **边信道攻击** | 时间/功耗分析 | 常数时间实现 |
| **Bleichenbacher** | PKCS#1 v1.5填充 | 使用OAEP填充 |

### 实际应用

**TLS/SSL握手**:

1. 客户端生成预主密钥
2. 用服务器公钥加密
3. 服务器私钥解密
4. 双方派生会话密钥

**数字签名**:

- **签名**: $s \equiv h(m)^d \pmod{n}$
- **验证**: $h(m) \stackrel{?}{\equiv} s^e \pmod{n}$

---

## 参考资源

### 原始论文

- **Rivest, R.L., Shamir, A., & Adleman, L.** (1978). "A method for obtaining digital signatures and public-key cryptosystems". *Commun. ACM*.

### 推荐教材

- **Stinson, D.R. & Paterson, M.** *Cryptography: Theory and Practice*.
- **Katz, J. & Lindell, Y.** *Introduction to Modern Cryptography*.
- **Hoffstein, J., Pipher, J., & Silverman, J.H.** *An Introduction to Mathematical Cryptography*.

---

**创建日期**: 2026年4月2日
**最后更新**: 2026年4月2日
