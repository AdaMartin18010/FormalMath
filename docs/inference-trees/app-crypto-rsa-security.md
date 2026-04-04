---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# RSA安全性推导链

## 概述
本推理树展示RSA密码系统的安全性基础，包括大整数分解困难性、RSA问题、语义安全、OAEP填充、侧信道防护等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph RSA基础
        A1[密钥生成<br/>p,q素数, n=pq] --> A2[欧拉函数<br/>φn = p-1q-1]
        A2 --> A3[密钥选择<br/>e,d: ed ≡ 1 mod φn]
        A3 --> A4[RSA函数<br/>fx = x^e mod n]
    end
    
    subgraph 单向性
        A4 --> B1[求逆困难<br/>f^{-1}y = y^d mod n]
        B1 --> B2[RSA问题<br/>RSA-INV]
        B2 --> B3[分解假设<br/>FACT ⇒ RSA]
        B3 --> B4[严格单向<br/>无多项式逆]
    end
    
    subgraph 语义安全
        B2 --> C1[确定性加密<br/>无IND-CPA安全]
        C1 --> C2[CPA攻击<br/>选择明文攻击]
        C2 --> C3[随机化填充<br/>OAEP]
        C3 --> C4[IND-CCA2<br/>自适应选择密文]
    end
    
    subgraph OAEP填充
        C3 --> D1[Feistel网络<br/>两轮]
        D1 --> D2[随机预言机<br/>G, H]
        D2 --> D3[填充结构<br/>s||t]

        D3 --> D4[可证明安全<br/>ROM下IND-CCA2]
    end
    
    subgroup 侧信道防护
        B1 --> E1[时序攻击<br/>模幂运算时间]
        E1 --> E2[ Montgomery ladder<br/>固定时间]
        E2 --> E3[幂盲化<br/>d' = d + r·φn]
        E3 --> E4[消息盲化<br/>盲签名]
    end
    
    subgraph 进阶分析
        B3 --> F1[Coppersmith<br/>部分信息泄露]
        F1 --> F2[Wiener攻击<br/>d < n^{1/4}/3]
        F2 --> F3[LLL算法<br/>格基约化]
        F3 --> F4[部分私钥恢复<br/>已知MSB/LSB]
    end
    
    style B2 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px
    style C4 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style D4 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style E4 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：RSA算法基础

**密钥生成**：
1. 选择两个大素数 $p, q$（通常各$1024$位或更大）
2. 计算 $n = p \cdot q$（模数，公开）
3. 计算 $\phi(n) = (p-1)(q-1)$（欧拉函数，保密）
4. 选择公钥指数 $e$（常用 $e = 3, 17, 65537$）
5. 计算私钥 $d$：$e \cdot d \equiv 1 \pmod{\phi(n)}$

**加密**：$c = m^e \mod n$

**解密**：$m = c^d \mod n$

**正确性证明**：

由欧拉定理，若 $\gcd(m, n) = 1$：
$$m^{\phi(n)} \equiv 1 \pmod{n}$$

因此：
$$(m^e)^d = m^{ed} = m^{1 + k\phi(n)} = m \cdot (m^{\phi(n)})^k \equiv m \pmod{n}$$

### 第二步：RSA问题与单向性

**RSA问题（RSA-INV）**：给定 $(n, e, y)$，求 $x$ 使得 $y = x^e \mod n$。

**大整数分解问题（FACT）**：给定 $n$，求素因子 $p, q$。

**定理**：$FACT \Rightarrow RSA$，即若可分解 $n$，则可解RSA问题。

**证明**：
1. 分解 $n = p \cdot q$
2. 计算 $\phi(n) = (p-1)(q-1)$
3. 用扩展欧几里得算法求 $d = e^{-1} \mod \phi(n)$
4. 计算 $x = y^d \mod n$

**开放问题**：$RSA \stackrel{?}{\Rightarrow} FACT$，即RSA是否等价于分解尚无证明。

### 第三步：语义安全性

**确定性RSA的问题**：
- 相同明文总是产生相同密文
- 攻击者可检查密文是否对应猜测的明文
- 不满足IND-CPA（不可区分性）安全

**IND-CPA安全定义**：

对任意PPT敌手 $\mathcal{A}$：
$$\left|\Pr[\mathcal{A}(pk, c_b) = b] - \frac{1}{2}\right| \leq \text{negl}(n)$$

其中 $c_b = \text{Enc}(pk, m_b)$，$m_0, m_1$ 由敌手选择。

**解决方案**：随机化填充方案

### 第四步：OAEP填充方案

**OAEP（Optimal Asymmetric Encryption Padding）**：

构造：
$$\text{OAEP}(m, r) = s \| t$$

其中：
- $r$：随机串（$k_0$ 位）
- $G$: 随机预言机（扩展函数）
- $H$: 随机预言机（压缩函数）
- $s = (m \| 0^{k_1}) \oplus G(r)$

- $t = r \oplus H(s)$

**加密**：$c = \text{RSA}(\text{OAEP}(m, r)) = (\text{OAEP}(m, r))^e \mod n$

**安全性定理（Fujisaki-Okamoto-Stern-Pointcheval）**：

OAEP-RSA在随机预言机模型（ROM）下是IND-CCA2安全的。

### 第五步：侧信道攻击与防护

**时序攻击（Kocher, 1996）**：

简单模幂算法：

```

result = 1
for each bit of d:
    if bit == 1:
        result = result * base mod n
    base = base^2 mod n

```

比特为1时多一次乘法，可通过计时推断私钥比特。

**防护**：

1. **Montgomery Ladder**（固定时间）：

```

R[0] = 1
R[1] = base
for i from k-1 downto 0:
    R[1-bit_i] = R[0] * R[1] mod n
    R[bit_i] = R[bit_i]^2 mod n

```

2. **幂盲化**：计算 $c^{d + r\phi(n)} \mod n = c^d \mod n$

3. **消息盲化**：$c' = c \cdot r^e \mod n$，解密后除以 $r$

### 第六步：高级攻击方法

**Wiener攻击（1990）**：

若 $d < n^{0.25}/3$，可利用连分数恢复 $d$。

**原理**：$ed - k\phi(n) = 1$，且 $\phi(n) \approx n$。

因此 $\frac{e}{n} \approx \frac{k}{d}$，用连分数展开可找到 $\frac{k}{d}$。

**Coppersmith方法**：

若已知私钥 $d$ 的高位或低位（约一半），可用格基约化（LLL算法）恢复完整私钥。

**部分密钥暴露攻击**：

- 已知 $d \mod p-1$：可分解 $n$
- 已知 $d \mod q-1$：可分解 $n$

---

## RSA安全参数建议

| 安全级别 | 模数长度 | 素数长度 | 推荐指数 |
|----------|----------|----------|----------|
| 80-bit | 1024 | 512 | 65537 |
| 112-bit | 2048 | 1024 | 65537 |
| 128-bit | 3072 | 1536 | 65537 |
| 256-bit | 15360 | 7680 | 65537 |

---

## 依赖关系图

```

数论基础 ← 模运算、欧拉定理
    ↓
RSA算法构造
    ↓
单向函数 ← 计算复杂性
    ↓
语义安全性 ← 可证明安全
    ↓
OAEP填充 ← 随机预言机
    ↓
IND-CCA2安全
    ↓
侧信道防护 ← 实现安全

```

---

## 关键概念汇总

| 概念 | 定义 | 意义 |
|------|------|------|
| RSA问题 | 求 $e$ 次根模 $n$ | 单向性基础 |
| IND-CPA | 选择明文不可区分 | 基本安全 |
| IND-CCA2 | 自适应选择密文 | 强安全 |
| OAEP | 最优非对称填充 | 可证明安全 |
| ROM | 随机预言机模型 | 证明工具 |

---

## 参考

- Rivest, R. L., Shamir, A., & Adleman, L. (1978). "A Method for Obtaining Digital Signatures and Public-Key Cryptosystems"
- Bellare, M. & Rogaway, P. (1995). "Optimal Asymmetric Encryption"
- Fujisaki, E., et al. (2004). "RSA-OAEP is Secure under the RSA Assumption"
- Kocher, P. (1996). "Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS"
- Boneh, D. & Durfee, G. (1999). "Cryptanalysis of RSA with Private Key d Less than $N^{0.292}$"

---

*生成时间：2026年4月*
