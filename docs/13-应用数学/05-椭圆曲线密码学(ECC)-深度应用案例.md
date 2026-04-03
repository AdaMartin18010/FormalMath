---
msc_primary: "00A69"
msc_secondary: "97Mxx"
---

# 椭圆曲线密码学(ECC)深度应用案例

> **数学主题**: 代数几何、有限域上的椭圆曲线、计算数论
> **MSC分类**: 11G20 (有限域上的曲线), 94A60 (密码学), 14H52 (椭圆曲线)
> **国际对齐**: NIST FIPS 186-5, SEC1/SEC2, ANSI X9.62, RFC 7748 (Curve25519)

---

## 1. 引言

椭圆曲线密码学(Elliptic Curve Cryptography, ECC)是现代密码学的核心支柱之一。与基于整数分解(RSA)或离散对数(DSA)的传统密码系统相比，ECC在提供同等安全级别的情况下，使用更短的密钥长度，计算效率更高。

### 1.1 历史背景

- **1985**: Neal Koblitz和Victor Miller独立提出将椭圆曲线用于密码学
- **1990s**: ECC标准化进程开始（ANSI、IEEE、ISO/IEC、NIST）
- **2009**: 比特币采用secp256k1曲线
- **2014**: IETF发布Curve25519/Ed25519标准(RFC 7748/8032)
- **2023**: NIST发布FIPS 186-5，正式推荐ECC标准

---

## 2. 数学基础

### 2.1 椭圆曲线的定义

**定义 2.1** (Weierstrass方程)：设 $\mathbb{K}$ 是一个域（特征 $\neq 2, 3$），**椭圆曲线** $E$ 是射影平面 $\mathbb{P}^2(\mathbb{K})$ 中由以下Weierstrass方程定义的曲线：

$$E: y^2 = x^3 + ax + b$$

其中 $a, b \in \mathbb{K}$，且判别式 $\Delta = -16(4a^3 + 27b^2) \neq 0$（保证曲线非奇异，即无自交点或尖点）。

**定义 2.2** (椭圆曲线上的点集)：椭圆曲线 $E$ 上的**有理点集**为：

$$E(\mathbb{K}) = \{(x, y) \in \mathbb{K}^2 : y^2 = x^3 + ax + b\} \cup \{\mathcal{O}\}$$

其中 $\mathcal{O}$ 是**无穷远点**（单位元）。

### 2.2 群结构

**定理 2.3** (Mordell-Weil定理，有限域版本)：$E(\mathbb{K})$ 在适当的加法运算下构成一个有限阿贝尔群。

**点加法规则** (弦切法则)：设 $P = (x_1, y_1)$，$Q = (x_2, y_2)$ 是 $E(\mathbb{K})$ 上的点。

**情况1**: $P \neq Q$ 且 $x_1 \neq x_2$ (弦法则)
$$\lambda = \frac{y_2 - y_1}{x_2 - x_1}, \quad x_3 = \lambda^2 - x_1 - x_2, \quad y_3 = \lambda(x_1 - x_3) - y_1$$

**情况2**: $P = Q$ 且 $y_1 \neq 0$ (切线法则，点加倍)
$$\lambda = \frac{3x_1^2 + a}{2y_1}, \quad x_3 = \lambda^2 - 2x_1, \quad y_3 = \lambda(x_1 - x_3) - y_1$$

**情况3**: $x_1 = x_2$ 且 $y_1 = -y_2$ (逆元)
$$P + Q = \mathcal{O}$$

**定理 2.4** (Hasse定理)：设 $E$ 是定义在 $\mathbb{F}_q$ 上的椭圆曲线，则：
$$|q + 1 - \#E(\mathbb{F}_q)| \leq 2\sqrt{q}$$

即椭圆曲线上的点数 $\#E(\mathbb{F}_q)$ 满足 $q + 1 - 2\sqrt{q} \leq \#E(\mathbb{F}_q) \leq q + 1 + 2\sqrt{q}$。

### 2.3 椭圆曲线离散对数问题 (ECDLP)

**定义 2.5** (ECDLP)：设 $E$ 是定义在有限域 $\mathbb{F}_q$ 上的椭圆曲线，$P \in E(\mathbb{F}_q)$ 是一个 $n$ 阶点，$Q \in \langle P \rangle$。椭圆曲线离散对数问题是指：给定 $P$ 和 $Q$，求整数 $k \in [0, n-1]$ 使得 $Q = kP$。

**安全假设**: ECDLP在一般椭圆曲线上是计算困难的。目前已知的最佳通用算法是Pollard's rho算法，时间复杂度为 $O(\sqrt{n})$。

**定理 2.6** (Pohlig-Hellman简化)：若群的阶有小的素因子，则ECDLP可分解为子群上的问题。因此，密码学应用要求群的阶有一个大的素因子。

---

## 3. 标准曲线参数

### 3.1 secp256k1 (比特币曲线)

secp256k1是SECG标准中的曲线，被比特币和以太坊采用。

**曲线方程**: $y^2 = x^3 + 7$ (即 $a=0, b=7$)

**域参数**:

- 素数域：$p = 2^{256} - 2^{32} - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1$
- 阶：$n = 2^{256} - 43242038656565665640554032518407253395635423895748233932554065773022197057957$
- 余因子：$h = 1$

**基点** $G = (G_x, G_y)$:

```
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
```

### 3.2 Curve25519 (蒙哥马利曲线)

Curve25519由Daniel J. Bernstein设计，提供120-bit安全级别，具有抗侧信道攻击特性。

**曲线方程**: $y^2 = x^3 + 486662x^2 + x$ (蒙哥马利形式)

**域参数**:

- $p = 2^{255} - 19$
- 基点 $x$ 坐标：$x = 9$

**优势**:

- 快速蒙哥马利阶梯算法
- 无需验证点是否在曲线上（ $x$ 坐标足够）
- 常数时间实现，抗时间侧信道攻击

### 3.3 NIST P-256 (secp256r1)

NIST推荐的标准曲线，广泛应用于TLS、SSH等协议。

**曲线方程**: $y^2 = x^3 - 3x + b$

**域参数**: 见NIST FIPS 186-5附录D.1.2.3

---

## 4. 核心算法实现

### 4.1 纯Python椭圆曲线实现

```python
"""
椭圆曲线密码学(ECC) - 纯Python实现
支持secp256k1、Curve25519等标准曲线

参考: SEC1 v2.0, RFC 7748, NIST FIPS 186-5
"""

import hashlib
import secrets
from typing import Optional, Tuple

# ============================================================================
# 第1部分：有限域算术
# ============================================================================

class FiniteField:
    """素域 F_p 上的元素"""

    def __init__(self, value: int, prime: int):
        self.prime = prime
        self.value = value % prime

    def __add__(self, other: 'FiniteField') -> 'FiniteField':
        if self.prime != other.prime:
            raise ValueError("Different fields")
        return FiniteField((self.value + other.value) % self.prime, self.prime)

    def __sub__(self, other: 'FiniteField') -> 'FiniteField':
        if self.prime != other.prime:
            raise ValueError("Different fields")
        return FiniteField((self.value - other.value) % self.prime, self.prime)

    def __mul__(self, other) -> 'FiniteField':
        if isinstance(other, FiniteField):
            if self.prime != other.prime:
                raise ValueError("Different fields")
            return FiniteField((self.value * other.value) % self.prime, self.prime)
        elif isinstance(other, int):
            return FiniteField((self.value * other) % self.prime, self.prime)
        else:
            return NotImplemented

    def __rmul__(self, other: int) -> 'FiniteField':
        return self.__mul__(other)

    def __pow__(self, exp: int) -> 'FiniteField':
        # 快速幂算法
        return FiniteField(pow(self.value, exp, self.prime), self.prime)

    def __truediv__(self, other: 'FiniteField') -> 'FiniteField':
        """除法 = 乘以乘法逆元"""
        if self.prime != other.prime:
            raise ValueError("Different fields")
        return self * other.inverse()

    def inverse(self) -> 'FiniteField':
        """扩展欧几里得算法求乘法逆元"""
        if self.value == 0:
            raise ZeroDivisionError("Cannot invert zero")
        # Fermat小定理: a^(p-2) ≡ a^(-1) (mod p)
        return FiniteField(pow(self.value, self.prime - 2, self.prime), self.prime)

    def __eq__(self, other) -> bool:
        if not isinstance(other, FiniteField):
            return False
        return self.prime == other.prime and self.value == other.value

    def __ne__(self, other) -> bool:
        return not self.__eq__(other)

    def __repr__(self) -> str:
        return f"FF({self.value:#x})"


# ============================================================================
# 第2部分：椭圆曲线点
# ============================================================================

class ECPoint:
    """
    椭圆曲线上的点 (Weierstrass形式: y^2 = x^3 + ax + b)
    """

    def __init__(self, x: Optional[FiniteField], y: Optional[FiniteField],
                 a: int, b: int, prime: int, is_infinity: bool = False):
        self.prime = prime
        self.a = FiniteField(a % prime, prime)
        self.b = FiniteField(b % prime, prime)

        if is_infinity:
            self.x = None
            self.y = None
            self.is_infinity = True
        else:
            self.x = x
            self.y = y
            self.is_infinity = False
            # 验证点在曲线上
            if not self._is_on_curve():
                raise ValueError("Point is not on the curve")

    def _is_on_curve(self) -> bool:
        if self.is_infinity:
            return True
        # y^2 = x^3 + ax + b
        left = self.y ** 2
        right = self.x ** 3 + self.a * self.x + self.b
        return left == right

    def __add__(self, other: 'ECPoint') -> 'ECPoint':
        if self.is_infinity:
            return other
        if other.is_infinity:
            return self
        if self.x == other.x:
            if self.y == other.y:
                if self.y.value == 0:
                    # P + (-P) = O，当y=0时2P=O
                    return ECPoint(None, None, self.a.value, self.b.value, self.prime, True)
                # 点加倍 (切线法则)
                return self._double()
            else:
                # P + (-P) = O
                return ECPoint(None, None, self.a.value, self.b.value, self.prime, True)

        # 弦法则: 计算斜率
        slope = (other.y - self.y) / (other.x - self.x)
        x3 = slope ** 2 - self.x - other.x
        y3 = slope * (self.x - x3) - self.y

        return ECPoint(x3, y3, self.a.value, self.b.value, self.prime)

    def _double(self) -> 'ECPoint':
        """点加倍: 2P"""
        if self.is_infinity or self.y.value == 0:
            return ECPoint(None, None, self.a.value, self.b.value, self.prime, True)

        # 切线斜率: (3x^2 + a) / (2y)
        slope = (3 * (self.x ** 2) + self.a) / (2 * self.y)
        x3 = slope ** 2 - 2 * self.x
        y3 = slope * (self.x - x3) - self.y

        return ECPoint(x3, y3, self.a.value, self.b.value, self.prime)

    def __rmul__(self, scalar: int) -> 'ECPoint':
        """标量乘法: kP (使用双倍-加法算法)"""
        if scalar < 0:
            raise ValueError("Negative scalar not supported")

        result = ECPoint(None, None, self.a.value, self.b.value, self.prime, True)
        addend = self

        # 二进制展开方法
        while scalar:
            if scalar & 1:
                result = result + addend
            addend = addend._double()
            scalar >>= 1

        return result

    def __neg__(self) -> 'ECPoint':
        """取逆元: -P = (x, -y)"""
        if self.is_infinity:
            return self
        return ECPoint(self.x, FiniteField((-self.y.value) % self.prime, self.prime),
                      self.a.value, self.b.value, self.prime)

    def __sub__(self, other: 'ECPoint') -> 'ECPoint':
        return self + (-other)

    def __eq__(self, other) -> bool:
        if not isinstance(other, ECPoint):
            return False
        if self.is_infinity and other.is_infinity:
            return True
        if self.is_infinity != other.is_infinity:
            return False
        return (self.prime == other.prime and
                self.a == other.a and self.b == other.b and
                self.x == other.x and self.y == other.y)

    def __repr__(self) -> str:
        if self.is_infinity:
            return "O (无穷远点)"
        return f"ECPoint({self.x.value:#x}, {self.y.value:#x})"

    def to_bytes(self, compressed: bool = False) -> bytes:
        """序列化为字节串 (SEC1格式)"""
        if self.is_infinity:
            return b'\x00'

        x_bytes = self.x.value.to_bytes((self.prime.bit_length() + 7) // 8, 'big')

        if compressed:
            # 压缩格式: 0x02 (y偶数) 或 0x03 (y奇数) + x
            prefix = b'\x02' if self.y.value % 2 == 0 else b'\x03'
            return prefix + x_bytes
        else:
            # 未压缩格式: 0x04 + x + y
            y_bytes = self.y.value.to_bytes((self.prime.bit_length() + 7) // 8, 'big')
            return b'\x04' + x_bytes + y_bytes


# ============================================================================
# 第3部分：标准曲线定义
# ============================================================================

class CurveParams:
    """椭圆曲线参数"""

    def __init__(self, name: str, p: int, a: int, b: int,
                 gx: int, gy: int, n: int, h: int = 1):
        self.name = name
        self.p = p
        self.a = a
        self.b = b
        self.gx = gx
        self.gy = gy
        self.n = n
        self.h = h

    def generator(self) -> ECPoint:
        """返回基点G"""
        return ECPoint(
            FiniteField(self.gx, self.p),
            FiniteField(self.gy, self.p),
            self.a, self.b, self.p
        )


# secp256k1参数 (比特币曲线)
SECP256K1 = CurveParams(
    name="secp256k1",
    p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    a=0x0000000000000000000000000000000000000000000000000000000000000000,
    b=0x0000000000000000000000000000000000000000000000000000000000000007,
    gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
    n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    h=1
)

# secp256r1参数 (NIST P-256)
SECP256R1 = CurveParams(
    name="secp256r1",
    p=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
    a=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC,
    b=0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
    gx=0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
    gy=0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
    n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
    h=1
)


# ============================================================================
# 第4部分：ECDH密钥交换
# ============================================================================

class ECDH:
    """
    椭圆曲线Diffie-Hellman (ECDH) 密钥交换

    协议流程:
    1. Alice生成私钥d_A，计算公钥Q_A = d_A * G
    2. Bob生成私钥d_B，计算公钥Q_B = d_B * G
    3. Alice计算共享密钥: S = d_A * Q_B = d_A * d_B * G
    4. Bob计算共享密钥: S = d_B * Q_A = d_B * d_A * G

    安全性基于ECDLP: 从Q_A或Q_B恢复d_A或d_B是困难的
    """

    def __init__(self, curve: CurveParams):
        self.curve = curve
        self._private_key: Optional[int] = None
        self._public_key: Optional[ECPoint] = None

    def generate_keypair(self) -> Tuple[int, ECPoint]:
        """生成密钥对 (d, Q=d*G)"""
        # 生成随机私钥 [1, n-1]
        self._private_key = secrets.randbelow(self.curve.n - 1) + 1
        G = self.curve.generator()
        self._public_key = self._private_key * G
        return self._private_key, self._public_key

    def compute_shared_secret(self, other_public: ECPoint) -> bytes:
        """
        计算共享密钥
        返回: x坐标的哈希值 (可扩展为使用KDF)
        """
        if self._private_key is None:
            raise ValueError("Private key not generated")

        # 计算 S = d_A * Q_B
        shared_point = self._private_key * other_public

        if shared_point.is_infinity:
            raise ValueError("Shared point is infinity - invalid public key")

        # 使用x坐标作为共享密钥素材
        x_bytes = shared_point.x.value.to_bytes(
            (self.curve.p.bit_length() + 7) // 8, 'big'
        )

        # 使用SHA-256派生最终密钥
        return hashlib.sha256(x_bytes).digest()


# ============================================================================
# 第5部分：ECDSA签名
# ============================================================================

class ECDSA:
    """
    椭圆曲线数字签名算法 (ECDSA)

    参考: SEC1 v2.0 Section 4.1, FIPS 186-5 Section 6

    签名生成:
    1. 选择随机数 k ∈ [1, n-1]
    2. 计算 R = k*G = (x_R, y_R), r = x_R mod n
    3. 计算 s = k^(-1) * (H(m) + d*r) mod n
    4. 签名 = (r, s)

    签名验证:
    1. 验证 r, s ∈ [1, n-1]
    2. 计算 w = s^(-1) mod n
    3. 计算 u1 = H(m) * w mod n, u2 = r * w mod n
    4. 计算 R' = u1*G + u2*Q = (x_R', y_R')
    5. 验证 r ≡ x_R' (mod n)
    """

    def __init__(self, curve: CurveParams):
        self.curve = curve
        self.G = curve.generator()

    def _hash_message(self, message: bytes) -> int:
        """对消息进行哈希，返回整数"""
        h = hashlib.sha256(message).digest()
        h_int = int.from_bytes(h, 'big')
        # 如果哈希值大于n，取模
        if h_int >= self.curve.n:
            h_int %= self.curve.n
        return h_int if h_int != 0 else 1  # 确保不为0

    def sign(self, private_key: int, message: bytes,
             k: Optional[int] = None) -> Tuple[int, int]:
        """
        生成ECDSA签名

        Args:
            private_key: 签名者私钥 d ∈ [1, n-1]
            message: 待签名消息
            k: 临时密钥 (可选，随机生成更安全)

        Returns:
            (r, s): 签名对
        """
        if not (1 <= private_key < self.curve.n):
            raise ValueError("Invalid private key")

        # 计算消息哈希
        e = self._hash_message(message)
        n = self.curve.n

        while True:
            # 生成随机临时密钥
            if k is None:
                k = secrets.randbelow(n - 1) + 1

            if not (1 <= k < n):
                continue

            # 计算 R = k*G
            R = k * self.G
            r = R.x.value % n

            if r == 0:
                continue  # r不能为0

            # 计算 s = k^(-1) * (e + d*r) mod n
            k_inv = pow(k, -1, n)
            s = (k_inv * (e + private_key * r)) % n

            if s == 0:
                continue  # s不能为0

            return (r, s)

    def verify(self, public_key: ECPoint, message: bytes,
               signature: Tuple[int, int]) -> bool:
        """
        验证ECDSA签名

        Args:
            public_key: 签名者公钥 Q = d*G
            message: 待验证消息
            signature: (r, s) 签名对

        Returns:
            bool: 签名是否有效
        """
        r, s = signature
        n = self.curve.n

        # 验证 r, s 范围
        if not (1 <= r < n) or not (1 <= s < n):
            return False

        # 计算消息哈希
        e = self._hash_message(message)

        # 计算 w = s^(-1) mod n
        w = pow(s, -1, n)

        # 计算 u1 = e*w mod n, u2 = r*w mod n
        u1 = (e * w) % n
        u2 = (r * w) % n

        # 计算 R' = u1*G + u2*Q
        R_prime = u1 * self.G + u2 * public_key

        if R_prime.is_infinity:
            return False

        # 验证 r ≡ x_R' (mod n)
        return r == (R_prime.x.value % n)


# ============================================================================
# 第6部分：测试与演示
# ============================================================================

def test_finite_field():
    """测试有限域算术"""
    print("=" * 60)
    print("测试有限域算术")
    print("=" * 60)

    p = 17
    a = FiniteField(3, p)
    b = FiniteField(5, p)

    print(f"p = {p}")
    print(f"a = {a.value}, b = {b.value}")
    print(f"a + b = {(a + b).value}")
    print(f"a * b = {(a * b).value}")
    print(f"a / b = {(a / b).value}")
    print(f"b^(-1) = {b.inverse().value}")
    print(f"验证: b * b^(-1) = {(b * b.inverse()).value}")
    print()


def test_ec_point_operations():
    """测试椭圆曲线点运算"""
    print("=" * 60)
    print("测试椭圆曲线点运算 (y^2 = x^3 + 2x + 2 mod 17)")
    print("=" * 60)

    p = 17
    a, b = 2, 2

    # 曲线 y^2 = x^3 + 2x + 2
    # 点 P = (5, 1): 1^2 = 1, 5^3 + 2*5 + 2 = 125 + 10 + 2 = 137 ≡ 1 (mod 17) ✓
    P = ECPoint(FiniteField(5, p), FiniteField(1, p), a, b, p)
    print(f"P = {P}")

    # 点 Q = (6, 3): 3^2 = 9, 6^3 + 2*6 + 2 = 216 + 12 + 2 = 230 ≡ 9 (mod 17) ✓
    Q = ECPoint(FiniteField(6, p), FiniteField(3, p), a, b, p)
    print(f"Q = {Q}")

    # 点加法
    R = P + Q
    print(f"P + Q = {R}")

    # 点加倍
    R2 = P._double()
    print(f"2P = {R2}")

    # 标量乘法
    S = 3 * P
    print(f"3P = {S}")

    # 验证群的结合律
    left = (P + Q) + S
    right = P + (Q + S)
    print(f"结合律验证: (P+Q)+S == P+(Q+S): {left == right}")
    print()


def test_secp256k1():
    """测试secp256k1曲线"""
    print("=" * 60)
    print("测试secp256k1曲线 (比特币曲线)")
    print("=" * 60)

    curve = SECP256K1
    print(f"曲线: {curve.name}")
    print(f"p = {curve.p:#x}")
    print(f"n = {curve.n:#x}")

    G = curve.generator()
    print(f"基点G: ({curve.gx:#x}, ...)")

    # 验证G在曲线上
    print(f"G在曲线上: {G._is_on_curve()}")

    # 验证n*G = O
    O = curve.n * G
    print(f"n*G = 无穷远点: {O.is_infinity}")

    # 测试标量乘法
    k = 12345678901234567890
    P = k * G
    print(f"k*G = {P}")
    print()


def test_ecdh():
    """测试ECDH密钥交换"""
    print("=" * 60)
    print("ECDH密钥交换演示")
    print("=" * 60)

    curve = SECP256K1

    # Alice生成密钥对
    alice = ECDH(curve)
    d_a, Q_a = alice.generate_keypair()
    print(f"Alice私钥: {d_a:#x}")
    print(f"Alice公钥: ({Q_a.x.value:#x}, ...)")

    # Bob生成密钥对
    bob = ECDH(curve)
    d_b, Q_b = bob.generate_keypair()
    print(f"Bob私钥: {d_b:#x}")
    print(f"Bob公钥: ({Q_b.x.value:#x}, ...)")

    # 交换公钥并计算共享密钥
    shared_alice = alice.compute_shared_secret(Q_b)
    shared_bob = bob.compute_shared_secret(Q_a)

    print(f"Alice计算的共享密钥: {shared_alice.hex()}")
    print(f"Bob计算的共享密钥: {shared_bob.hex()}")
    print(f"密钥匹配: {shared_alice == shared_bob}")
    print()


def test_ecdsa():
    """测试ECDSA签名"""
    print("=" * 60)
    print("ECDSA签名演示")
    print("=" * 60)

    curve = SECP256K1
    ecdsa = ECDSA(curve)

    # 生成密钥对
    private_key = secrets.randbelow(curve.n - 1) + 1
    public_key = private_key * curve.generator()

    print(f"私钥: {private_key:#x}")
    print(f"公钥: ({public_key.x.value:#x}, ...)")

    # 待签名消息
    message = b"Hello, ECC! This is a test message."
    print(f"消息: {message.decode()}")

    # 签名
    r, s = ecdsa.sign(private_key, message)
    print(f"签名 r: {r:#x}")
    print(f"签名 s: {s:#x}")

    # 验证
    valid = ecdsa.verify(public_key, message, (r, s))
    print(f"签名验证: {'通过 ✓' if valid else '失败 ✗'}")

    # 尝试伪造签名（篡改消息）
    fake_message = b"Fake message"
    valid_fake = ecdsa.verify(public_key, fake_message, (r, s))
    print(f"伪造消息验证: {'通过' if valid_fake else '失败 ✓'}")
    print()


def test_ecdsa_with_known_k():
    """
    使用已知k值的测试 - 演示密钥泄露攻击

    警告: 实际应用中必须使用随机k!
    如果重复使用k，攻击者可恢复私钥:
    s1 = k^(-1) * (h1 + d*r) mod n
    s2 = k^(-1) * (h2 + d*r) mod n
    => k = (h1 - h2) / (s1 - s2) mod n
    => d = (s1*k - h1) / r mod n
    """
    print("=" * 60)
    print("ECDSA - k重用攻击演示")
    print("=" * 60)

    curve = SECP256K1
    ecdsa = ECDSA(curve)

    private_key = secrets.randbelow(curve.n - 1) + 1

    # 使用相同的k签名两条消息 (危险!)
    k = secrets.randbelow(curve.n - 1) + 1
    msg1 = b"Message 1"
    msg2 = b"Message 2"

    r1, s1 = ecdsa.sign(private_key, msg1, k)
    r2, s2 = ecdsa.sign(private_key, msg2, k)

    print(f"消息1签名: (r={r1:#x}, s={s1:#x})")
    print(f"消息2签名: (r={r2:#x}, s={s2:#x})")
    print(f"注意: r1 == r2: {r1 == r2}")

    # 攻击者恢复私钥
    n = curve.n
    h1 = ecdsa._hash_message(msg1)
    h2 = ecdsa._hash_message(msg2)

    # k = (h1 - h2) / (s1 - s2) mod n
    k_recovered = ((h1 - h2) * pow((s1 - s2) % n, -1, n)) % n
    print(f"恢复的k值: {k_recovered:#x}")
    print(f"k值匹配: {k == k_recovered}")

    # d = (s1*k - h1) / r mod n
    d_recovered = ((s1 * k_recovered - h1) * pow(r1, -1, n)) % n
    print(f"恢复的私钥: {d_recovered:#x}")
    print(f"私钥匹配: {private_key == d_recovered}")
    print("\n警告: 永远不要重复使用随机数k!")
    print()


def run_all_tests():
    """运行所有测试"""
    test_finite_field()
    test_ec_point_operations()
    test_secp256k1()
    test_ecdh()
    test_ecdsa()
    test_ecdsa_with_known_k()

    print("=" * 60)
    print("所有测试完成!")
    print("=" * 60)


if __name__ == "__main__":
    run_all_tests()
```

### 4.2 使用标准库的完整实现

```python
"""
使用标准库(ecdsa, cryptography)的ECC实现
提供生产级安全性参考
"""

# 安装: pip install ecdsa cryptography

def demo_ecdsa_with_library():
    """使用ecdsa库的演示"""
    try:
        import ecdsa
        import hashlib

        print("=" * 60)
        print("使用ecdsa库的ECC演示")
        print("=" * 60)

        # 使用secp256k1曲线
        curve = ecdsa.SECP256k1

        # 生成密钥对
        private_key = ecdsa.SigningKey.generate(curve=curve)
        public_key = private_key.get_verifying_key()

        print(f"私钥: {private_key.to_string().hex()}")
        print(f"公钥: {public_key.to_string().hex()}")

        # 签名
        message = b"Hello, World!"
        signature = private_key.sign(message, hashfunc=hashlib.sha256)
        print(f"签名: {signature.hex()}")

        # 验证
        try:
            public_key.verify(signature, message, hashfunc=hashlib.sha256)
            print("验证: 通过 ✓")
        except ecdsa.BadSignatureError:
            print("验证: 失败 ✗")

        # 序列化
        pem_private = private_key.to_pem()
        pem_public = public_key.to_pem()
        print(f"\n私钥PEM格式:\n{pem_private.decode()}")

    except ImportError:
        print("请安装ecdsa库: pip install ecdsa")


def demo_cryptography_library():
    """使用cryptography库的演示"""
    try:
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.hazmat.backends import default_backend

        print("\n" + "=" * 60)
        print("使用cryptography库的ECC演示")
        print("=" * 60)

        # 使用NIST P-256曲线
        private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())
        public_key = private_key.public_key()

        # ECDH密钥交换
        peer_private = ec.generate_private_key(ec.SECP256R1(), default_backend())
        peer_public = peer_private.public_key()

        shared_key = private_key.exchange(ec.ECDH(), peer_public)
        print(f"ECDH共享密钥: {shared_key.hex()}")

        # ECDSA签名
        message = b"Test message"
        signature = private_key.sign(message, ec.ECDSA(hashes.SHA256()))
        print(f"ECDSA签名: {signature.hex()}")

        # 验证
        try:
            public_key.verify(signature, message, ec.ECDSA(hashes.SHA256()))
            print("验证: 通过 ✓")
        except Exception as e:
            print(f"验证失败: {e}")

        # 序列化为PEM
        pem = private_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        )
        print(f"\n私钥PEM格式:\n{pem.decode()}")

    except ImportError:
        print("请安装cryptography库: pip install cryptography")


if __name__ == "__main__":
    demo_ecdsa_with_library()
    demo_cryptography_library()
```

---

## 5. 安全性分析

### 5.1 安全级别对照表

| 安全级别 | 对称加密 | RSA/DSA | ECC |
|---------|---------|---------|-----|
| 80-bit | 3DES | 1024-bit | 160-bit |
| 128-bit | AES-128 | 3072-bit | 256-bit |
| 256-bit | AES-256 | 15360-bit | 512-bit |

### 5.2 已知攻击方法

**1. Pohlig-Hellman攻击**

- 如果曲线阶有小的素因子，可将问题分解到子群
- 对策：选择素数阶或接近素数阶的曲线

**2. MOV攻击 (Menezes-Okamoto-Vanstone)**

- 利用Weil配对将ECDLP约化到有限域上的DLP
- 对策：使用异常曲线(anomalous curves)避免

**3. 异常曲线攻击 (Semaev-Satoh-Araki-Smart)**

- 针对 $\#E(\mathbb{F}_p) = p$ 的异常曲线
- 可在多项式时间内求解ECDLP
- 对策：验证 $\#E(\mathbb{F}_p) \neq p$

**4. 侧信道攻击**

- 时间攻击、功耗分析、故障注入
- 对策：使用恒定时间算法，Curve25519等设计时已考虑

**5. 随机数重用攻击**

- ECDSA中重复使用k泄露私钥
- 对策：使用确定性ECDSA (RFC 6979)

### 5.3 安全实现建议

1. **使用经过验证的库**：OpenSSL, libsodium, cryptography等
2. **验证公钥**：确保点在曲线上且不在小子群中
3. **防止侧信道**：使用恒定时间算法
4. **随机数生成**：使用密码学安全的随机数生成器
5. **密钥派生**：使用HKDF等标准KDF从共享密钥派生

---

## 6. 实际应用场景

### 6.1 比特币/以太坊

```python
"""
比特币地址生成示例
基于secp256k1曲线
"""

import hashlib
import base58

def generate_bitcoin_address(private_key_bytes: bytes) -> str:
    """
    从私钥生成比特币地址

    流程:
    1. 私钥 -> 公钥 (secp256k1)
    2. 公钥 -> SHA256 -> RIPEMD160 (20字节)
    3. 添加版本字节 (0x00主网)
    4. 双SHA256取前4字节作为校验和
    5. Base58编码
    """
    import ecdsa

    # 1. 生成公钥
    sk = ecdsa.SigningKey.from_string(private_key_bytes, curve=ecdsa.SECP256k1)
    vk = sk.get_verifying_key()

    # 未压缩公钥格式: 0x04 + x(32字节) + y(32字节)
    public_key = b'\x04' + vk.to_string()

    # 2. SHA256然后RIPEMD160
    sha256_bpk = hashlib.sha256(public_key).digest()
    ripemd160_bpk = hashlib.new('ripemd160', sha256_bpk).digest()

    # 3. 添加版本字节 (主网)
    network_bitcoin_public_key = b'\x00' + ripemd160_bpk

    # 4. 双SHA256校验和
    checksum_full = hashlib.sha256(
        hashlib.sha256(network_bitcoin_public_key).digest()
    ).digest()
    checksum = checksum_full[:4]

    # 5. Base58编码
    address_bytes = network_bitcoin_public_key + checksum
    bitcoin_address = base58.b58encode(address_bytes).decode()

    return bitcoin_address


# 示例
if __name__ == "__main__":
    # 生成随机私钥
    private_key = secrets.token_bytes(32)
    address = generate_bitcoin_address(private_key)
    print(f"私钥: {private_key.hex()}")
    print(f"比特币地址: {address}")
```

### 6.2 TLS/HTTPS

ECC在TLS中的应用：

- **密钥交换**: ECDHE (Ephemeral ECDH) 提供前向安全性
- **认证**: ECDSA证书替代RSA证书
- **性能**: 握手速度提升，特别适合移动端

### 6.3 安全消息传递 (Signal协议)

Signal协议使用X3DH (Extended Triple Diffie-Hellman)：

- 结合Curve25519的静态和临时密钥
- 提供前向安全和后向安全

---

## 7. 与形式化证明的联系

### 7.1 群公理的形式化

椭圆曲线点加法满足群的四条公理，可在Coq/Isabelle中形式化证明：

```
1. 封闭性: ∀P,Q ∈ E(𝔽_p), P+Q ∈ E(𝔽_p)
2. 结合律: ∀P,Q,R ∈ E(𝔽_p), (P+Q)+R = P+(Q+R)
3. 单位元: ∃O, ∀P ∈ E(𝔽_p), P+O = O+P = P
4. 逆元: ∀P ∈ E(𝔽_p), ∃(-P), P+(-P) = O
```

### 7.2 ECDLP困难性的数论基础

- 通用群模型下，Pollard's rho是最优算法
- 特定曲线可能有额外结构（需要避免）

### 7.3 安全协议的形式化验证

ECDH和ECDSA的安全性可在计算模型和符号模型中形式化验证：

- **计算模型**: 基于ECDLP假设的归约证明
- **符号模型**: 使用ProVerif/Tamarin验证协议属性

---

## 8. 参考文献

1. **Hankerson, Menezes, Vanstone**: "Guide to Elliptic Curve Cryptography" (2004)
2. **Washington**: "Elliptic Curves: Number Theory and Cryptography" (2nd ed., 2008)
3. **Silverman**: "The Arithmetic of Elliptic Curves" (2nd ed., 2009)
4. **Bernstein & Lange**: "SafeCurves: choosing safe curves for elliptic-curve cryptography"
5. **NIST FIPS 186-5**: "Digital Signature Standard" (2023)
6. **SEC1/SEC2**: Standards for Efficient Cryptography (SECG)
7. **RFC 7748**: Elliptic Curves for Security (Curve25519)
8. **RFC 8032**: Edwards-Curve Digital Signature Algorithm (EdDSA)

---

## 9. 总结

椭圆曲线密码学是现代密码学的基石，其安全性建立在椭圆曲线离散对数问题的计算困难性之上。与RSA相比，ECC在同等安全级别下提供更短的密钥和更高的效率，使其成为移动设备、物联网和区块链等场景的首选方案。

**核心要点**:

- 椭圆曲线 $y^2 = x^3 + ax + b$ 在有限域上构成阿贝尔群
- ECDLP是ECC安全性的数学基础
- secp256k1和Curve25519是两个最重要的标准曲线
- ECDH提供密钥交换，ECDSA提供数字签名
- 实现时必须防范侧信道攻击和随机数重用

---

*本文档为FormalMath项目的一部分，旨在提供现代密码学的深度数学理论与实用实现。*
