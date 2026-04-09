---
title: RSA与椭圆曲线密码学完整实现
msc_primary: 94A60
---

# RSA与椭圆曲线密码学完整实现

## 1. RSA加密算法

### 数学原理
RSA基于大整数分解的困难性：
1. 选择两个大素数 $p$ 和 $q$
2. 计算 $n = pq$，$\varphi(n) = (p-1)(q-1)$
3. 选择 $e$ 满足 $1 < e < \varphi(n)$ 且 $\gcd(e, \varphi(n)) = 1$
4. 计算 $d$ 使得 $ed \equiv 1 \pmod{\varphi(n)}$

### 完整Python实现

```python
import random
from math import gcd

# 扩展欧几里得算法
def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    gcd_val, x1, y1 = extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return gcd_val, x, y

def mod_inverse(a, m):
    """计算模逆元 a^(-1) mod m"""
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None  # 逆元不存在
    return (x % m + m) % m

# Miller-Rabin素性测试
def is_prime(n, k=10):
    if n < 2: return False
    if n == 2 or n == 3: return True
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

def generate_prime(bits):
    """生成指定位数的大素数"""
    while True:
        n = random.getrandbits(bits)
        n |= (1 << bits - 1) | 1  # 确保最高位和最低位为1
        if is_prime(n):
            return n

# RSA密钥生成
def generate_rsa_keys(key_size=2048):
    """生成RSA密钥对"""
    p = generate_prime(key_size // 2)
    q = generate_prime(key_size // 2)
    
    n = p * q
    phi = (p - 1) * (q - 1)
    
    # 选择公钥指数e（常用65537）
    e = 65537
    while gcd(e, phi) != 1:
        e = random.randrange(3, phi, 2)
    
    # 计算私钥d
    d = mod_inverse(e, phi)
    
    return ((e, n), (d, n))  # (公钥, 私钥)

# RSA加密/解密
def rsa_encrypt(message, public_key):
    e, n = public_key
    return pow(message, e, n)

def rsa_decrypt(ciphertext, private_key):
    d, n = private_key
    return pow(ciphertext, d, n)

# 演示
print("=== RSA加密演示 ===")
pub_key, priv_key = generate_rsa_keys(512)  # 使用512位便于演示
print(f"公钥: e={pub_key[0]}, n={pub_key[1]}")
print(f"私钥: d={priv_key[0][:20]}... (前20位), n={priv_key[1]}")

message = 123456789
print(f"原始消息: {message}")

ciphertext = rsa_encrypt(message, pub_key)
print(f"加密后: {ciphertext}")

decrypted = rsa_decrypt(ciphertext, priv_key)
print(f"解密后: {decrypted}")
print(f"验证: {'成功' if decrypted == message else '失败'}")
```

---

## 2. 椭圆曲线密码学（ECC）

### 数学原理
椭圆曲线方程：$y^2 = x^3 + ax + b \pmod{p}$

点加法是群运算，椭圆曲线离散对数问题（ECDLP）是安全性基础。

### Python实现

```python
class Point:
    """椭圆曲线上的点"""
    def __init__(self, x, y, curve=None):
        self.x = x
        self.y = y
        self.curve = curve
    
    def __eq__(self, other):
        if not isinstance(other, Point):
            return False
        return self.x == other.x and self.y == other.y
    
    def __repr__(self):
        return f"Point({self.x}, {self.y})"
    
    def is_infinity(self):
        return self.x is None and self.y is None

# 无穷远点（群的单位元）
INFINITY = Point(None, None)

class EllipticCurve:
    """椭圆曲线 y^2 = x^3 + ax + b mod p"""
    def __init__(self, a, b, p):
        self.a = a
        self.b = b
        self.p = p
        # 验证判别式非零
        assert (4 * a**3 + 27 * b**2) % p != 0, "曲线奇异"
    
    def is_on_curve(self, point):
        if point.is_infinity():
            return True
        x, y = point.x, point.y
        return (y**2 - x**3 - self.a * x - self.b) % self.p == 0
    
    def point_add(self, P, Q):
        """椭圆曲线点加法"""
        if P.is_infinity():
            return Q
        if Q.is_infinity():
            return P
        
        x1, y1 = P.x, P.y
        x2, y2 = Q.x, Q.y
        
        if x1 == x2 and y1 != y2:
            return INFINITY
        
        # 计算斜率
        if x1 == x2:  # P == Q，倍点
            # s = (3x1^2 + a) / (2y1)
            numerator = (3 * x1**2 + self.a) % self.p
            denominator = (2 * y1) % self.p
        else:  # P != Q
            # s = (y2 - y1) / (x2 - x1)
            numerator = (y2 - y1) % self.p
            denominator = (x2 - x1) % self.p
        
        # 计算模逆元
        s = (numerator * pow(denominator, self.p - 2, self.p)) % self.p
        
        # 计算结果点
        x3 = (s**2 - x1 - x2) % self.p
        y3 = (s * (x1 - x3) - y1) % self.p
        
        return Point(x3, y3, self)
    
    def scalar_mult(self, k, P):
        """标量乘法 k*P（双加算法）"""
        result = INFINITY
        addend = P
        
        while k:
            if k & 1:
                result = self.point_add(result, addend)
            addend = self.point_add(addend, addend)
            k >>= 1
        
        return result

# secp256k1曲线参数（比特币使用）
SECP256K1_P = 2**256 - 2**32 - 2**9 - 2**8 - 2**7 - 2**6 - 2**4 - 1
SECP256K1_A = 0
SECP256K1_B = 7

# 基点G
SECP256K1_GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
SECP256K1_GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# 使用小参数演示
p_demo = 17
a_demo = 0
b_demo = 7

curve_demo = EllipticCurve(a_demo, b_demo, p_demo)

# 找一个曲线上的点
for x in range(p_demo):
    rhs = (x**3 + a_demo * x + b_demo) % p_demo
    for y in range(p_demo):
        if (y**2) % p_demo == rhs:
            G = Point(x, y, curve_demo)
            print(f"曲线上的点: {G}")
            break
    else:
        continue
    break

print(f"\n=== ECC演示（小参数） ===")
print(f"曲线: y^2 = x^3 + {a_demo}x + {b_demo} mod {p_demo}")

# 标量乘法演示
for k in range(1, 6):
    result = curve_demo.scalar_mult(k, G)
    print(f"{k} * G = {result}")
```

---

## 3. 数字签名

### ECDSA（椭圆曲线数字签名算法）

```python
def ecdsa_sign(message, private_key, curve, G, n):
    """ECDSA签名"""
    z = hash(message) % n  # 消息哈希
    
    while True:
        k = random.randrange(1, n)
        R = curve.scalar_mult(k, G)
        r = R.x % n
        if r == 0:
            continue
        
        s = (mod_inverse(k, n) * (z + r * private_key)) % n
        if s == 0:
            continue
        
        return (r, s)

def ecdsa_verify(message, signature, public_key, curve, G, n):
    """ECDSA验证"""
    r, s = signature
    z = hash(message) % n
    
    w = mod_inverse(s, n)
    u1 = (z * w) % n
    u2 = (r * w) % n
    
    P = curve.point_add(
        curve.scalar_mult(u1, G),
        curve.scalar_mult(u2, public_key)
    )
    
    return P.x % n == r
```

---

## 习题

### 习题1
证明RSA的正确性：若 $c = m^e \pmod{n}$，则 $c^d \equiv m \pmod{n}$

**证明**：
需要证明 $m^{ed} \equiv m \pmod{n}$

由于 $ed \equiv 1 \pmod{\varphi(n)}$，存在 $k$ 使得 $ed = 1 + k\varphi(n)$

- 若 $\gcd(m, n) = 1$，由欧拉定理：$m^{\varphi(n)} \equiv 1 \pmod{n}$
  $$m^{ed} = m^{1+k\varphi(n)} = m \cdot (m^{\varphi(n)})^k \equiv m \pmod{n}$$

- 若 $\gcd(m, n) \neq 1$，需用中国剩余定理分解到 $p$ 和 $q$ 上证明∎

### 习题2
计算椭圆曲线 $y^2 = x^3 + 2x + 2 \pmod{17}$ 上点 $(5, 1)$ 的阶。

**解答**：连续倍点直到得到无穷远点：
- $2G$，$3G$，... 直到 $nG = \mathcal{O}$

---

**适用**：docs/24-密码学/
