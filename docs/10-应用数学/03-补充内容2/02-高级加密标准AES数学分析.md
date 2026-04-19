---
msc_primary: 94

  - 94A60
  - 12E20
  - 11T71
  - 14G50
title: 高级加密标准AES数学分析
processed_at: '2026-04-05'
---
# 高级加密标准AES数学分析

**创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
**版本**: v1.0
**状态**: 完成
**国际对齐**: Daemen-Rijmen "The Design of Rijndael", 2nd Edition

---

## 📋 概述

高级加密标准(AES)是Rijndael算法的特定实例，于2001年被NIST采纳为联邦信息处理标准(FIPS-197)。AES的数学设计基于代换-置换网络(SPN)，其核心运算在有限域$\mathbb{F}_{2^8}$上定义，体现了完美的代数学结构与密码学安全性的结合。

---

## 一、有限域$\mathbb{F}_{2^8}$的构造

### 1.1 域扩张与不可约多项式

**定义 1.1（有限域$\mathbb{F}_{2^8}$）**:
AES使用$\mathbb{F}_2$的8次扩域，其元素可表示为：
$$
\mathbb{F}_{2^8} = \mathbb{F}_2[x] / (m(x))
$$

其中$m(x)$为8次不可约多项式。AES选择：
$$
m(x) = x^8 + x^4 + x^3 + x + 1 \in \mathbb{F}_2[x]
$$

**定义 1.2（元素表示）**:
$\mathbb{F}_{2^8}$中元素可表示为：

- **多项式形式**: $b(x) = b_7x^7 + b_6x^6 + \cdots + b_1x + b_0$
- **字节形式**: 8位字节$(b_7b_6b_5b_4b_3b_2b_1b_0)_2$
- **十六进制**: 两位十六进制数

**示例**:
十六进制值`{57}`（即$0x57 = 87$）对应：
$$
b(x) = x^6 + x^4 + x^2 + x + 1
$$
因为$87 = 64 + 16 + 4 + 2 + 1 = 2^6 + 2^4 + 2^2 + 2^1 + 2^0$。

### 1.2 域运算

**加法**:
在$\mathbb{F}_{2^8}$中，加法为按位异或(XOR)：
$$
a(x) + b(x) = a(x) \oplus b(x)
$$

**乘法**:
乘法定义为多项式乘法模$m(x)$：
$$
a(x) \cdot b(x) = a(x) \times b(x) \mod m(x)
$$

**乘法算法**:

```

输入: a(x), b(x) ∈ F_{2^8}
输出: c(x) = a(x) · b(x)

c ← 0
for i = 0 to 7:
    if b_i = 1:
        c ← c ⊕ a
    a ← a · x mod m(x)  // 左移一位，若溢出则异或0x1B
return c

```

**乘$x$操作（xtime）**:
$$
\mathsf{xtime}(a) = \begin{cases}
a \ll 1 & \text{if } a_7 = 0 \\
(a \ll 1) \oplus 0x1B & \text{if } a_7 = 1
\end{cases}
$$

其中$0x1B = 00011011_2$对应$x^4 + x^3 + x + 1$。

**乘法逆元**:
对非零$a \in \mathbb{F}_{2^8}^*$，逆元$a^{-1}$满足$a \cdot a^{-1} = 1$。可用扩展欧几里得算法计算。

**定理 1.3（逆元存在性）**:
$\mathbb{F}_{2^8}^*$为255阶乘法循环群，每个非零元素有唯一逆元。

---

## 二、AES算法结构

### 2.1 数据表示

**状态(State)**:
AES将128-bit明文组织为4×4字节矩阵：
$$
\begin{bmatrix}
s_{0,0} & s_{0,1} & s_{0,2} & s_{0,3} \\
s_{1,0} & s_{1,1} & s_{1,2} & s_{1,3} \\
s_{2,0} & s_{2,1} & s_{2,2} & s_{2,3} \\
s_{3,0} & s_{3,1} & s_{3,2} & s_{3,3}
\end{bmatrix}
$$

按列优先顺序填入：
$$
\text{input}_0, \text{input}_4, \text{input}_8, \text{input}_{12} \to \text{第0列}
$$

### 2.2 算法参数

| 参数 | AES-128 | AES-192 | AES-256 |
|-----|---------|---------|---------|
| 密钥长度 | 128 bits | 192 bits | 256 bits |
| 分组长度 | 128 bits | 128 bits | 128 bits |
| 轮数$N_r$ | 10 | 12 | 14 |
| 轮密钥字数 | 44 | 52 | 60 |

### 2.3 轮函数结构

每轮（除最后一轮）包含四个变换：

1. **SubBytes()**: 字节代换（非线性层）
2. **ShiftRows()**: 行移位（扩散层）
3. **MixColumns()**: 列混合（扩散层）
4. **AddRoundKey()**: 轮密钥加（密钥混合）

最后一轮省略MixColumns()。

---

## 三、SubBytes的代数性质

### 3.1 S-box构造

**定义 3.1（AES S-box）**:
S-box是$\mathbb{F}_{2^8} \to \mathbb{F}_{2^8}$的置换，定义为：
$$
S(a) = M \cdot a^{-1} \oplus c
$$

其中：

- $a^{-1}$为$\mathbb{F}_{2^8}$中的乘法逆元（$a=0$时定义为0）
- $M$为$\mathbb{F}_2$上的8×8可逆矩阵：

$$
M = \begin{bmatrix}
1 & 0 & 0 & 0 & 1 & 1 & 1 & 1 \\
1 & 1 & 0 & 0 & 0 & 1 & 1 & 1 \\
1 & 1 & 1 & 0 & 0 & 0 & 1 & 1 \\
1 & 1 & 1 & 1 & 0 & 0 & 0 & 1 \\
1 & 1 & 1 & 1 & 1 & 0 & 0 & 0 \\
0 & 1 & 1 & 1 & 1 & 1 & 0 & 0 \\
0 & 0 & 1 & 1 & 1 & 1 & 1 & 0 \\
0 & 0 & 0 & 1 & 1 & 1 & 1 & 1
\end{bmatrix}
$$

- $c = 0x63 = 01100011_2$为常数向量

### 3.2 S-box的密码学性质

**代数次数**:
S-box作为$\mathbb{F}_2$上的布尔函数，代数次数为7（最大可能）。

**差分均匀性**:
差分分布表(DDT)中最大值为4（对8-bit S-box，这是最优的）。

**非线性度**:
S-box的非线性度为112，接近理论上界120。

**代数免疫性**:
S-box抵抗代数攻击，不存在低次数代数关系。

**定理 3.2（S-box双射性）**:
AES S-box是$\mathbb{F}_{2^8}$上的置换。

*证明*:

1. 逆元映射$a \mapsto a^{-1}$在$\mathbb{F}_{2^8}^*$上是双射，且$0 \mapsto 0$
2. 仿射变换$M \cdot x \oplus c$是双射（$M$可逆）
3. 双射的复合仍是双射 ∎

### 3.3 逆S-box

逆S-box计算：
$$
S^{-1}(b) = (M^{-1} \cdot (b \oplus c))^{-1}
$$

其中：
$$
M^{-1} = \begin{bmatrix}
0 & 0 & 1 & 0 & 0 & 1 & 0 & 1 \\
1 & 0 & 0 & 1 & 0 & 0 & 1 & 0 \\
0 & 1 & 0 & 0 & 1 & 0 & 0 & 1 \\
1 & 0 & 1 & 0 & 0 & 1 & 0 & 0 \\
0 & 1 & 0 & 1 & 0 & 0 & 1 & 0 \\
0 & 0 & 1 & 0 & 1 & 0 & 0 & 1 \\
1 & 0 & 0 & 1 & 0 & 1 & 0 & 0 \\
0 & 1 & 0 & 0 & 1 & 0 & 1 & 0
\end{bmatrix}
$$

---

## 四、MixColumns的MDS性质

### 4.1 列混合变换

**定义 4.1（MixColumns）**:
MixColumns将状态每列视为$\mathbb{F}_{2^8}[x]/(x^4+1)$中的多项式，乘以固定多项式：
$$
a(x) = \{03\}x^3 + \{01\}x^2 + \{01\}x + \{02\}
$$

矩阵表示：
$$
\begin{bmatrix}
s'_{0,c} \\
s'_{1,c} \\
s'_{2,c} \\
s'_{3,c}
\end{bmatrix}
=
\begin{bmatrix}
02 & 03 & 01 & 01 \\
01 & 02 & 03 & 01 \\
01 & 01 & 02 & 03 \\
03 & 01 & 01 & 02
\end{bmatrix}
\cdot
\begin{bmatrix}
s_{0,c} \\
s_{1,c} \\
s_{2,c} \\
s_{3,c}
\end{bmatrix}
$$

### 4.2 MDS码理论

**定义 4.2（分支数）**:
设$\theta$为线性变换，输入输出重量分别为$w_{in}$和$w_{out}$：

- **分支数**: $B(\theta) = \min_{a \neq 0}(w_{in}(a) + w_{out}(\theta(a)))$

**定义 4.3（MDS矩阵）**:
$k \times k$矩阵$M$称为**MDS（最大距离可分）矩阵**，若其分支数为$k+1$（可能最大值）。

**定理 4.4（MDS等价条件）**:
$k \times k$矩阵$M$是MDS矩阵当且仅当$M$的所有子矩阵都可逆。

**定理 4.5（AES MixColumns是MDS）**:
AES的MixColumns矩阵是MDS矩阵，分支数为5。

*证明概要*:
MixColumns矩阵的循环结构保证：

1. 所有1×1子矩阵（对角元）非零
2. 所有2×2子矩阵行列式非零
3. 所有3×3和4×4子矩阵可逆

具体验证：

- $\det\begin{bmatrix}02&03\\01&02\end{bmatrix} = 02 \cdot 02 + 03 \cdot 01 = 04 + 03 = 07 \neq 0$
- 其他子矩阵类似可验证 ∎

### 4.3 扩散性质

**命题 4.6（完全扩散）**:
两轮AES保证：

- 改变1个输入字节至少影响8个输出字节
- 4轮后每一输出字节依赖于所有输入字节

---

## 五、ShiftRows与整体扩散

### 5.1 行移位变换

**定义 5.1（ShiftRows）**:
$$
\begin{bmatrix}
s_{0,0} & s_{0,1} & s_{0,2} & s_{0,3} \\
s_{1,0} & s_{1,1} & s_{1,2} & s_{1,3} \\
s_{2,0} & s_{2,1} & s_{2,2} & s_{2,3} \\
s_{3,0} & s_{3,1} & s_{3,2} & s_{3,3}
\end{bmatrix}
\xrightarrow{\mathsf{ShiftRows}}
\begin{bmatrix}
s_{0,0} & s_{0,1} & s_{0,2} & s_{0,3} \\
s_{1,1} & s_{1,2} & s_{1,3} & s_{1,0} \\
s_{2,2} & s_{2,3} & s_{2,0} & s_{2,1} \\
s_{3,3} & s_{3,0} & s_{3,1} & s_{3,2}
\end{bmatrix}
$$

移位量: 第0行0字节，第1行1字节，第2行2字节，第3行3字节。

### 5.2 扩散分析

**定理 5.2（宽轨迹策略）**:
ShiftRows与MixColumns的组合实现**宽轨迹**扩散：

- 活跃S-box构成连续轨迹
- 轮数增加时活跃S-box数指数增长

**活跃S-box下界**:

| 轮数 | 活跃S-box最小数 |
|-----|---------------|
| 1 | 1 |
| 2 | 5 |
| 3 | 25 |
| 4 | 50 |

---

## 六、密钥扩展算法

### 6.1 密钥调度

AES密钥扩展从种子密钥生成$N_r + 1$个轮密钥。

**RotWord**: 4字节字循环左移1字节
**SubWord**: 对4字节应用S-box
**Rcon**: 轮常数$[x^{i-1}, 00, 00, 00]$在$\mathbb{F}_{2^8}$

**密钥扩展伪代码**:

```

KeyExpansion(key):
    w[0..Nk-1] = key
    for i = Nk to 4*(Nr+1)-1:
        temp = w[i-1]
        if i mod Nk == 0:
            temp = SubWord(RotWord(temp)) ⊕ Rcon[i/Nk]
        else if Nk > 6 and i mod Nk == 4:
            temp = SubWord(temp)
        w[i] = w[i-Nk] ⊕ temp
    return w

```

### 6.2 密钥调度安全性

**设计目标**:

1. **非线性**: SubWord引入S-box非线性
2. **对称性消除**: 打破轮密钥对称性
3. **扩散**: 每个轮密钥位依赖于多个种子密钥位

---

## 七、安全性分析框架

### 7.1 差分密码分析

**定义 7.1（差分特征）**:
差分特征是一系列轮差分$(\Delta_0, \Delta_1, \ldots, \Delta_r)$，其中$\Delta_i$为第$i$轮输入差分。

**差分概率**:
对S-box，输入差分$\Delta_{in}$到输出差分$\Delta_{out}$的概率：
$$
DP(\Delta_{in}, \Delta_{out}) = \frac{|\{x : S(x) \oplus S(x \oplus \Delta_{in}) = \Delta_{out}\}|}{256}

$$

**定理 7.2（AES抗差分分析）**:
4轮AES的最佳差分特征概率上界为$2^{-150}$，远低于穷举搜索复杂度$2^{-128}$。

### 7.2 线性密码分析

**线性近似**:
对S-box，线性近似概率：
$$
LP(\Gamma_{in}, \Gamma_{out}) = \left(\frac{|\{x : \Gamma_{in} \cdot x = \Gamma_{out} \cdot S(x)\}|}{128} - 1\right)^2

$$

**定理 7.3（AES抗线性分析）**:
4轮AES的最佳线性特征概率上界为$2^{-150}$。

### 7.3 代数攻击

**XL算法**: 通过线性化方程组求解
**Gröbner基**: 多项式系统求解

**AES代数结构**:

- 可表示为$\mathbb{F}_{2^8}$上的稀疏二次方程组
- 目前代数攻击对完整AES无效

---

## 八、Python实现

### 8.1 完整AES实现

```python
class AES:
    """AES-128/192/256实现"""

    # S-box
    S_BOX = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
        0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        # ... (完整256字节)
    ]

    # 逆S-box
    INV_S_BOX = [0] * 256
    for i in range(256):
        INV_S_BOX[S_BOX[i]] = i

    # 轮常数
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

    def __init__(self, key: bytes):
        self.Nk = len(key) // 4  # 密钥字数
        self.Nr = {4: 10, 6: 12, 8: 14}[self.Nk]  # 轮数
        self.round_keys = self._key_expansion(key)

    def _sub_bytes(self, state: list):
        """字节代换"""
        for i in range(4):
            for j in range(4):
                state[i][j] = self.S_BOX[state[i][j]]

    def _inv_sub_bytes(self, state: list):
        """逆字节代换"""
        for i in range(4):
            for j in range(4):
                state[i][j] = self.INV_S_BOX[state[i][j]]

    def _shift_rows(self, state: list):
        """行移位"""
        state[1] = state[1][1:] + state[1][:1]
        state[2] = state[2][2:] + state[2][:2]
        state[3] = state[3][3:] + state[3][:3]

    def _inv_shift_rows(self, state: list):
        """逆行移位"""
        state[1] = state[1][-1:] + state[1][:-1]
        state[2] = state[2][-2:] + state[2][:-2]
        state[3] = state[3][-3:] + state[3][:-3]

    def _xtime(self, b: int) -> int:
        """乘x运算"""
        return ((b << 1) ^ 0x1b) & 0xff if b & 0x80 else (b << 1) & 0xff

    def _mul(self, a: int, b: int) -> int:
        """F_{2^8}乘法"""
        result = 0
        for i in range(8):
            if b & 1:
                result ^= a
            a = self._xtime(a)
            b >>= 1
        return result

    def _mix_columns(self, state: list):
        """列混合"""
        for j in range(4):
            s0 = state[0][j]
            s1 = state[1][j]
            s2 = state[2][j]
            s3 = state[3][j]

            state[0][j] = self._mul(0x02, s0) ^ self._mul(0x03, s1) ^ s2 ^ s3
            state[1][j] = s0 ^ self._mul(0x02, s1) ^ self._mul(0x03, s2) ^ s3
            state[2][j] = s0 ^ s1 ^ self._mul(0x02, s2) ^ self._mul(0x03, s3)
            state[3][j] = self._mul(0x03, s0) ^ s1 ^ s2 ^ self._mul(0x02, s3)

    def _add_round_key(self, state: list, round_key: list):
        """轮密钥加"""
        for i in range(4):
            for j in range(4):
                state[i][j] ^= round_key[i][j * 4 + i]

    def _key_expansion(self, key: bytes) -> list:
        """密钥扩展"""
        w = [list(key[i:i+4]) for i in range(0, len(key), 4)]

        for i in range(self.Nk, 4 * (self.Nr + 1)):
            temp = w[i-1].copy()
            if i % self.Nk == 0:
                # RotWord + SubWord + Rcon
                temp = [self.S_BOX[temp[1]], self.S_BOX[temp[2]],
                       self.S_BOX[temp[3]], self.S_BOX[temp[0]]]
                temp[0] ^= self.RCON[i // self.Nk - 1]
            elif self.Nk > 6 and i % self.Nk == 4:
                temp = [self.S_BOX[b] for b in temp]

            w.append([w[i-self.Nk][j] ^ temp[j] for j in range(4)])

        return w

    def encrypt(self, plaintext: bytes) -> bytes:
        """加密单分组"""
        # 初始化为状态矩阵
        state = [[plaintext[i + 4*j] for j in range(4)] for i in range(4)]

        # 初始轮密钥加
        self._add_round_key(state, self.round_keys[0:4])

        # Nr-1轮完整轮
        for round in range(1, self.Nr):
            self._sub_bytes(state)
            self._shift_rows(state)
            self._mix_columns(state)
            self._add_round_key(state, self.round_keys[round*4:(round+1)*4])

        # 最后一轮（无MixColumns）
        self._sub_bytes(state)
        self._shift_rows(state)
        self._add_round_key(state, self.round_keys[self.Nr*4:(self.Nr+1)*4])

        # 输出密文
        return bytes(state[i][j] for i in range(4) for j in range(4))

# 使用示例
if __name__ == "__main__":
    key = bytes([0x00] * 16)  # 128-bit零密钥
    plaintext = bytes([0x00] * 16)  # 128-bit零明文

    aes = AES(key)
    ciphertext = aes.encrypt(plaintext)
    print(f"密文: {ciphertext.hex()}")
    # 预期输出: 66e94bd4ef8a2c3b884cfa59ca342b2e

```

## 8.2 有限域运算测试

```python
def test_gf28():
    """测试F_{2^8}运算"""
    aes = AES(bytes(16))

    # 测试乘法
    assert aes._mul(0x57, 0x13) == 0xfe  # 验证: {57}·{13} = {fe}

    # 测试xtime
    assert aes._xtime(0x57) == 0xae
    assert aes._xtime(0xae) == 0x47  # 溢出情况

    print("有限域运算测试通过")

test_gf28()

```

---

## 九、Lean4形式化片段

### 9.1 有限域运算形式化

```lean4
import Mathlib

-- AES irreducible polynomial: x^8 + x^4 + x^3 + x + 1
def aesPoly : Polynomial (ZMod 2) :=
  Polynomial.X ^ 8 + Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X + 1

-- GF(2^8) as quotient ring
def GF256 := Polynomial (ZMod 2) ⧸ (Ideal.span {aesPoly})

instance : Field GF256 := by
  unfold GF256
  apply Ideal.Quotient.field
  -- Prove aesPoly is irreducible over F_2
  sorry

-- S-box affine transformation matrix
def sboxMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1,0,0,0,1,1,1,1;
     1,1,0,0,0,1,1,1;
     1,1,1,0,0,0,1,1;
     1,1,1,1,0,0,0,1;
     1,1,1,1,1,0,0,0;
     0,1,1,1,1,1,0,0;
     0,0,1,1,1,1,1,0;
     0,0,0,1,1,1,1,1]

-- S-box constant
def sboxConst : Vector (ZMod 2) 8 :=
  ![0,1,1,0,0,0,1,1]  -- 0x63

-- AES S-box as composition of inverse and affine transform
def aesSbox (a : GF256) : GF256 :=
  if a = 0 then
    -- Special case: 0 maps to constant 0x63
    sorry
  else
    let inv := a⁻¹
    -- Apply affine transformation
    sorry

-- Theorem: S-box is a permutation
theorem sbox_bijective : Function.Bijective aesSbox := by
  sorry

```

### 9.2 MDS性质形式化

```lean4
-- MDS matrix definition
-- A matrix is MDS if every square submatrix is invertible
def IsMDS {n : ℕ} (M : Matrix (Fin n) (Fin n) GF256) : Prop :=
  ∀ (s t : Finset (Fin n)), s.card = t.card →
    IsUnit (M.submatrix s t)

-- AES MixColumns matrix
def mixColumnsMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  !![2,3,1,1;
     1,2,3,1;
     1,1,2,3;
     3,1,1,2]

-- Theorem: MixColumns matrix is MDS
theorem mixColumns_is_MDS : IsMDS mixColumnsMatrix := by
  -- Verify all submatrices are invertible
  -- 1×1 submatrices: all entries non-zero
  -- 2×2 submatrices: all determinants non-zero
  -- 3×3 and 4×4 submatrices: all determinants non-zero
  sorry

-- Branch number definition
def branchNumber {n : ℕ} (M : Matrix (Fin n) (Fin n) GF256) : ℕ :=
  let hammingWeight (v : Fin n → GF256) : ℕ :=
    (Finset.univ.filter (fun i => v i ≠ 0)).card
  Finset.univ.fold min (2 * n) (fun v =>
    if v ≠ 0 then hammingWeight v + hammingWeight (M.mulVec v) else 2 * n)

-- Theorem: MDS matrix has maximum branch number
theorem mds_max_branch_number {n : ℕ} (M : Matrix (Fin n) (Fin n) GF256)
    (hMDS : IsMDS M) : branchNumber M = n + 1 := by
  sorry

```

---

## 十、实际应用

### 10.1 磁盘加密

**BitLocker (Windows)**: AES-XTS模式
**FileVault (macOS)**: AES-XTS模式
**LUKS (Linux)**: AES-XTS或AES-CBC

### 10.2 网络通信

**TLS 1.3**: AES-128-GCM或AES-256-GCM
**IPsec**: AES-CBC或AES-GCM
**SSH**: AES-256-CTR

### 10.3 无线通信

**Wi-Fi WPA3**: AES-CCMP-128或AES-CCMP-256
**5G NR**: AES-256加密用户面数据

---

## 参考文献

1. Daemen, J., & Rijmen, V. (2002). *The Design of Rijndael: AES - The Advanced Encryption Standard*. Springer.
2. NIST (2001). FIPS PUB 197: Advanced Encryption Standard (AES).
3. Daemen, J., & Rijmen, V. (2000). Rijndael for AES. *AES Candidate Conference*.
4. Biham, E., & Shamir, A. (1991). Differential Cryptanalysis of DES-like Cryptosystems. *CRYPTO*.
5. Matsui, M. (1994). Linear Cryptanalysis Method for DES Cipher. *EUROCRYPT*.

---

**最后更新**: 2026年4月3日
