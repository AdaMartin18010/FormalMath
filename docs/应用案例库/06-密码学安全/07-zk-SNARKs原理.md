---
msc_primary: 08A99
msc_secondary:
- 00A99
- 00A99
- 00A99
title: zk-SNARKs原理
processed_at: '2026-04-05'
---
# zk-SNARKs原理

## 概述
- **应用领域**: 区块链/隐私计算/可验证计算
- **数学分支**: 计算复杂性/代数几何/密码学
- **难度级别**: 高级（研究级）
- **关键词**: zk-SNARK、QAP、配对、椭圆曲线、简洁证明

---

## 问题背景

### 问题定义

如何将任意计算转化为可高效验证的简洁证明？

**核心挑战**:
- 证明大小应与计算规模无关（简洁性）
- 验证时间应与计算规模无关（高效性）
- 不泄露计算输入（零知识性）

### 实际应用

- **Zcash**: 隐私加密货币
- **zk-Rollups**: 以太坊扩容方案
- **Filecoin**: 存储证明
- **暗池交易**: 金融隐私
- **机器学习推理验证**: AI可验证性

---

## 数学建模

### 计算到电路的转换

**步骤1**: 将程序转换为算术电路

```

程序: c = a * b + a
      
电路: a -----\

      |      * ----\
      |            + ---> c

      b -----/

```

**门约束**: 每个门的输入输出满足代数关系

### R1CS (Rank-1 Constraint System)

**定义**: 三元组 $(A, B, C)$ 的矩阵，使得:
$$\langle A, w \rangle \cdot \langle B, w \rangle = \langle C, w \rangle$$

其中 $w$ 是证据向量（包含输入、输出和中间变量）。

**示例**: 对于 $c = a \cdot b$
- 约束: $a \cdot b = c$
- 矩阵形式: $A = [0,1,0,...], B = [0,0,1,...], C = [0,0,0,1,...]$

### QAP (Quadratic Arithmetic Program)

**核心思想**: 将R1CS约束转化为多项式恒等式

**构造**:
1. 选择点集 $r_1, r_2, \ldots, r_m$（每个约束一个点）
2. 对每列构造拉格朗日插值多项式:
   $$A_i(x), B_i(x), C_i(x)$$
3. 目标多项式: $Z(x) = \prod_{i=1}^{m}(x - r_i)$

**验证条件**:
$$\left(\sum_{i=0}^{n} w_i A_i(x)\right) \cdot \left(\sum_{i=0}^{n} w_i B_i(x)\right) - \left(\sum_{i=0}^{n} w_i C_i(x)\right) = H(x) \cdot Z(x)$$

---

## 数学方法

### 基于配对的zk-SNARK构造 (Pinocchio协议)

#### 双线性配对

**定义**: 映射 $e: \mathbb{G}_1 \times \mathbb{G}_2 \rightarrow \mathbb{G}_T$ 满足:
1. 双线性: $e(aP, bQ) = e(P, Q)^{ab}$
2. 非退化: $e \not\equiv 1$
3. 可计算: 高效计算

#### 公共参考字符串 (CRS)

**结构化CRS**:
- $\{g^{\alpha s^i}, h^{\alpha s^i}\}_{i=0}^{d}$ （用于多项式承诺）
- $\{g^{\beta_i}\}$ （用于变量绑定）

**注意**: $\alpha, s$ 必须保密（有毒废料），但可验证被销毁。

#### 证明生成

**证明组成**: $(A, B, C)$ 三个群元素

1. 计算见证多项式 $W(x) = \sum w_i L_i(x)$
2. 计算 $H(x)$ 使得约束成立
3. 使用CRS评估多项式于秘密点 $s$:
   $$A = g^{W(s)}, B = h^{W(s)}, C = g^{H(s)}$$

#### 验证

验证者检查:
$$e(A, B) = e(g^{Z(s)}, C) \cdot \prod e(\text{公开输入项})$$

时间复杂度: $O(|\text{公开输入}|)$，与电路规模无关！

---

## 求解过程

### Groth16优化

当前最流行的zk-SNARK构造，证明仅3个群元素。

#### 证明结构

$$\pi = (A, B, C) \in \mathbb{G}_1 \times \mathbb{G}_2 \times \mathbb{G}_1$$

大小: ~200字节（BN254曲线）

#### 验证方程

$$e(A, B) = e(\alpha, \beta) \cdot e(C, \delta) \cdot e(\text{公开输入多项式}, \gamma)$$

#### 计算成本

| 操作 | 复杂度 | 实际时间 |
|------|--------|----------|
| 证明生成 | $O(|C|)$ | 秒级~分钟级 |
| 证明验证 | $O(|\text{输入}|)$ | 毫秒级 |
| 证明大小 | $O(1)$ | ~200字节 |

### 从程序到证明的流程

```

高级程序
    ↓ (编译器)
算术电路 (R1CS)
    ↓ (QAP转换)
多项式约束系统
    ↓ (证明者)
简洁证明 π
    ↓ (验证者)
接受/拒绝

```

---

## 结果分析

### 安全性假设

1. **q-PKE假设**: 幂知识指数假设
2. **q-SDH假设**: 强Diffie-Hellman假设
3. **双线性Diffie-Hellman**: 标准假设

### 局限性与挑战

| 挑战 | 说明 | 解决方案 |
|------|------|----------|
| 可信设置 | 需要生成并销毁有毒参数 | 多方计算、透明方案(STARKs) |
| 量子安全 | 基于椭圆曲线，不抗量子 | 格基方案、哈希方案 |
| 证明生成开销 | 比原生执行慢1000x+ | 硬件加速、递归证明 |
| 电路专用 | 每个程序需要专用设置 | 通用设置方案(Plonk) |

### 替代方案对比

| 方案 | 证明大小 | 验证时间 | 设置 | 量子安全 |
|------|----------|----------|------|----------|
| Groth16 | 200B | 1.5ms | 可信 | 否 |
| Plonk | ~400B | 3ms | 通用 | 否 |
| STARK | ~50KB | 10ms | 透明 | 是 |
| Bulletproofs | ~1KB | 线性 | 透明 | 否 |

---

## 拓展思考

### 递归证明与压缩

**思想**: 使用zk-SNARK证明另一个zk-SNARK验证的正确性

**应用**:
- 区块链轻客户端
- 无限压缩
- Halo、Fractal协议

### 实际编程

**circom语言**:

```circom
template Multiplier() {
    signal input a;
    signal input b;
    signal output c;
    c <== a * b;
}

```

**snarkjs工具链**:

```bash
circom circuit.circom --r1cs --wasm
snarkjs groth16 setup circuit.r1cs ptau_0001.ptau circuit_0000.zkey
snarkjs groth16 prove circuit_0000.zkey input.json proof.json public.json
snarkjs groth16 verify verification_key.json public.json proof.json

```

---

## 参考资源

### 开创性论文
- [1] Parno, B., et al. (2013). Pinocchio: Nearly practical verifiable computation. *IEEE S&P*.
- [2] Ben-Sasson, E., et al. (2014). Succinct non-interactive zero knowledge for a von neumann architecture. *USENIX Security*.
- [3] Groth, J. (2016). On the size of pairing-based non-interactive arguments. *EUROCRYPT*.

### 教材与教程
- [1] Boneh, D., et al. (2023). *A Graduate Course in Applied Cryptography*.
- [2] 0xPARC: zk-learning.org
- [3] Vitalik Buterin的博客系列

### 开源实现
- [libsnark](https://github.com/scipr-lab/libsnark): C++库
- [snarkjs](https://github.com/iden3/snarkjs): JavaScript实现
- [arkworks](https://github.com/arkworks-rs): Rust生态系统

---

**案例创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
