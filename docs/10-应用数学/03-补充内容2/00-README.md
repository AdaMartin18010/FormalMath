---
msc_primary: 00A99
msc_secondary:
- 94A60
- 00A99
title: 19-应用数学 - 密码学与编码理论
processed_at: '2026-04-05'
---
# 19-应用数学 - 密码学与编码理论

**创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
**版本**: v1.0
**状态**: 完成

---

## 📚 目录概述

本目录包含密码学与编码理论的深度数学文档，涵盖现代密码学的数学基础、标准算法分析、纠错码理论以及后量子密码学。

---

## 📁 文档列表

### 1. [密码学数学基础-深度版](01-密码学数学基础-深度版.md)

**MSC**: 94A60, 11T71, 14G50

**核心内容**:

- 计算复杂性基础（P vs NP, 单向函数）
- 对称加密的数学结构（Feistel网络、SPN）
- RSA的数论基础（Euler定理、模幂运算）
- 椭圆曲线密码学（ECDSA原理）
- 零知识证明基础

**国际对齐**: Katz-Lindell "Introduction to Modern Cryptography"

**包含实现**:

- RSA完整Python实现
- 椭圆曲线运算
- Lean4形式化片段（Euler定理、单向函数定义）

---

### 2. [高级加密标准AES数学分析](02-高级加密标准AES数学分析.md)

**MSC**: 94A60, 12E20

**核心内容**:

- 有限域$\mathbb{F}_{2^8}$的构造与运算
- SubBytes的代数性质（S-box分析）
- MixColumns的MDS性质
- AES安全性分析框架（差分/线性密码分析）

**国际对齐**: Daemen-Rijmen "The Design of Rijndael"

**包含实现**:

- 完整AES-128/192/256 Python实现
- 有限域运算测试
- Lean4形式化片段（MDS矩阵性质）

---

### 3. [编码理论基础-深度版](03-编码理论基础-深度版.md)

**MSC**: 94Bxx, 94B05, 94B15, 94B35

**核心内容**:

- 线性码的参数与界（Singleton界、Hamming界、Gilbert-Varshamov界）
- 循环码与生成多项式
- Reed-Solomon码的构造与解码（Berlekamp-Welch算法）
- LDPC码与置信传播解码

**国际对齐**: MacWilliams-Sloane "The Theory of Error-Correcting Codes"

**包含实现**:

- Reed-Solomon编解码器（Python）
- Berlekamp-Welch解码实现
- LDPC码与置信传播算法
- Lean4形式化片段（Singleton界、MDS码、循环码）

---

### 4. [后量子密码学数学基础](04-后量子密码学数学基础.md)

**MSC**: 94A60, 11T71, 68P25

**核心内容**:

- 格的基本概念与困难问题（SVP, CVP）
- LWE问题与Regev加密
- NTRU密码系统
- NIST PQC标准（ML-KEM, ML-DSA, SLH-DSA）

**国际对齐**: Peikert "A Decade of Lattice Cryptography", NIST PQC FIPS 203/204/205

**包含实现**:

- LWE加密Python实现
- NTRU加密Python实现
- Lean4形式化片段（格定义、LWE问题、NTRU问题）

---

## 🎯 学习目标

完成本目录学习后，应能够：

1. **理解现代密码学数学基础**：单向函数、计算复杂性、困难问题假设
2. **掌握对称加密设计原理**：SPN结构、Feistel网络、AES的代数结构
3. **理解公钥密码学**：RSA、椭圆曲线、格密码的数学基础
4. **掌握纠错码理论**：线性码、循环码、Reed-Solomon码、LDPC码
5. **了解后量子密码学**：LWE、NTRU、NIST标准算法

---

## 📖 前置知识

- 线性代数
- 抽象代数（群、环、域）
- 数论基础
- 概率论
- 计算复杂性理论

---

## 🔗 相关文档

- [信息论数学-深化版](../10-应用数学/10-信息论数学-深化版.md)
- [区块链数学-深化版](../10-应用数学/13-区块链数学-深化版.md)
- [量子计算数学-深化版](../10-应用数学/14-量子计算数学-深化版.md)

---

## 📚 主要参考文献

### 密码学

1. Katz, J., & Lindell, Y. (2020). *Introduction to Modern Cryptography* (3rd ed.). CRC Press.
2. Goldreich, O. (2001). *Foundations of Cryptography*. Cambridge University Press.
3. Daemen, J., & Rijmen, V. (2002). *The Design of Rijndael*. Springer.

### 编码理论

1. MacWilliams, F. J., & Sloane, N. J. A. (1977). *The Theory of Error-Correcting Codes*. North-Holland.
2. Richardson, T., & Urbanke, R. (2008). *Modern Coding Theory*. Cambridge University Press.

### 后量子密码学

1. Peikert, C. (2016). A Decade of Lattice Cryptography. *Foundations and Trends in TCS*.
2. NIST (2024). FIPS 203/204/205: Post-Quantum Cryptography Standards.

---

## 📝 文档统计

| 文档 | 字数（估算） | 核心数学定义 | Python代码 | Lean4形式化 |
|-----|-----------|------------|-----------|------------|
| 01-密码学数学基础 | ~4500 | 15+ | 有 | 有 |
| 02-AES数学分析 | ~5000 | 12+ | 有 | 有 |
| 03-编码理论基础 | ~6000 | 18+ | 有 | 有 |
| 04-后量子密码学 | ~5500 | 14+ | 有 | 有 |

---

**最后更新**: 2026年4月3日
