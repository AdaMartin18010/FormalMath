---
msc_primary: 00

  - 00A99
title: 数学×计算机科学：密码学的数论代数
processed_at: '2026-04-05'
---
# 数学×计算机科学：密码学的数论代数

## 概述

现代密码学是建立在严格数学基础上的安全科学。从数论中的大数分解和离散对数问题，到代数中的椭圆曲线和格理论，数学困难问题构成了密码安全性的基石。

---

## 核心思维导图

```mermaid
mindmap
  root((密码学<br/>Cryptography))
    数学基础
      数论
        模运算
        欧拉定理
        中国剩余定理
        原根与指数
      计算困难问题
        整数分解
        离散对数
        椭圆曲线离散对数
        最短向量问题
      代数结构
        群
        环
        域
        有限域
      概率论
        随机性
        伪随机生成器
        不可区分性
    对称密码
      分组密码
        SPN结构
        Feistel网络
        AES
        DES
      流密码
        LFSR
        RC4
        ChaCha20
      工作模式
        ECB, CBC
        CTR, GCM
      安全性
        完美保密
        语义安全
        不可区分性
    公钥密码
      RSA
        模n = pq
        e,d满足ed≡1 mod φ(n)
        基于分解困难性
      ElGamal
        离散对数
        密钥交换
        数字签名
      ECC
        椭圆曲线群
        更短密钥
        ECDSA, ECDH
      格密码
        LWE问题
        抗量子
        NTRU, Kyber
    密码分析
      经典攻击
        频率分析
        差分分析
        线性分析
      代数攻击
        Gröbner基
        方程组求解
      侧信道
        功耗分析
        时序攻击
        故障注入
    协议与证明
      零知识证明
        交互证明
        知识证明
        SNARKs, STARKs
      承诺方案
        隐藏与绑定
        Pedersen承诺
      秘密共享
        Shamir门限
        拉格朗日插值
      同态加密
        部分同态
        全同态
        Gentry方案
    后量子密码
      格密码
        LWE, Ring-LWE
        最坏情况到平均情况
      编码密码
        McEliece
        Goppa码
      多元密码
        MQ问题
        多项式方程组
      哈希签名
        Lamport签名
        Merkle树

```

---

## 困难问题与安全归约

```mermaid
graph TD
    subgraph 数学困难问题
        F[整数分解] --> RSA[RSA假设]
        DL[离散对数] --> DH[Diffie-Hellman]
        ECDL[椭圆曲线DL] --> ECDH[ECDH]
        SVP[最短向量] --> LWE[Learning With Errors]
    end
    
    subgraph 密码构造
        RSA1[RSA加密/签名] --> CPA1[IND-CPA安全]
        DH1[DH密钥交换] 
        ECDH1[ECIES加密] --> CCA1[IND-CCA安全]
        LWE1[Kyber加密] --> PQ[后量子安全]
    end
    
    RSA -.-> RSA1
    DH -.-> DH1
    ECDH -.-> ECDH1
    LWE -.-> LWE1
    
    style F fill:#ffcdd2
    style DL fill:#ffcdd2
    style ECDL fill:#ffcdd2
    style SVP fill:#ffcdd2

```

---

## 公钥密码系统对比

| 系统 | 数学基础 | 密钥长度(128位安全) | 主要运算 | 应用 |
|------|----------|---------------------|----------|------|
| RSA | 大整数分解 | 3072位 | 模幂运算 | 签名、加密 |
| ECC | 椭圆曲线DL | 256位 | 点乘法 | 密钥交换、签名 |
| Kyber | Module-LWE | 1536位 | 多项式乘法 | 密钥封装(KEM) |
| Dilithium | Module-LWE+SIS | 性 | 多项式运算 | 数字签名 |
| McEliece | 编码理论 | 1MB | 矩阵运算 | 加密(大密钥) |

---

## 零知识证明发展

```mermaid
timeline
    title 零知识证明发展历程
    1985 : Goldwasser-Micali-Rackoff
         : 交互零知识证明定义
    1986 : 第一个具体构造
         : 图同构/非同构
    1992 : Blum-Feldman-Micali
         : 非交互零知识(NIZK)
    2013 : Pinocchio协议
         : 实用的zk-SNARK
    2016 : zk-STARK
         : 透明设置，后量子安全
    2019 : Plonk
         : 通用可信设置

```

---

## 同态加密层次

```mermaid
mindmap
  root((同态加密<br/>Homomorphic Encryption))
    部分同态(PHE)
      加法同态
        Paillier加密
        投票系统
      乘法同态
        RSA(未填充)
        ElGamal
      有限次数
        支持加法和乘法
        但次数受限
    全同态(FHE)
      Gentry突破
        自举(Bootstrapping)
        2010年
      层次FHE
        leveled FHE
        预设电路深度
      自举优化
        环上LWE
        近似特征向量
      应用
        隐私计算
        外包计算
        安全机器学习

```

---

## 密码学中的高级数学

- **代数几何**: 椭圆曲线配对、超椭圆曲线密码
- **理想格**: 环上LWE、NTRU的安全性证明
- **表示论**: 代数密码分析中的群论方法
- **算术几何**: 椭圆曲线的L函数、BSD猜想关联
- **随机矩阵**: 密码分析中的统计方法

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数学×计算机科学 / 交叉学科*
