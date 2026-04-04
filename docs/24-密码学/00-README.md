---
msc_primary: "94A60"
msc_secondary: ['11T71', '14G50', '68P25']
---

# 密码学 / Cryptography

**最后更新**: 2026年4月4日

---

## 📋 分支概述

密码学是研究信息安全和通信保密的数学分支，包括对称密码学、公钥密码学和现代密码协议。它结合了数论、代数、计算复杂性理论等数学工具，为信息安全提供理论基础和实用方案。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 对称加密、公钥加密、零知识证明 | 94A60, 94A62 | Katz & Lindell |
| [02-核心定理](./02-核心定理.md) | RSA正确性、椭圆曲线安全性 | 11T71, 14G50 | Silverman |
| [03-实战问题](./03-实战问题.md) | 5个经典密码学问题 | 94Axx | 密码学经典习题集 |

---

## 🎯 理论架构

```

密码学
├── 对称密码学
│   ├── 流密码
│   ├── 分组密码
│   └── 消息认证码
├── 公钥密码学
│   ├── RSA加密
│   ├── 椭圆曲线密码
│   └── Diffie-Hellman密钥交换
├── 密码协议
│   ├── 数字签名
│   ├── 零知识证明
│   └── 多方计算
└── 密码分析
    ├── 经典攻击方法
    ├── 侧信道攻击
    └── 量子密码分析

```

---

## 📚 核心人物

- **Claude Shannon (1916-2001)**: 信息论安全理论奠基人
- **Whitfield Diffie & Martin Hellman**: 公钥密码学创始人（1976）
- **Ron Rivest, Adi Shamir, Leonard Adleman**: RSA算法（1977）
- **Shafi Goldwasser & Silvio Micali**: 概率加密、零知识证明
- **Neal Koblitz & Victor Miller**: 椭圆曲线密码学（1985）

---

## 🔗 与其他分支的联系

- **数论**: RSA、离散对数问题基于数论难题
- **代数**: 群论、环论、有限域在密码学中广泛应用
- **信息论**: 信息论安全、完美保密
- **计算复杂性**: 密码安全性归约到困难问题
- **概率论**: 概率加密、随机预言机模型

---

## 📖 学习路径建议

1. **先修知识**: 离散数学、基础数论、概率论
2. **第一阶段**: 对称密码学（流密码、分组密码、AES）
3. **第二阶段**: 公钥密码学（RSA、ElGamal、ECC）
4. **第三阶段**: 密码协议（数字签名、零知识证明）
5. **第四阶段**: 高级专题（格密码、同态加密、量子密码）

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Jonathan Katz & Yehuda Lindell** - *Introduction to Modern Cryptography* (3rd Edition, 2020)
- **Oded Goldreich** - *Foundations of Cryptography* (Vols. 1-2, 2001-2004)
- **Alfred J. Menezes, Paul C. van Oorschot & Scott A. Vanstone** - *Handbook of Applied Cryptography* (1996)
- **Neal Koblitz** - *A Course in Number Theory and Cryptography* (2nd Edition, 1994)
- **Joseph H. Silverman** - *The Arithmetic of Elliptic Curves* (2nd Edition, 2009)

---

*最后更新：2026年4月*
