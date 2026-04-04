---
msc_primary: "94Axx"
msc_secondary: ['60-XX', '68P30', '94Bxx']
---

# 信息论 / Information Theory

**最后更新**: 2026年4月4日

---

## 📋 分支概述

信息论是研究信息传输、存储和处理的数学理论，由Claude Shannon于1948年创立。它提供了量化信息的数学框架，是现代通信、数据压缩、密码学的理论基础。本分支系统构建信息论的完整理论体系。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 熵、互信息、信道容量 | 94A15, 94A17 | Cover & Thomas |
| [02-核心定理](./02-核心定理.md) | 信道编码定理、率失真理论 | 94A24, 94A29 | Shannon |
| [03-实战问题](./03-实战问题.md) | 5个经典信息论问题 | 94Axx | 信息论经典习题集 |

---

## 🎯 理论架构

```

信息论
├── 信息度量
│   ├── 香农熵
│   ├── 互信息
│   └── 相对熵
├── 信源编码
│   ├── 无损编码
│   ├── 有损编码
│   └── 率失真理论
├── 信道编码
│   ├── 信道容量
│   ├── 信道编码定理
│   └── 纠错码
└── 高级专题
    ├── 网络信息论
    ├── 多用户信息论
    └── 量子信息论

```

---

## 📚 核心人物

- **Claude E. Shannon (1916-2001)**: 信息论创始人，《通信的数学理论》
- **Richard Hamming (1915-1998)**: 纠错码理论，Hamming码
- **David Huffman (1925-1999)**: Huffman编码
- **Andrey Kolmogorov (1903-1987)**: 算法信息论（Kolmogorov复杂度）
- **Robert Fano (1917-2016)**: Fano不等式、香农-范诺编码

---

## 🔗 与其他分支的联系

- **概率论**: 信息度量基于概率分布
- **统计学**: 统计推断与信息不等式
- **编码理论**: 纠错码与信道容量
- **密码学**: 信息论安全、完美保密
- **机器学习**: 信息瓶颈、特征选择

---

## 📖 学习路径建议

1. **先修知识**: 概率论、离散数学
2. **第一阶段**: 信息度量（熵、互信息、相对熵）
3. **第二阶段**: 信源编码（Huffman编码、算术编码、率失真）
4. **第三阶段**: 信道编码（信道容量、编码定理）
5. **第四阶段**: 高级专题（网络信息论、量子信息论）

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Thomas M. Cover & Joy A. Thomas** - *Elements of Information Theory* (2nd Edition, 2006)
- **David J.C. MacKay** - *Information Theory, Inference, and Learning Algorithms* (2003)
- **Robert G. Gallager** - *Information Theory and Reliable Communication* (1968)
- **Imre Csiszár & János Körner** - *Information Theory: Coding Theorems for Discrete Memoryless Systems* (2011)
- **Claude E. Shannon & Warren Weaver** - *The Mathematical Theory of Communication* (1949)

---

*最后更新：2026年4月*
