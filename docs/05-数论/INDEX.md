---
msc_primary: 11
title: 数论分支索引 / Number Theory Index
processed_at: '2026-04-08'
review_status: draft
---

# 数论分支索引 / Number Theory Index

> **最后更新**: 2026年4月8日  
> **MSC主类**: 11-00 (Number theory)  
> **国际对标**: MIT 18.785/18.786, Harvard Math 129/229/259X, Princeton MAT 419/451/455

---

## 📋 目录结构

```
docs/05-数论/
├── INDEX.md                          # 本索引文件
├── 00-README.md                      # 分支概述（待创建）
├── 01-初等数论/                     # Elementary Number Theory
│   ├── 01-整除理论.md               # Divisibility Theory [11A05]
│   ├── 02-同余理论.md               # Congruence Theory [11A07]
│   └── 03-原根与离散对数.md         # Primitive Roots & Discrete Log [11A07]
├── 02-解析数论/                     # Analytic Number Theory
│   ├── 01-素数定理.md               # Prime Number Theorem [11N05]
│   └── 02-Riemann假设.md            # Riemann Hypothesis [11M26]
├── 03-代数数论/                     # Algebraic Number Theory
│   └── 01-代数整数.md               # Algebraic Integers [11R04]
├── 04-算术几何/                     # Arithmetic Geometry
│   ├── 01-椭圆曲线.md               # Elliptic Curves [11G05]
│   └── 02-模形式.md                 # Modular Forms [11F11]
└── 07-深度扩展/                     # Advanced Extensions
    ├── 00-README.md
    ├── 04-类域论基础-深度扩展版.md
    ├── 05-椭圆曲线与BSD猜想-深度扩展版.md
    ├── 05-解析数论-深度扩展版.md
    ├── 06-模形式-深度扩展版.md
    ├── 06-模形式与L函数-深度扩展版.md
    ├── 07-代数数论深化-类域论基础.md
    ├── 07-代数数论的现代应用-深度扩展版.md
    └── 08-椭圆曲线算术-深度扩展版.md
```

---

## 📚 核心内容索引

### 初等数论 (01-初等数论/)

| 文档 | 核心概念 | MSC编码 | 前置知识 | 国际对标 |
|------|----------|---------|----------|----------|
| 01-整除理论.md | 整除、GCD、LCM、素数、算术基本定理 | 11A05 | 基础集合论 | MIT 18.310 |
| 02-同余理论.md | 同余、Euler定理、CRT、Fermat小定理 | 11A07 | 整除理论 | MIT 18.310 |
| 03-原根与离散对数.md | 阶、原根、离散对数、Diffie-Hellman | 11A07 | 同余理论 | MIT 18.783 |

### 解析数论 (02-解析数论/)

| 文档 | 核心概念 | MSC编码 | 前置知识 | 国际对标 |
|------|----------|---------|----------|----------|
| 01-素数定理.md | π(x)、li(x)、PNT、Dirichlet定理 | 11N05 | 复分析基础 | MIT 18.785 |
| 02-Riemann假设.md | ζ函数、零点、显式公式、RH等价形式 | 11M26 | 解析数论基础 | Harvard 229 |

### 代数数论 (03-代数数论/)

| 文档 | 核心概念 | MSC编码 | 前置知识 | 国际对标 |
|------|----------|---------|----------|----------|
| 01-代数整数.md | 代数整数、整数环、判别式、Dedekind整环 | 11R04 | 抽象代数 | Harvard 129 |

### 算术几何 (04-算术几何/)

| 文档 | 核心概念 | MSC编码 | 前置知识 | 国际对标 |
|------|----------|---------|----------|----------|
| 01-椭圆曲线.md | Weierstrass方程、群结构、Mordell-Weil、BSD | 11G05 | 代数几何基础 | Harvard 259X |
| 02-模形式.md | 模群、Eisenstein级数、Hecke算子、谷山-志村 | 11F11 | 复分析、表示论 | Princeton 419 |

---

## 🎯 学习路径

### 基础路线（本科生）

```
整除理论 → 同余理论 → 原根与离散对数
    ↓
素数定理（基础概念）
```

### 进阶路线（研究生）

```
初等数论基础
    ↓
代数数论（代数整数）
    ↓
解析数论（素数定理 → Riemann假设）
    ↓
算术几何（椭圆曲线 → 模形式）
```

### 专业路线（研究者）

```
代数数论深化 → 类域论
解析数论深化 → L函数理论
    ↓
Langlands纲领（算术几何高级主题）
```

---

## 🌍 国际课程对齐

### MIT课程映射

| MIT课程 | 课程名称 | 对应文档 |
|---------|----------|----------|
| 18.310 | Principles of Discrete Applied Math | 01-初等数论全系列 |
| 18.783 | Elliptic Curves | 04-算术几何/01-椭圆曲线.md |
| 18.785 | Number Theory I | 02-解析数论全系列、部分代数数论 |
| 18.786 | Number Theory II | 04-算术几何全系列、深度扩展 |

### Harvard课程映射

| Harvard课程 | 对应文档 |
|-------------|----------|
| Math 129 | Number Fields → 03-代数数论/ |
| Math 229 | Topics in Number Theory → 02-解析数论/深度扩展/ |
| Math 259X | Modular Forms → 04-算术几何/02-模形式.md |

### Princeton课程映射

| Princeton课程 | 对应文档 |
|---------------|----------|
| MAT 419 | Algebraic Number Theory → 03-代数数论/、深度扩展/ |
| MAT 451 | Analytic Number Theory → 02-解析数论/、深度扩展/ |
| MAT 455 | Arithmetic of Elliptic Curves → 04-算术几何/ |

---

## 🔢 MSC编码覆盖

### 一级分类

| MSC编码 | 分类名称 | 覆盖文档 |
|---------|----------|----------|
| 11A05 | 乘法结构；因子分解；素数 | 01-整除理论.md |
| 11A07 | 幂剩余与互反律 | 02-同余理论.md、03-原根与离散对数.md |
| 11N05 | 素数分布 | 01-素数定理.md |
| 11M26 | ζ函数与L函数的非实零点 | 02-Riemann假设.md |
| 11R04 | 代数数域：一般理论与整数环 | 01-代数整数.md |
| 11G05 | 椭圆曲线整体域 | 01-椭圆曲线.md |
| 11F11 | 全纯模形式 | 02-模形式.md |

---

## 🔗 关联文档

- [../](../) - 返回文档根目录
- [../01-基础数学/](../01-基础数学/) - 数学基础与集合论
- [../02-代数结构/](../02-代数结构/) - 抽象代数
- [../03-分析学/](../03-分析学/) - 复分析基础
- [../04-几何与拓扑/](../04-几何与拓扑/) - 代数几何基础

---

## 📊 内容统计

| 类别 | 文档数 | 主要定理 | 代码示例 |
|------|--------|----------|----------|
| 初等数论 | 3 | 15+ | 3 |
| 解析数论 | 2 | 10+ | 2 |
| 代数数论 | 1 | 8+ | 1 |
| 算术几何 | 2 | 12+ | 2 |
| **总计** | **8** | **45+** | **8** |

---

## 📖 参考文献

### 初等数论
- Hardy, G.H. & Wright, E.M. *An Introduction to the Theory of Numbers*. Oxford.
- Niven, I., Zuckerman, H.S., & Montgomery, H.L. *An Introduction to the Theory of Numbers*. Wiley.

### 解析数论
- Davenport, H. *Multiplicative Number Theory*. Springer.
- Iwaniec, H. & Kowalski, E. *Analytic Number Theory*. AMS.
- Montgomery, H.L. & Vaughan, R.C. *Multiplicative Number Theory I*. Cambridge.

### 代数数论
- Marcus, D.A. *Number Fields*. Springer.
- Neukirch, J. *Algebraic Number Theory*. Springer.

### 算术几何
- Silverman, J.H. *The Arithmetic of Elliptic Curves*. Springer.
- Diamond, F. & Shurman, J. *A First Course in Modular Forms*. Springer.

---

**最后更新**: 2026年4月8日
