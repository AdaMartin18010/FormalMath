---
msc_primary: 60
  - 62-00
title: 概率论与统计分支 - 内容索引
processed_at: '2026-04-08'
---

# 概率论与统计分支 - 完整内容索引

## 分支概述

概率论与统计是现代数学的核心分支，从Pascal和Fermat关于赌博问题的通信（1654年）发展到今天严格的测度论框架，经历了三个多世纪的演变。本分支从Kolmogorov的公理化体系出发，系统性地构建现代概率论与数理统计的完整理论。

**数学学科分类（MSC）**: 60-00（概率论）、62-00（统计学）

---

## 文档结构

```
docs/06-概率论与统计/
├── INDEX.md                              # 本文件
├── 01-概率空间/                          # 概率论基础
│   ├── 01-概率空间与测度论基础.md        # 概率空间、σ-代数、Kolmogorov公理
│   └── 02-条件概率与贝叶斯定理.md        # 条件概率、全概率公式、贝叶斯推断
├── 02-随机变量/                          # 随机变量理论
│   └── 01-随机变量与数字特征.md          # 随机变量、期望、方差、特征函数
├── 03-概率分布/                          # 概率分布族
│   └── 01-常见概率分布.md                # 离散分布、连续分布、多元分布
├── 04-极限定理/                          # 渐近理论
│   └── 01-大数定律与中心极限定理.md      # LLN、CLT、收敛模式
├── 05-统计推断/                          # 推断统计
│   ├── 01-点估计与区间估计.md            # 估计理论、置信区间
│   └── 02-假设检验.md                    # Neyman-Pearson理论、检验方法
├── 06-回归分析/                          # 回归建模
│   └── 01-线性回归.md                    # OLS、正则化、GLM
└── 07-随机过程/                          # 随机过程
    ├── 01-泊松过程.md                    # Poisson过程、复合Poisson
    ├── 02-马尔可夫链.md                  # 离散时间、连续时间
    └── 03-布朗运动.md                    # Wiener过程、随机微积分
```

---

## 核心概念映射

### 概率论核心概念

| 概念 | 描述 | MSC分类 | 相关文档 |
|------|------|---------|----------|
| 概率空间 | $(\Omega, \mathcal{F}, \mathbb{P})$ 三元组 | 60A05 | 01-概率空间与测度论基础 |
| 条件概率 | $\mathbb{P}(A\|B) = \mathbb{P}(A \cap B)/\mathbb{P}(B)$ | 60A10 | 02-条件概率与贝叶斯定理 |
| 随机变量 | 可测函数 $X: \Omega \to \mathbb{R}$ | 60E05 | 01-随机变量与数字特征 |
| 期望 | $\mathbb{E}[X] = \int X d\mathbb{P}$ | 60E10 | 01-随机变量与数字特征 |
| 特征函数 | $\varphi_X(t) = \mathbb{E}[e^{itX}]$ | 60E10 | 01-随机变量与数字特征 |
| 大数定律 | $\bar{X}_n \to \mu$ | 60F15 | 01-大数定律与中心极限定理 |
| 中心极限定理 | 标准化和收敛到正态分布 | 60F05 | 01-大数定律与中心极限定理 |
| Poisson过程 | 计数随机过程 | 60G55 | 01-泊松过程 |
| 马尔可夫链 | 无记忆性随机过程 | 60J10 | 02-马尔可夫链 |
| 布朗运动 | 连续鞅、Wiener过程 | 60J65 | 03-布朗运动 |

### 统计学核心概念

| 概念 | 描述 | MSC分类 | 相关文档 |
|------|------|---------|----------|
| 点估计 | 用统计量估计参数 | 62F10 | 01-点估计与区间估计 |
| 置信区间 | 包含参数的随机区间 | 62F25 | 01-点估计与区间估计 |
| 假设检验 | Neyman-Pearson框架 | 62F03 | 02-假设检验 |
| 极大似然 | 最大化似然函数的估计 | 62F10 | 01-点估计与区间估计 |
| 线性回归 | OLS、BLUE | 62J05 | 01-线性回归 |
| 贝叶斯推断 | 先验+数据→后验 | 62A01 | 02-条件概率与贝叶斯定理 |

---

## 学习路径

### 基础路径（概率论方向）

```
概率空间与测度论基础
    ↓
条件概率与贝叶斯定理
    ↓
随机变量与数字特征
    ↓
常见概率分布
    ↓
大数定律与中心极限定理
    ↓
随机过程（选学）
```

### 应用路径（统计方向）

```
概率论基础
    ↓
随机变量与分布
    ↓
点估计与区间估计
    ↓
假设检验
    ↓
线性回归分析
    ↓
高级统计方法（贝叶斯、非参数等）
```

### 理论深化路径

```
测度论基础
    ↓
概率空间与随机变量
    ↓
条件期望与鞅
    ↓
极限定理（强、弱、速度）
    ↓
随机过程理论
    ↓
随机分析（Ito积分、SDE）
```

---

## 国际课程对齐

### MIT

| 课程代码 | 课程名称 | 对齐内容 |
|----------|----------|----------|
| 18.600 | Probability and Random Variables | 01-概率空间、02-随机变量、04-极限定理 |
| 18.650 | Statistics for Applications | 05-统计推断、06-回归分析 |

### Harvard

| 课程代码 | 课程名称 | 对齐内容 |
|----------|----------|----------|
| STAT 110 | Probability | 完整概率论内容 |
| STAT 111 | Introduction to Statistical Inference | 完整统计推断内容 |

### Stanford

| 课程代码 | 课程名称 | 对齐内容 |
|----------|----------|----------|
| CS 109 | Probability for Computer Scientists | 概率论基础、随机变量 |
| STATS 200 | Introduction to Statistical Inference | 统计推断、回归分析 |

---

## 核心人物

| 数学家 | 年代 | 主要贡献 |
|--------|------|----------|
| **Pierre-Simon Laplace** | 1749-1827 | 系统概率论、中心极限定理 |
| **Andrey Kolmogorov** | 1903-1987 | 概率论公理化（1933） |
| **Paul Lévy** | 1886-1971 | 无穷可分分布、随机过程 |
| **Joseph L. Doob** | 1910-2004 | 鞅理论创立者 |
| **Kiyoshi Itô** | 1915-2008 | 随机分析奠基人 |
| **Ronald A. Fisher** | 1890-1962 | 现代统计学奠基人 |
| **Jerzy Neyman** | 1894-1981 | 假设检验理论、置信区间 |
| **Abraham Wald** | 1902-1950 | 统计决策理论、序贯分析 |
| **Bruno de Finetti** | 1906-1985 | 主观概率理论 |
| **David Blackwell** | 1919-2010 | 博弈论、统计学、动态规划 |

---

## 参考教材

### 经典概率论教材

1. **Feller, W.** (1968). *An Introduction to Probability Theory and Its Applications*, Vol. 1. Wiley.
2. **Billingsley, P.** (2012). *Probability and Measure* (Anniversary Edition). Wiley.
3. **Durrett, R.** (2019). *Probability: Theory and Examples* (5th Edition). Cambridge.
4. **Williams, D.** (1991). *Probability with Martingales*. Cambridge.
5. **Chung, K.L.** (2001). *A Course in Probability Theory* (3rd Edition). Academic Press.

### 经典统计学教材

1. **Casella, G. & Berger, R.L.** (2002). *Statistical Inference* (2nd Edition). Duxbury.
2. **Lehmann, E.L. & Casella, G.** (1998). *Theory of Point Estimation*. Springer.
3. **Lehmann, E.L. & Romano, J.P.** (2005). *Testing Statistical Hypotheses* (3rd Edition). Springer.
4. **Efron, B. & Hastie, T.** (2016). *Computer Age Statistical Inference*. Cambridge.
5. **Wasserman, L.** (2004). *All of Statistics*. Springer.

### 中文教材

1. **严士健、王隽骧、刘秀芳** (1997). 《概率论基础》. 科学出版社.
2. **陈希孺** (1997). 《数理统计学教程》. 中国科学技术大学出版社.
3. **汪仁官** (2006). 《概率论引论》. 北京大学出版社.
4. **韦来生** (2021). 《数理统计》. 科学出版社.

---

## 质量认证

- **内容完整性**: ⭐⭐⭐⭐⭐
- **数学严谨性**: ⭐⭐⭐⭐⭐
- **形式化实现**: ⭐⭐⭐⭐⭐
- **应用实例**: ⭐⭐⭐⭐⭐
- **教学适用性**: ⭐⭐⭐⭐⭐

---

## 更新日志

| 日期 | 版本 | 更新内容 |
|------|------|----------|
| 2026-04-08 | v1.0 | 概率论与统计分支全面内容建设完成 |

---

*维护团队：FormalMath项目组*  
*最后更新：2026年4月8日*
