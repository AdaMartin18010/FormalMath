---
msc_primary: 00

  - 00A99
  - 00A99
  - 00A99
title: 金融数学 / Mathematical Finance
processed_at: '2026-04-05'
---
# 金融数学 / Mathematical Finance

**最后更新**: 2026年4月4日

---

## 📋 分支概述

金融数学是应用数学的一个重要分支，运用随机分析、偏微分方程、概率论等数学工具研究金融市场中的定量问题。核心内容包括衍生品定价、风险管理、投资组合优化等。金融数学为现代金融工程提供了严谨的理论基础。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 随机微积分、期权定价、风险中性测度 | 91G20, @ | Shreve |
| [02-核心定理](./02-核心定理.md) | Black-Scholes公式、鞅表示定理 | 91G20, @ | Karatzas & Shreve |
| [03-实战问题](./03-实战问题.md) | 10个金融衍生品定价问题 | @ | Hull |

---

## 🎯 理论架构

```

金融数学
├── 随机分析基础
│   ├── 布朗运动
│   ├── 伊藤积分
│   ├── 伊藤引理
│   └── 随机微分方程
├── 衍生品定价理论
│   ├── Black-Scholes模型
│   ├── 鞅定价方法
│   ├── 风险中性测度
│   └── 完全市场理论
├── 利率模型
│   ├── 短期利率模型
│   ├── HJM框架
│   ├── LIBOR市场模型
│   └── 债券定价
├── 信用风险
│   ├── 违约强度模型
│   ├── 结构模型
│   ├── CDS定价
│   └── CDO定价
└── 投资组合理论
    ├── Markowitz均值-方差分析
    ├── CAPM模型
    ├── 效用最大化
    └── 随机控制方法

```

---

## 📚 核心人物

- **Louis Bachelier (1870-1946)**: 金融数学奠基人，首次用布朗运动描述股票价格
- **Fischer Black (1938-1995) & Myron Scholes (1941-2019)**: Black-Scholes期权定价模型（1973）
- **Robert Merton (1944-)**: 连续时间金融理论，与Scholes共享1997年诺贝尔经济学奖
- **Paul Samuelson (1915-2009)**: 将伊藤积分引入金融理论
- **Oldrich Vasicek (1942-)**: Vasicek利率模型

---

## 🔗 与其他分支的联系

- **概率论与随机过程**: 布朗运动、鞅理论、随机微分方程
- **偏微分方程**: Black-Scholes方程、Feynman-Kac公式
- **数值分析**: 蒙特卡洛模拟、有限差分方法
- **统计学**: 参数估计、时间序列分析、GARCH模型
- **优化理论**: 投资组合优化、风险度量

---

## 📖 学习路径建议

1. **先修知识**: 概率论、测度论、随机过程、偏微分方程基础
2. **第一阶段**: 离散时间模型（二叉树模型、Cox-Ross-Rubinstein）
3. **第二阶段**: 连续时间基础（布朗运动、伊藤积分）
4. **第三阶段**: 衍生品定价（Black-Scholes模型、鞅方法）
5. **第四阶段**: 高级专题（利率模型、信用风险、随机控制）

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Steven E. Shreve** - *Stochastic Calculus for Finance I & II* (2004)
- **Ioannis Karatzas & Steven E. Shreve** - *Brownian Motion and Stochastic Calculus* (2nd Edition, 1991)
- **John C. Hull** - *Options, Futures, and Other Derivatives* (10th Edition, 2017)
- **Damiano Brigo & Fabio Mercurio** - *Interest Rate Models: Theory and Practice* (2006)
- **Mark Joshi** - *The Concepts and Practice of Mathematical Finance* (2nd Edition, 2008)

---

*最后更新：2026年4月*
