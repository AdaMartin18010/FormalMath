---
msc_primary: 00A99
msc_secondary:
- 00A99
- 00A99
- 91A22
title: 生物数学 / Biomathematics
processed_at: '2026-04-05'
---
# 生物数学 / Biomathematics

**最后更新**: 2026年4月4日

---

## 📋 分支概述

生物数学是应用数学与生命科学的交叉学科，运用微分方程、动力系统、概率统计等数学工具研究生物现象。核心内容包括种群动力学、流行病模型、生物化学反应、进化博弈论等。生物数学为理解生态系统的动态行为和疾病传播提供了定量分析框架。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 种群动力学、流行病模型、进化博弈论 | 92B05, 92D25, 91A22 | Murray |
| [02-核心定理](./02-核心定理.md) | Lotka-Volterra稳定性、繁殖者方程 | 34D20, 92D25 | Hofbauer & Sigmund |
| [03-实战问题](./03-实战问题.md) | 10个生物建模问题 | 92Bxx | Edelstein-Keshet |

---

## 🎯 理论架构

```

生物数学
├── 种群动力学
│   ├── 单种群模型（指数增长、Logistic增长）
│   ├── Lotka-Volterra竞争模型
│   ├── Lotka-Volterra捕食-被捕食模型
│   └── 食物网与生态系统
├── 流行病模型
│   ├── SI模型
│   ├── SIS模型
│   ├── SIR模型
│   ├── SEIR模型
│   └── 网络传播模型
├── 生物化学反应
│   ├── Michaelis-Menten动力学
│   ├── 基因调控网络
│   └── 代谢网络分析
├── 进化动力学
│   ├── 复制者方程
│   ├── 进化稳定策略(ESS)
│   ├── 进化博弈论
│   └── 群体遗传学
└── 空间模型
    ├── 反应-扩散方程
    ├── 图灵斑图形成
    └── 种群空间分布

```

---

## 📚 核心人物

- **Alfred J. Lotka (1880-1949)**: Lotka-Volterra方程创始人，物理生物学家
- **Vito Volterra (1860-1940)**: 与Lotka独立发展捕食-被捕食模型
- **Ronald Ross (1857-1932)**: 疟疾传播数学模型，1902年诺贝尔奖
- **Kermack & McKendrick**: SIR流行病模型（1927）
- **John Maynard Smith (1920-2004)**: 进化博弈论和进化稳定策略
- **Karl Sigmund (1945-)**: 进化博弈论、复制者方程

---

## 🔗 与其他分支的联系

- **常微分方程**: 种群动态、化学反应的时序演化
- **动力系统**: 稳定性分析、分岔理论、混沌
- **偏微分方程**: 空间扩散、反应-扩散系统
- **概率论**: 随机种群模型、分支过程
- **博弈论**: 进化博弈、策略动力学
- **统计学**: 参数估计、数据拟合

---

## 📖 学习路径建议

1. **先修知识**: 常微分方程、线性代数、基础概率论
2. **第一阶段**: 单种群和双种群模型（Logistic、Lotka-Volterra）
3. **第二阶段**: 流行病模型和生化反应
4. **第三阶段**: 空间模型（反应-扩散方程）
5. **第四阶段**: 进化动力学和高级专题

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **James D. Murray** - *Mathematical Biology I & II* (3rd Edition, 2002-2003)
- **Leah Edelstein-Keshet** - *Mathematical Models in Biology* (1988)
- **Josef Hofbauer & Karl Sigmund** - *Evolutionary Games and Population Dynamics* (1998)
- **Nicholas F. Britton** - *Essential Mathematical Biology* (2003)
- **Fred Brauer & Carlos Castillo-Chavez** - *Mathematical Models in Population Biology and Epidemiology* (2012)

---

*最后更新：2026年4月*
