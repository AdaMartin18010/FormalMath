---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 概率论与随机过程

msc_primary: 60xx

## 分支概述

概率论与随机过程是现代数学的核心分支之一，从Pascal和Fermat关于赌博问题的通信（1654年）发展到今天严格的测度论框架，经历了三个多世纪的演变。本分支从Kolmogorov的公理化体系出发，系统性地构建现代概率论的完整理论，并深入到随机分析的前沿领域。

### 历史脉络

**古典时期（1654-1900）**

- 1654年：Pascal与Fermat的通信奠定概率论基础
- 1713年：Bernoulli《猜度术》提出大数定律
- 1733年：de Moivre证明中心极限定理特例
- 1812年：Laplace《概率分析理论》系统总结古典概率

**测度论时期（1900-1950）**

- 1900年：Borel创立测度论
- 1933年：Kolmogorov《概率论基础》建立公理化体系
- 1930年代：Lévy发展无穷可分分布理论
- 1940年代：Doob创立鞅理论

**随机分析时期（1950-今）**

- 1944年：Itô创立随机积分理论
- 1973年：Black-Scholes期权定价公式
- 1980年代：Malliavin分析创立
- 1990年代：粗糙路径理论（Lyons）

### 理论架构

```

概率论与随机过程
├── 测度论基础
│   ├── Kolmogorov公理化
│   ├── 随机变量与分布
│   ├── 条件期望
│   └── 收敛性理论
├── 随机过程
│   ├── 有限维分布
│   ├── 布朗运动
│   ├── 鞅理论
│   └── 马尔可夫过程
└── 随机微积分
    ├── Itô积分
    ├── Itô公式
    ├── 随机微分方程
    └── 金融应用

```

### 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-测度论概率基础-深度版](./01-测度论概率基础-深度版.md) | Kolmogorov公理化、随机变量、期望、收敛性 | 60Axx, 60Bxx | Durrett, Billingsley |
| [02-随机过程基础-深度版](./02-随机过程基础-深度版.md) | 布朗运动、鞅、马尔可夫过程 | 60Gxx, 60Jxx | Karatzas-Shreve, Revuz-Yor |
| [03-随机微积分-深度版](./03-随机微积分-深度版.md) | Itô积分、SDE、Black-Scholes | 60Hxx, 91Gxx | Øksendal, Shreve |

### 核心人物

- **Andrey Kolmogorov (1903-1987)**：概率论公理化奠基人，1933年出版《概率论基础》
- **Norbert Wiener (1894-1964)**：布朗运动数学理论的创立者，1923年严格构造Wiener过程
- **Kiyoshi Itô (1915-2008)**：随机分析奠基人，创立Itô积分和Itô公式
- **Joseph L. Doob (1910-2004)**：鞅理论创立者，《随机过程》经典著作
- **Fischer Black (1938-1995)** & **Myron Scholes (1941-)**：Black-Scholes期权定价模型，1997年诺贝尔经济学奖

### 与项目其他分支的联系

- **实分析**：测度论与积分理论是概率论的严格基础
- **泛函分析**：随机过程取值于函数空间，需要泛函分析工具
- **偏微分方程**：Kolmogorov向前/向后方程，Feynman-Kac公式
- **数值分析**：随机微分方程的数值解法（Euler-Maruyama等）
- **数理金融**：衍生品定价、风险管理的核心数学工具

### 学习路径建议

1. **先修知识**：实分析（测度与积分）、泛函分析基础
2. **第一阶段**：测度论概率基础（概率空间、随机变量、条件期望）
3. **第二阶段**：极限理论（大数定律、中心极限定理）
4. **第三阶段**：随机过程（布朗运动、鞅、马尔可夫过程）
5. **第四阶段**：随机微积分（Itô积分、SDE）
6. **第五阶段**：应用专题（金融、滤波、控制）

### 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Rick Durrett** - *Probability: Theory and Examples* (5th Edition, 2019)
- **Patrick Billingsley** - *Probability and Measure* (Anniversary Edition, 2012)
- **Ioannis Karatzas & Steven Shreve** - *Brownian Motion and Stochastic Calculus* (2nd Edition, 1991)
- **Daniel Revuz & Marc Yor** - *Continuous Martingales and Brownian Motion* (3rd Edition, 1999)
- **Bernt Øksendal** - *Stochastic Differential Equations* (6th Edition, 2003)
- **Steven Shreve** - *Stochastic Calculus for Finance II: Continuous-Time Models* (2004)

---

*最后更新：2026年4月*
