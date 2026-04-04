# 应用数学概念MSC2020编码对照表

## 概述
本文档为FormalMath项目中应用数学核心概念提供MSC2020编码对照。

## MSC2020编码说明
- **60-XX**: 概率论与随机过程 (Probability theory and stochastic processes)
- **62-XX**: 统计学 (Statistics)
- **65-XX**: 数值分析 (Numerical analysis)
- **68-XX**: 计算机科学 (Computer science)
- **90-XX**: 运筹学, 数学规划 (Operations research, mathematical programming)

---

## 概率统计类 (Probability & Statistics)

| 概念(中文) | 概念(英文) | 概念ID | MSC编码 | 说明 |
|-----------|-----------|--------|---------|------|
| 概率测度 | Probability Measure | probability_measure | 60A10 | 概率测度与积分理论 |
| 随机变量 | Random Variable | random_variable | 60A99 | 随机变量基础理论 |
| 期望 | Expectation | expectation | 60A99 | 数学期望 |
| 方差 | Variance | variance | 60A99 | 方差与标准差 |
| 期望方差 | Expectation and Variance | expectation_variance | 62J99 | 统计推断基础 |
| 大数定律 | Law of Large Numbers | law_of_large_numbers | 60F15 | 强大数定律 |
| 中心极限定理 | Central Limit Theorem | central_limit_theorem | 60F05 | 中心极限定理 |
| 随机过程 | Stochastic Process | stochastic_process | 60G07 | 随机过程基础 |
| 布朗运动 | Brownian Motion | brownian_motion | 60J65 | 布朗运动与维纳过程 |
| 马尔可夫链 | Markov Chain | markov_chain | 60J10 | 离散时间马尔可夫链 |
| 鞅 | Martingale | martingale | 60G48 | 离散参数鞅 |

---

## 最优化类 (Optimization)

| 概念(中文) | 概念(英文) | 概念ID | MSC编码 | 说明 |
|-----------|-----------|--------|---------|------|
| 凸优化 | Convex Optimization | convex_optimization | 90C25 | 凸规划与凸优化 |
| 线性规划 | Linear Programming | linear_programming | 90C05 | 线性规划 |
| 梯度下降 | Gradient Descent | gradient_descent | 90C30 | 非线性规划中的梯度方法 |
| 拉格朗日乘子 | Lagrange Multiplier | lagrange_multiplier | 90C46 | 约束优化的拉格朗日乘子 |

---

## 计算数学类 (Computational Mathematics)

| 概念(中文) | 概念(英文) | 概念ID | MSC编码 | 说明 |
|-----------|-----------|--------|---------|------|
| 数值积分 | Numerical Integration | numerical_integration | 65D30 | 数值积分与求积公式 |
| 插值 | Interpolation | interpolation | 65D05 | 插值与逼近 |
| 线性方程组求解 | Linear System Solver | linear_system_solver | 65F10 | 迭代法求解线性系统 |
| 特征值计算 | Eigenvalue Computation | eigenvalue_computation | 65F15 | 矩阵特征值计算 |

---

## 数据科学类 (Data Science)

| 概念(中文) | 概念(英文) | 概念ID | MSC编码 | 说明 |
|-----------|-----------|--------|---------|------|
| 机器学习 | Machine Learning | machine_learning | 68T05 | 机器学习与人工智能 |
| 深度学习 | Deep Learning | deep_learning | 68T07 | 深度学习与神经网络 |
| 统计学习理论 | Statistical Learning Theory | statistical_learning_theory | 62G99 | 非参数推断与学习理论 |

---

## 编码总览

### 按类别统计
- 概率统计类: 11个概念
- 最优化类: 4个概念
- 计算数学类: 4个概念
- 数据科学类: 3个概念
- **总计: 22个概念** (包含期望和方差分开计算)

### 按MSC大类统计
- 60-XX (概率论): 11个
- 62-XX (统计学): 2个
- 65-XX (数值分析): 4个
- 68-XX (计算机科学): 2个
- 90-XX (运筹学): 4个

---

## 参考
- [MSC2020官方文档](https://mathscinet.ams.org/mathscinet/msc/msc2020.html)
- FormalMath概念前置关系数据库 v3.0
