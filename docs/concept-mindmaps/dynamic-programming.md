---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 动态规划思维导图
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 动态规划思维导图

## 概述

动态规划是解决多阶段决策问题的强大方法，由Bellman于1950年代创立。其核心思想是最优性原理：最优策略的子策略也是最优的。适用于离散/连续时间、确定/随机环境。

```mermaid
mindmap
  root((动态规划<br/>Dynamic Programming))
    基础理论
      最优性原理
        Bellman原理
        最优子结构
        重叠子问题
      值函数
        定义与性质
        值迭代
        单调性与凹性
      策略迭代
        策略评估
        策略改进
        收敛性
      收缩映射
        压缩因子
        Banach不动点
        收敛速率
    离散时间DP
      确定性DP
        有限时域
          前向DP
          后向DP
          边界条件
        无限时域
          折扣准则
          平均准则
          总报酬准则
      随机DP
        MDP框架
          状态空间
          动作空间
          转移概率
          报酬函数
        有限时域SDP
        无限时域SDP
          折扣MDP
          平均报酬MDP
      结构性质
        单调策略
        凸性保持
        阈值策略
    连续时间DP
      确定性最优控制
        Hamilton-Jacobi
        验证定理
        值函数光滑性
      随机最优控制
        HJB方程
        粘性解
        鞅问题
      脉冲控制
        拟变分不等式
        最优停止
        混合控制
    求解方法
      数值方法
        值迭代
          同步更新
          异步更新
          Gauss-Seidel
        策略迭代
          精确评估
          截断评估
          修正策略迭代
        线性规划法
          原始LP
          对偶LP
      近似方法
        函数逼近
          线性逼近
          神经网络
          核方法
         rollout算法
          基策略
          多步前瞻
        蒙特卡洛
          首次访问
          每次访问
      强化学习
        时序差分
          TD(0)
          TD(λ)
          n步回报
        Q学习
          离策略
          收敛性
          探索策略
        SARSA
          在策略
          函数逼近
    应用
      资源分配
        背包问题
        库存管理
        投资组合
      路径优化
        最短路径
        旅行商问题
        车辆路径
      博弈论
        马尔可夫博弈
        微分博弈
        均衡策略
      金融工程
        期权定价
        消费投资
        风险管理
      运营管理
        生产调度
        维修策略
        排队控制
      机器学习
        序列决策
        策略梯度
        Actor-Critic
    前沿研究
      大规模问题
        分布式DP
        联邦RL
        并行计算
      理论分析
        样本复杂度
        近似误差
        泛化界
      深度RL
        DQN
        A3C/PPO
        MuZero

```

## 核心概念详解

### 1. Bellman方程

**离散时间（确定性）**：
$$V_t(x) = \min_{u \in U(x)} \{g_t(x,u) + V_{t+1}(f_t(x,u))\}$$

**离散时间（随机，MDP）**：
$$V^*(x) = \min_{u \in U(x)} \{g(x,u) + \gamma \sum_{y} P(y|x,u)V^*(y)\}$$

**连续时间（HJB方程）**：
$$\rho V = \min_u \{g(x,u) + \nabla V \cdot f(x,u)\} + \frac{1}{2}\text{tr}(\sigma\sigma^T \nabla^2 V)$$

### 2. 算法比较

| 方法 | 存储需求 | 计算量 | 收敛速度 |
|------|----------|--------|----------|
| 值迭代 | O(\|S\|\|A\|) | O(\|S\|²\|A\|) | 线性 |
| 策略迭代 | O(\|S\|²) | 解线性方程组 | 二次 |
| Q学习 | O(\|S\|\|A\|) | 样本驱动 | 渐近 |

### 3. 收敛性条件

**值迭代收敛**：
- 折扣因子 γ ∈ [0,1)
- 或：所有策略 proper（有限步终止）

**策略迭代收敛**：
- 有限状态/动作空间
- 或：满足一定正则条件

### 4. 近似动态规划

**线性架构**：
$$\tilde{V}(x; r) = \sum_{i=1}^k r_i \phi_i(x) = \phi(x)^T r$$

**投影Bellman方程**：
$$\Phi r = \Pi T(\Phi r)$$

其中 Π 是到特征空间的投影，T 是Bellman算子

## 相关主题

- [最优控制](./optimal-control.md)
- [随机优化](./stochastic-optimization.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Bertsekas: "Dynamic Programming and Optimal Control"
- Puterman: "Markov Decision Processes"
- Powell: "Approximate Dynamic Programming"
- Sutton & Barto: "Reinforcement Learning"
