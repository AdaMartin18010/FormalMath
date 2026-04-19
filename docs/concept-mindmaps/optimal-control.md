---
msc_primary: 00

  - 00A99
title: 最优控制思维导图
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 最优控制思维导图

## 概述

最优控制理论是现代控制理论的核心分支，研究如何使动态系统在给定性能指标下达到最优。它由Pontryagin等人于1950-60年代创立，综合了变分法、动态规划和微分方程理论。

```mermaid
mindmap
  root((最优控制<br/>Optimal Control))
    问题形式
      Bolza问题
        混合型指标
        终端约束
        路径约束
      Lagrange问题
        积分型指标
        时间最优
        能量最优
      Mayer问题
        终端型指标
        终端流形
        终端时间自由
      问题转换
        等价性定理
        状态增广
        时间变换
    连续时间理论
      Pontryagin原理
        正则方程
          状态方程
          协态方程
        极值条件
          最小值原理
          奇异控制
           bang-bang控制
        横截条件
          终端协态
          终端时间
          切换函数
      Hamilton-Jacobi
        HJB方程
          值函数
          验证定理
          粘性解
        特征线法
        反馈控制
      二阶条件
        加强Legendre
        Jacobi条件
        共轭点
    离散时间理论
      离散极大值原理
        差分状态
        差分协态
        离散Hamiltonian
      离散HJB
        值迭代
        策略迭代
      模型预测控制
        滚动时域
        稳定性分析
        鲁棒MPC
    特殊控制问题
      时间最优控制
        可控集
        等时区域
        切换曲面
      线性二次调节
        LQR问题
          Riccati方程
          稳态解
          稳定性保证
        LQG问题
          分离原理
          Kalman滤波
        跟踪问题
      奇异控制
        奇异弧
        Kelley条件
        高阶条件
      状态约束
        直接法
        间接法
        混合约束
      微分博弈
        Nash均衡
        Stackelberg
        Hamilton-Jacobi-Isaacs
    求解方法
      间接法
        打靶法
          单 shooting
          多 shooting
          同伦延拓
        边界值问题
          配点法
          有限差分
      直接法
        直接打靶
        配点变换
          伪谱法
          正交配点
        控制参数化
        直接转录
      数值优化
        SQP方法
        内点法
        稀疏结构
      实时算法
        显式MPC
        快速梯度
        在线优化
    鲁棒与随机
      H∞控制
        范数优化
        Riccati方法
        LMI方法
      μ分析
        结构奇异值
        鲁棒稳定性
      随机控制
        完全信息
        部分信息
        分离原理
      自适应控制
        在线估计
        双重控制
    应用领域
      航空航天
        轨道转移
        再入控制
        姿态控制
      机器人
        轨迹规划
        最优运动
        力控制
      过程工业
        化工过程
        电力系统
        能源管理
      生物医学
        药物动力学
        人工器官
        神经刺激
      经济学
        最优增长
        消费投资
        资源开采
      自动驾驶
        路径规划
        速度规划
        协同控制

```

## 核心概念详解

### 1. Pontryagin最小值原理

**标准问题**：
$$\min_{u} J = \phi(x(t_f)) + \int_{t_0}^{t_f} L(x,u,t) dt$$

**Hamiltonian**：
$$H(x,u,p,t) = L(x,u,t) + p^T f(x,u,t)$$

**必要条件**：
- 状态方程：$\dot{x} = \partial H / \partial p$
- 协态方程：$\dot{p} = -\partial H / \partial x$
- 极值条件：$H(x^*,u^*,p^*,t) = \min_u H(x^*,u,p^*,t)$
- 横截条件：$p(t_f) = \partial \phi / \partial x|_{t_f}$

### 2. Hamilton-Jacobi-Bellman方程

**连续时间**：
$$-\frac{\partial V}{\partial t} = \min_u \{L(x,u,t) + \nabla V \cdot f(x,u,t)\}$$

终端条件：$V(x,t_f) = \phi(x)$

**验证定理**：若 $V$ 是HJB方程的光滑解，则 $V$ 为最优值函数

### 3. 线性二次调节器

**问题**：
$$\min_u \int_0^\infty (x^TQx + u^TRu) dt$$

**解**：$u^* = -R^{-1}B^TPx = -Kx$

其中 $P$ 满足代数Riccati方程：
$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**性质**：若 $(A,B)$ 能控，$(A,Q^{1/2})$ 能观，则闭环稳定

### 4. 数值方法比较

| 方法 | 精度 | 收敛域 | 计算量 | 适用问题 |
|------|------|--------|--------|----------|
| 间接法 | 高 | 小 | 小 | 简单问题 |
| 直接配点 | 中 | 大 | 大 | 复杂约束 |
| 伪谱法 | 高 | 中 | 中 | 光滑解 |
| MPC | 次优 | 大 | 实时 | 在线控制 |

## 相关主题

- [变分法](./calculus-of-variations.md)
- [动态规划](./dynamic-programming.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Pontryagin et al.: "The Mathematical Theory of Optimal Processes"
- Bryson & Ho: "Applied Optimal Control"
- Lewis et al.: "Optimal Control"
- Rawlings & Mayne: "Model Predictive Control"
