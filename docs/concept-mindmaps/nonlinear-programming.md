# 非线性规划思维导图

## 概述

非线性规划研究目标函数或约束条件为非线性函数的优化问题。与线性规划相比，非线性规划更加一般化，但求解难度也显著增加，可能出现多个局部最优解。

```mermaid
mindmap
  root((非线性规划<br/>Nonlinear Programming))
    问题分类
      无约束优化
        光滑函数
        非光滑函数
        大规模问题
      等式约束
        拉格朗日乘子
        消元法
        流形优化
      不等式约束
        KKT条件
        积极集法
        障碍法
      混合约束
        一般NLP
        MINLP
        互补约束
      特殊结构
        二次规划
        二次约束QP
        几何规划
    最优性条件
      一阶必要条件
        梯度为零
        约束规范
        KKT条件
      二阶条件
        二阶必要
        二阶充分
        海森矩阵
      约束规范
        LICQ
        MFCQ
        Slater条件
      对偶性
        拉格朗日对偶
        Wolfe对偶
        间隙分析
    无约束算法
      线搜索方法
        最速下降
        牛顿法
        拟牛顿法
          DFP
          BFGS
          L-BFGS
        共轭梯度
          FR方法
          PR方法
          预条件
      信赖域方法
        柯西点
        狗腿法
        Steihaug-CG
      非光滑优化
        次梯度法
        束方法
        邻近点法
      全局优化
        随机搜索
        遗传算法
        模拟退火
    约束算法
      惩罚函数法
        外点法
        内点法
        精确惩罚
      增广拉格朗日
        等式约束
        不等式约束
        乘子更新
      序列二次规划
        局部SQP
        全局收敛
        超线性收敛
      内点法
        原始内点
        原始对偶
        滤子法
      积极集法
        梯度投影
        有效集识别
    全局优化
      分支定界
        凸松弛
        区间分析
        空间分支
      多起点策略
        随机采样
        聚类分析
      凸包络近似
        McCormick
        α-BB方法
        分段线性
      确定性方法
        区间方法
        Lipschitz优化
    变分与互补
      变分不等式
        单调算子
        投影方法
        间隙函数
      互补问题
        NCP函数
        光滑化
        半光滑牛顿
      均衡约束
        MPEC
        正则化
        松弛方法
    应用
      工程设计
        结构优化
        参数估计
        电路设计
      经济学
        均衡模型
        效用最大化
        博弈论
      机器学习
        神经网络训练
        核方法
        深度网络
      化学工程
        过程优化
        反应器设计
```

## 核心概念详解

### 1. KKT条件

对于问题：
$$\begin{aligned}
\min \quad & f(x) \\
\text{s.t.} \quad & g_i(x) \leq 0, \; i=1,...,m \\
& h_j(x) = 0, \; j=1,...,p
\end{aligned}$$

**KKT条件**：
- 平稳性：∇f(x) + Σλᵢ∇gᵢ(x) + Σνⱼ∇hⱼ(x) = 0
- 原始可行性：gᵢ(x) ≤ 0, hⱼ(x) = 0
- 对偶可行性：λᵢ ≥ 0
- 互补松弛：λᵢgᵢ(x) = 0

### 2. 牛顿法与拟牛顿法

**牛顿法**：
$$x_{k+1} = x_k - [\nabla^2 f(x_k)]^{-1} \nabla f(x_k)$$

**BFGS更新**：
$$B_{k+1} = B_k - \frac{B_k s_k s_k^T B_k}{s_k^T B_k s_k} + \frac{y_k y_k^T}{y_k^T s_k}$$

### 3. SQP方法

每步求解子问题：
$$\begin{aligned}
\min \quad & \nabla f_k^T d + \frac{1}{2}d^T W_k d \\
\text{s.t.} \quad & g(x_k) + \nabla g(x_k)^T d \leq 0 \\
& h(x_k) + \nabla h(x_k)^T d = 0
\end{aligned}$$

### 4. 收敛速率

| 方法 | 收敛阶 | 收敛条件 |
|------|--------|----------|
| 梯度下降 | 线性 | 强凸性 |
| 牛顿法 | 二次 | 接近最优 |
| 拟牛顿 | 超线性 | 凸性 |
| SQP | 超线性 | LICQ, SSC |

## 相关主题

- [凸优化](./convex-optimization.md)
- [最优控制](./optimal-control.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Nocedal & Wright: "Numerical Optimization"
- Bazaraa et al.: "Nonlinear Programming"
- Bertsekas: "Nonlinear Programming"
