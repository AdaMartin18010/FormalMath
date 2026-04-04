# 线性规划思维导图

## 概述

线性规划是优化理论中最成熟的分支，研究线性目标函数在线性约束下的极值问题。自1947年单纯形法提出以来，线性规划已成为运筹学和决策科学的基础工具。

```mermaid
mindmap
  root((线性规划<br/>Linear Programming))
    基础理论
      标准形式
        原始形式
        对偶形式
        规范形式
      几何理论
        可行域多面体
        极点与极方向
        顶点解
      基本定理
        存在性定理
        基本最优性
        对偶定理
      退化与唯一性
    单纯形法
      基本思想
        顶点遍历
        相邻顶点
        改进方向
      算法步骤
        寻找初始基
        最优性检验
        换入换出
        枢轴运算
      单纯形表
        表格形式
        矩阵形式
        修正单纯形
      处理方法
        大M法
        两阶段法
        循环避免
    对偶理论
      对偶问题构造
        对称对偶
        非对称对偶
        混合对偶
      对偶定理
        弱对偶
        强对偶
        互补松弛
      对偶单纯形
        算法思想
        适用场景
      灵敏度分析
        右端项变化
        目标系数变化
        约束系数变化
    内点法
      障碍函数法
        对数障碍
        中心路径
        收敛分析
      原始对偶方法
        牛顿步
        步长选择
        预测校正
      复杂度分析
        多项式时间
        实际性能
      与单纯形比较
    网络流问题
      特殊结构
        全单模性
        整数解性质
      运输问题
        表上作业
        位势法
      指派问题
        匈牙利算法
        二分图匹配
      最大流最小割
        Ford-Fulkerson
        Edmonds-Karp
        Dinic算法
      最小费用流
        网络单纯形
        消圈算法
    整数线性规划
      建模技巧
        二进制变量
        逻辑约束
        分段线性
      分支定界
        分支策略
        定界方法
        剪枝规则
      割平面法
        Gomory割
        覆盖割
        提升投影
      启发式算法
        贪心算法
        局部搜索
        元启发式
    软件工具
      商业求解器
        CPLEX
        Gurobi
        Xpress
      开源求解器
        GLPK
        Clp
        SCIP
      建模语言
        AMPL
        GAMS
        PuLP
```

## 核心概念详解

### 1. 标准形式

**原始问题**：
$$\begin{aligned}
\min \quad & c^T x \\
\text{s.t.} \quad & Ax = b \\
& x \geq 0
\end{aligned}$$

**对偶问题**：
$$\begin{aligned}
\max \quad & b^T y \\
\text{s.t.} \quad & A^T y \leq c
\end{aligned}$$

### 2. 单纯形法迭代

```
1. 选择非基变量 x_j 使 c_j < 0（进基）
2. 计算方向 d = B⁻¹A_j
3. 确定步长 θ = min{b_i/d_i : d_i > 0}
4. 更新基，重复直到最优
```

### 3. 复杂度比较

| 方法 | 最坏复杂度 | 平均性能 | 适用规模 |
|------|-----------|----------|----------|
| 单纯形法 | 指数级 | 多项式 | 大规模稀疏 |
| 椭球法 | O(n⁶L) | 差 | 理论分析 |
| 内点法 | O(√n L) | 好 | 大规模稠密 |

### 4. 网络流特殊性

**全单模性**：约束矩阵 A 的所有方子行列式值为 0, ±1

**推论**：若 b 为整数，则 LP 存在整数最优解

## 相关主题

- [凸优化](./convex-optimization.md)
- [非线性规划](./nonlinear-programming.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Dantzig: "Linear Programming and Extensions"
- Bertsimas & Tsitsiklis: "Introduction to Linear Optimization"
- Vanderbei: "Linear Programming: Foundations and Extensions"
