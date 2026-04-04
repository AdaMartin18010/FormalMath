# 随机优化思维导图

## 概述

随机优化研究包含不确定性的优化问题，在机器学习、金融工程、运营管理等领域有广泛应用。它涵盖随机规划、随机逼近、鲁棒优化等方法，处理数据噪声、模型不确定性和环境随机性。

```mermaid
mindmap
  root((随机优化<br/>Stochastic Optimization))
    问题类型
      随机规划
        两阶段问题
          追索问题
          完全追索
          相对完全追索
        多阶段问题
          决策树
          情景树
          非预期约束
        概率约束
          机会约束
          联合约束
          个体约束
      鲁棒优化
        集合鲁棒
          盒式不确定
          椭球不确定
          多面体不确定
        分布鲁棒
          矩约束
          φ-散度
          Wasserstein
        可调鲁棒
          仿射决策
          分段仿射
      随机逼近
        无约束SA
          Robbins-Monro
          Kiefer-Wolfowitz
          收敛速率
        约束SA
          投影SA
          随机拟梯度
          随机次梯度
      在线优化
        遗憾分析
          静态遗憾
          动态遗憾
          约束遗憾
        对抗设置
        随机设置
    两阶段随机规划
      问题形式
        第一 stage
          决策x
          成本cᵀx
        第二 stage
          追索决策y
          追索成本Q(x,ξ)
      期望追索
        积分形式
        可测性条件
        L-shaped方法
      求解方法
        样本平均近似
          统计性质
          样本复杂度
          指数收敛
        分解算法
          Benders分解
          Dantzig-Wolfe
          增广Lagrange
      风险度量
        风险中性
        风险厌恶
          CVaR
          一致风险
          随机占优
    多阶段随机规划
      非预期性
        信息结构
        适应性决策
        因果约束
      情景树
        节点表示
        路径表示
        压缩技术
      嵌套分解
        嵌套Benders
        前向传播
        后向传播
      随机对偶DP
        价值函数逼近
        凸包络
        收敛分析
    鲁棒优化
      静态鲁棒
        最坏情况分析
        保守性分析
        精确重构
      可调鲁棒
        线性决策规则
        分离定理
        仿射可调
      分布鲁棒
        模糊集构造
          矩信息
          Wasserstein球
          似然比
        对偶重构
          凸对偶
          拉格朗日对偶
          分布对偶
      鲁棒随机规划
        混合方法
        保守性权衡
    随机逼近
      经典理论
        Robbins-Monro
          步长条件
          收敛定理
          渐近正态
        Kiefer-Wolfowitz
          差分逼近
          扰动选择
        Polyak-Ruppert
          平均迭代
          加速收敛
      现代发展
        方差缩减
          SAG/SAGA
          SVRG
          SARAH
        自适应方法
          AdaGrad
          Adam
          RMSprop
        大规模SA
          异步更新
          稀疏更新
          压缩通信
      约束处理
        投影方法
        原始对偶
        罚函数
    风险度量
      一致性风险
        单调性
        平移等变
        正齐次
        次可加性
      CVaR
        定义与性质
        变分表示
        线性化
      其他度量
        谱风险
        熵风险
        分位数
      多目标
        风险收益权衡
        Pareto前沿
        效用理论
    机器学习应用
      随机优化
        ERM问题
          样本平均
          正则化
          收敛分析
        SGD分析
          凸情形
          强凸情形
          非凸情形
      深度网络
        自适应学习率
        批量归一化
        二阶方法
      强化学习
        策略梯度
        Actor-Critic
        信任域
      贝叶斯优化
        采集函数
        GP代理
        超参优化
    应用领域
      供应链管理
        库存优化
        网络设计
        产能规划
      能源系统
        机组组合
        风电整合
        需求响应
      金融工程
        投资组合
        资产负债
        衍生品对冲
      医疗决策
        治疗优化
        临床试验
        资源分配
      交通运输
        路径规划
        时刻表优化
        共享出行
```

## 核心概念详解

### 1. 两阶段随机规划

**标准形式**：
$$\min_{x} c^T x + \mathbb{E}_\xi[Q(x, \xi)]$$

其中追索函数：
$$Q(x, \xi) = \min_y \{q(\xi)^T y : Wy = h(\xi) - T(\xi)x, \; y \geq 0\}$$

**样本平均近似（SAA）**：
$$\min_{x} c^T x + \frac{1}{N}\sum_{i=1}^N Q(x, \xi_i)$$

**收敛性**：在适当条件下，SAA解以指数速率收敛到真实解

### 2. 条件风险价值（CVaR）

**定义**：
$$\text{CVaR}_\alpha(Z) = \inf_{t} \{t + \frac{1}{1-\alpha}\mathbb{E}[(Z-t)_+]\}$$

**等价表示**：
$$\text{CVaR}_\alpha(Z) = \mathbb{E}[Z | Z \geq \text{VaR}_\alpha(Z)]$$

**优化重构**：
$$\min_{x} \text{CVaR}_\alpha(f(x,\xi)) = \min_{x,t} t + \frac{1}{(1-\alpha)N}\sum_{i=1}^N (f(x,\xi_i) - t)_+$$

### 3. 随机逼近收敛

**Robbins-Monro算法**：
$$x_{k+1} = x_k - \gamma_k \hat{g}_k$$

其中 $\hat{g}_k$ 是 $g(x_k)$ 的无偏估计

**收敛条件**：
- 步长：$\sum \gamma_k = \infty$, $\sum \gamma_k^2 < \infty$
- 增长：$\|g(x)\|^2 \leq a + b\|x\|^2$

**收敛速率**（强凸情形）：
$$\mathbb{E}[\|x_k - x^*\|^2] = O(1/k)$$

### 4. 分布鲁棒优化

**一般形式**：
$$\min_x \sup_{P \in \mathcal{P}} \mathbb{E}_P[f(x, \xi)]$$

**Wasserstein模糊集**：
$$\mathcal{P} = \{P : W_c(P, P_N) \leq \epsilon\}$$

其中 $W_c$ 是以成本 $c$ 为基础的Wasserstein距离

**对偶重构**（凸 $f$）：
$$\min_{x,\lambda,s_i} \lambda\epsilon + \frac{1}{N}\sum_{i=1}^N s_i$$
$$\text{s.t. } s_i \geq f(x,\xi_i) - \lambda c(\xi_i, \xi), \; \forall \xi$$

## 相关主题

- [动态规划](./dynamic-programming.md)
- [凸优化](./convex-optimization.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Birge & Louveaux: "Introduction to Stochastic Programming"
- Shapiro et al.: "Lectures on Stochastic Programming"
- Ben-Tal et al.: "Robust Optimization"
- Kushner & Yin: "Stochastic Approximation Algorithms"
