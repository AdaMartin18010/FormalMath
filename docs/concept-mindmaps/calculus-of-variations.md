---
msc_primary: 00

  - 00A99
title: 变分法思维导图
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 变分法思维导图

## 概述

变分法是研究泛函极值的数学分支，起源于最速降线问题等经典问题。它为最优控制理论、理论物理和工程优化提供了数学基础，是连接微积分与无穷维优化的桥梁。

```mermaid
mindmap
  root((变分法<br/>Calculus of Variations))
    基础理论
      泛函定义
        映射空间
        范数与距离
        连续性
      变分概念
        一阶变分
        二阶变分
        Gateaux微分
        Frechet微分
      极值定义
        强极值
        弱极值
        全局极值
      Euler方程
        推导过程
        必要条件
        自然边界
    经典问题
      最速降线
        问题描述
        摆线解
        历史意义
      测地线问题
        曲面测地线
        欧拉-拉格朗日
        测地曲率
      等周问题
        约束变分
        Lagrange乘子
        Dido问题
      最小曲面
        Plateau问题
        平均曲率
        Weierstrass表示
      悬链线
        链条形状
        平衡条件
        变分解
    Euler-Lagrange方程
      基本形式
        单变量情形
        多变量情形
        高阶导数
      推广形式
        参数形式
        隐函数形式
        非标准问题
      首次积分
        守恒律
        能量积分
        对称性与Noether
      存在性理论
        Tonelli定理
        下半连续性
        紧性论证
    充分条件
      Legendre条件
        凸性要求
        正则点
        共轭点
      Jacobi条件
        共轭点理论
        二阶变分
        极值场
      Weierstrass条件
         excess函数
        强极值充分性
      场论方法
        极值曲线场
        中心场
        横截性条件
    约束问题
      等式约束
        微分约束
        代数约束
        乘子规则
      不等式约束
        单边变分
        障碍问题
        自由边界
      积分约束
        等周约束
        积分方程
        广义乘子
      端点约束
        固定端点
        可变端点
        横截条件
    多变量变分
      多重积分
        偏微分Euler方程
        散度形式
        椭圆性条件
      极小曲面方程
        非线性PDE
        正则性理论
        Bernstein定理
      几何测度论
        面积泛函
        BV函数
        有限周长集
    现代发展
      Gamma收敛
        序列收敛
        紧性恢复
        应用实例
      松弛理论
        凸包络
        拟凸性
        梯度Young测度
      非凸变分
        微观结构
        多井问题
        数值逼近
      变分不等式
        障碍问题
        双边约束
        拟变分
    物理应用
      经典力学
        Hamilton原理
        Lagrange方程
        相空间
      相对论
        测地线假设
        能量动量张量
        变分原理
      场论
        作用量原理
        Noether定理
        规范对称性
      连续介质力学
        弹性变分
        塑性理论
        断裂力学

```

## 核心概念详解

### 1. Euler-Lagrange方程

**标准形式**：
对于泛函 $J[y] = \int_a^b F(x, y, y') dx$

$$\frac{\partial F}{\partial y} - \frac{d}{dx}\frac{\partial F}{\partial y'} = 0$$

**高阶推广**：
$$\sum_{k=0}^n (-1)^k \frac{d^k}{dx^k}\frac{\partial F}{\partial y^{(k)}} = 0$$

**多变量情形**：
$$\frac{\partial F}{\partial u} - \sum_{i=1}^n \frac{\partial}{\partial x_i}\frac{\partial F}{\partial u_{x_i}} = 0$$

### 2. 充分条件体系

| 条件 | 形式 | 含义 |
|------|------|------|
| Legendre | $F_{y'y'} > 0$ | 局部凸性 |
| Jacobi | 无共轭点 | 二阶变分正定 |
| Weierstrass | $E \geq 0$ | 全局极值 |

**Jacobi方程**：
$$-\frac{d}{dx}(Pu') + Qu = 0$$
其中 $P = F_{y'y'}$, $Q = F_{yy} - \frac{d}{dx}F_{yy'}$

### 3. Noether定理

若 Lagrangian 在单参数变换群下不变：
$$F(x, y, y') = F(x^*, y^*, y'^*)$$

则存在守恒量：
$$\sum_i p_i \xi_i - \eta F = \text{const}$$

其中 $p_i = \partial F / \partial \dot{q}_i$ 为广义动量

### 4. 直接法（Tonelli方法）

**步骤**：
1. 证明极小化序列存在
2. 证明序列相对紧
3. 证明下半连续
4. 得到极限为解

**关键条件**：
- 强制性：$F(x,y,z) \geq c|z|^p - C$

- 凸性：$F$ 对 $z$ 凸

## 相关主题

- [最优控制](./optimal-control.md)
- [变分法与PDE](./calculus-of-variations.md)
- [应用数学思维导图索引](./00-应用数学思维导图索引.md)

## 参考资源

- Gelfand & Fomin: "Calculus of Variations"
- Dacorogna: "Introduction to the Calculus of Variations"
- Giaquinta & Hildebrandt: "Calculus of Variations"
- Struwe: "Variational Methods"
