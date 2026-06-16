---
msc_primary: '00

  - 00A99'
title: 常微分方程数值解 思维导图
processed_at: '2026-04-05'
references:
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
external_ids:
  wikipedia_url: https://en.wikipedia.org/wiki/Differential_equation
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E5%BE%AE%E5%88%86%E6%96%B9%E7%A8%8B
  nlab_url: https://ncatlab.org/nlab/show/differential+equation
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 常微分方程数值解 思维导图

## 一、基本概念

### 1.1 问题分类
- **初值问题 (IVP)**
  - y' = f(t,y), y(t₀) = y₀
- **边值问题 (BVP)**
  - 边界条件
  - 两点边值

### 1.2 数值解基础
- **离散化**
  - 步长 h
  - 网格点 tₙ
- **局部截断误差**
- **整体误差**
- **收敛性与稳定性**

## 二、单步法

### 2.1 Euler方法
- **显式Euler**
  - yₙ₊₁ = yₙ + hf(tₙ,yₙ)
  - 一阶精度
- **隐式Euler**
  - yₙ₊₁ = yₙ + hf(tₙ₊₁,yₙ₊₁)
  - 绝对稳定
- **梯形公式**
  - yₙ₊₁ = yₙ + h/2[f(tₙ,yₙ)+f(tₙ₊₁,yₙ₊₁)]
  - 二阶精度
- **改进Euler**
  - Heun方法
  - 预测-校正

### 2.2 Runge-Kutta方法
- **二阶RK**
  - 中点方法
  - Heun方法
  - Ralston方法
- **经典四阶RK**
  - RK4
  - 四阶精度
- **高阶RK**
  - Butcher表
  - 阶条件

### 2.3 自适应步长
- **Richardson外推**
- **嵌入RK方法**
  - Runge-Kutta-Fehlberg (RKF)
  - Dormand-Prince (DP)
- **误差控制**
  - 局部误差估计
  - 步长调整

## 三、多步法

### 3.1 Adams方法
- **Adams-Bashforth (显式)**
  - 二步: AB2
  - 四步: AB4
- **Adams-Moulton (隐式)**
  - 一步: 梯形
  - 三步: AM3
- **预测-校正**
  - PECE模式
  - PECLE模式

### 3.2 向后微分公式 (BDF)
- **BDF1**
  - 隐式Euler
- **BDF2-BDF6**
  - 刚性问题
  - 稳定性优势

### 3.3 多步法的启动
- **Runge-Kutta启动**
- **Taylor展开**

## 四、刚性问题

### 4.1 刚性定义
- **刚性比**
  - max|Re(λ)| / min|Re(λ)|

- **特征**
  - 步长受限
  - 稳定性需求

### 4.2 刚性求解器
- **隐式RK**
  - Gauss-Legendre
  - Radau IIA
- **BDF方法**
- **隐式多步法**

### 4.3 稳定性概念
- **A-稳定性**
- **L-稳定性**
- **刚性衰减**

## 五、边值问题

### 5.1 打靶法
- **初值问题迭代**
- **Newton迭代**
- **多点打靶**

### 5.2 有限差分法
- **中心差分**
- **边界处理**
- **非线性系统**

### 5.3 配置法
- **多项式配置**
- **样条配置**

### 5.4 有限元方法
- **Galerkin方法**
- **弱形式**

## 六、稳定性分析

### 6.1 绝对稳定性
- **稳定性区域**
- **试验方程**
  - y' = λy

### 6.2 线性稳定性
- **特征值分析**
- **谱半径**

### 6.3 非线性稳定性
- **收缩性**
- **B-稳定性**
- **代数稳定性**

## 七、微分代数方程 (DAE)

### 7.1 DAE分类
- **指标1**
- **高阶指标**

### 7.2 求解方法
- **指标约化**
- **直接离散化**
- **BDF方法**

## 八、特殊方法

### 8.1 辛方法
- **Hamilton系统**
- **辛Euler**
- **Stormer-Verlet**

### 8.2 守恒律方法
- **能量守恒**
- **对称方法**

### 8.3 延迟微分方程
- **方法扩展**
- **历史依赖**

---

## 关联概念
- [偏微分方程数值解](./num-07-偏微分方程数值解.md)
- [线性方程组求解](./num-03-线性方程组求解.md)

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845