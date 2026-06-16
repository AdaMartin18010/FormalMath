---
msc_primary: '00

  - 00A99'
title: 数值积分 思维导图
processed_at: '2026-04-05'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/integral
  wikipedia_url: https://en.wikipedia.org/wiki/Integral
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E7%A7%AF%E5%88%86
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q80091
    consulted_at: '2026-06-16'
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
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 数值积分 思维导图

## 一、Newton-Cotes公式

### 1.1 闭型公式
- **梯形公式**
  - 代数精度: 1次
  - 误差项: -h³/12 f''(ξ)
- **Simpson公式**
  - 代数精度: 3次
  - 误差项: -h⁵/90 f⁽⁴⁾(ξ)
- **Cotes公式**
  - Newton-Cotes系数
  - 高阶公式的不稳定性

### 1.2 开型公式
- **中点公式**
  - 代数精度: 1次
- **高阶开型公式**

### 1.3 复合公式
- **复合梯形公式**
  - 收敛阶: O(h²)
  - 递推计算
- **复合Simpson公式**
  - 收敛阶: O(h⁴)
- **Romberg积分**
  - Richardson外推
  - 加速收敛

## 二、高斯求积公式

### 2.1 Gauss-Legendre求积
- **节点与权值**
  - Legendre多项式零点
  - 权值计算
- **代数精度**
  - n点公式: 2n-1次
- **区间变换**
  - [a,b]到[-1,1]

### 2.2 其他Gauss型求积
- **Gauss-Chebyshev**
  - 权函数: (1-x²)^{-1/2}
- **Gauss-Hermite**
  - 区间: (-∞,∞)
  - 权函数: e^{-x²}
- **Gauss-Laguerre**
  - 区间: [0,∞)
  - 权函数: e^{-x}

### 2.3 高斯求积性质
- **正交多项式零点**
- **权值正性**
- **收敛性**

## 三、自适应积分

### 3.1 自适应Simpson
- **误差估计**
  - 子区间比较
- **递归细分**
  - 终止条件
- **效率优化**

### 3.2 自适应高斯求积
- **局部误差控制**
- **全局精度保证**

## 四、奇异积分与特殊技巧

### 4.1 奇异积分处理
- **变量替换**
- **区间分割**
- **Gauss型求积**

### 4.2 无穷积分
- **变量替换**
- **截断与估计**
- **Gauss-Hermite/Laguerre**

### 4.3 振荡积分
- **Filon方法**
- **积分平均**

## 五、多重积分

### 5.1 重积分方法
- **累次积分**
  - 降维策略
- **复合公式推广**
  - 复合Simpson
  - 复合Gauss

### 5.2 Monte Carlo方法
- **随机采样**
- **收敛速度**
  - O(1/√N)
- **方差缩减**
  - 重要性采样
  - 分层采样

### 5.3 高维积分
- **维数灾难**
- **拟Monte Carlo**
  - 低差异序列
- **稀疏网格**

## 六、数值微分

### 6.1 差商公式
- **向前差分**
  - f'(x) ≈ [f(x+h)-f(x)]/h
- **向后差分**
  - f'(x) ≈ [f(x)-f(x-h)]/h
- **中心差分**
  - f'(x) ≈ [f(x+h)-f(x-h)]/(2h)
  - O(h²)精度

### 6.2 高阶导数
- **二阶中心差分**
- **高阶差分公式**

### 6.3 Richardson外推
- **精度提升**
- **误差估计**

---

## 关联概念
- [插值与逼近](./num-01-插值与逼近.md)
- [线性方程组求解](./num-03-线性方程组求解.md)

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845