---
msc_primary: "12Fxx"
msc_secondary: ['12Exx', '22E47', '13Cxx']
---

# 主成分分析(PCA)的谱分解原理

## 应用领域

**学科**: 机器学习 / 数据降维 / 统计学
**具体应用**: 人脸识别、图像压缩、基因表达分析、金融风险管理
**MSC分类**: 62H25 (Factor analysis), 15A18 (Eigenvalues), 68T10 (Pattern recognition)

---

## 数学概念

### 核心数学工具

1. **协方差矩阵**: 描述数据各维度间的线性关系
2. **特征值分解**: 对称矩阵的谱分解
3. **奇异值分解(SVD)**: 更一般的矩阵分解
4. **瑞利商**: 特征值的变分刻画

### 关键定义

- **数据中心化**: $\tilde{x}_i = x_i - \bar{x}$
- **样本协方差**: $S = \frac{1}{n-1}\sum_{i=1}^n \tilde{x}_i \tilde{x}_i^T = \frac{1}{n-1}X^TX$

---

## 问题描述

### 降维问题

给定高维数据 $\{x_1, ..., x_n\} \subset \mathbb{R}^d$，寻找低维表示 $\{y_1, ..., y_n\} \subset \mathbb{R}^k$ ($k < d$) 保留最大方差。

### 核心问题

1. 如何定义"最优"投影方向？
2. 投影后的方差如何最大化？
3. 如何选择保留的主成分个数？

---

## 数学模型

### 方差最大化视角

**寻找第一主成分**: 单位向量 $w_1$ 使投影方差最大

$$\max_{w_1} \frac{1}{n}\sum_{i=1}^n (w_1^T \tilde{x}_i)^2 = \max_{w_1} w_1^T S w_1$$

**约束**: $\|w_1\|_2 = 1$

**解**: $w_1$ 是 $S$ 的最大特征值对应的特征向量。

### 谱分解形式

协方差矩阵的对角化：

$$S = W \Lambda W^T = \sum_{j=1}^d \lambda_j w_j w_j^T$$

其中:

- $\lambda_1 \geq \lambda_2 \geq ... \geq \lambda_d \geq 0$: 特征值
- $w_j$: 对应的正交特征向量

### 投影矩阵

**前k个主成分构成的投影矩阵**:

$$W_k = [w_1, w_2, ..., w_k] \in \mathbb{R}^{d \times k}$$

**降维映射**:

$$y_i = W_k^T \tilde{x}_i \in \mathbb{R}^k$$

**重构**:

$$\hat{x}_i = W_k y_i + \bar{x} = W_k W_k^T \tilde{x}_i + \bar{x}$$

---

## 求解过程

### 步骤1：数据预处理

**中心化**:

$$\bar{x} = \frac{1}{n}\sum_{i=1}^n x_i$$
$$\tilde{X} = X - \mathbf{1}\bar{x}^T$$

**标准化（可选）**: 当各维度量纲不同时

$$\tilde{x}_{ij} = \frac{x_{ij} - \bar{x}_j}{\sigma_j}$$

### 步骤2：计算协方差矩阵

$$S = \frac{1}{n-1}\tilde{X}^T\tilde{X} \in \mathbb{R}^{d \times d}$$

### 步骤3：特征值分解

求解特征值问题：

$$S w_j = \lambda_j w_j, \quad j = 1, ..., d$$

**排序**: $\lambda_1 \geq \lambda_2 \geq ... \geq \lambda_d$

### 步骤4：选择主成分数k

**方差保留率**:

$$\text{保留方差比例} = \frac{\sum_{j=1}^k \lambda_j}{\sum_{j=1}^d \lambda_j}$$

**常用准则**:

- 累计方差达到85-95%
- Kaiser准则: 保留 $\lambda_j > 1$（标准化后）
- 肘部法则（scree plot）

### 步骤5：降维与重构

**降维**:

$$Y = \tilde{X}W_k \in \mathbb{R}^{n \times k}$$

**重构误差**:

$$\text{MSE} = \frac{1}{n}\sum_{i=1}^n \|\tilde{x}_i - W_k W_k^T \tilde{x}_i\|^2 = \sum_{j=k+1}^d \lambda_j$$

---

## 结果分析

### 几何解释

**主成分** $w_j$ 构成数据方差最大的正交方向：

- $w_1$: 数据散布最大的方向
- $w_2$: 与$w_1$正交的数据散布最大方向
- 以此类推...

**特征值的意义**: $\lambda_j$ 是数据在第 $j$ 主成分方向上的方差。

### 与SVD的关系

对数据矩阵 $\tilde{X}$ 进行SVD：

$$\tilde{X} = U \Sigma V^T$$

其中:

- $V$ 的列是 $S = \frac{1}{n-1}\tilde{X}^T\tilde{X}$ 的特征向量（主成分）
- $\Sigma^2/(n-1)$ 的对角元是特征值

**数值稳定性**: 对大型数据，使用随机SVD或迭代方法更高效。

### 应用案例

| 应用 | 数据维度 | 降维后 | 效果 |
|------|----------|--------|------|
| **人脸识别** | 64×64=4096 | 50-150 | Eigenfaces |
| **基因表达** | ~20000 | 2-50 | 样本聚类 |
| **图像压缩** | 512×512 | 50 | 有损压缩 |
| **金融风控** | 100+指标 | 10-20 | 风险因子提取 |

### 局限性

1. **线性方法**: 无法捕捉非线性结构
2. **对异常值敏感**: 协方差矩阵受极端值影响
3. **解释性**: 主成分可能是原始特征的混合，难以解释

**非线性扩展**: 核PCA (Kernel PCA)、流形学习（Isomap, t-SNE, UMAP）

---

## 参考资源

### 经典文献

- **Pearson, K.** (1901). "On lines and planes of closest fit to systems of points in space". *Philosophical Magazine*.
- **Hotelling, H.** (1933). "Analysis of a complex of statistical variables into principal components". *J. Educ. Psychol.*.

### 推荐教材

- **Jolliffe, I.T.** *Principal Component Analysis* (2002).
- **Bishop, C.M.** *Pattern Recognition and Machine Learning* — 第12章

---

**创建日期**: 2026年4月2日
**最后更新**: 2026年4月2日
