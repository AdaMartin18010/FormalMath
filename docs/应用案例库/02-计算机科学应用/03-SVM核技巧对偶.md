---
msc_primary: "12Fxx"
msc_secondary: ['12Exx', '13Cxx', '62Fxx']
---

# 支持向量机的核技巧与对偶问题

## 应用领域

**学科**: 机器学习 / 统计学习理论
**具体应用**: 文本分类、图像识别、生物信息学、手写数字识别
**MSC分类**: 68T05 (Learning), 90C25 (Convex programming), 46E22 (Hilbert spaces)

---

## 数学概念

### 核心数学工具

1. **凸优化**: 拉格朗日对偶、KKT条件
2. **核方法**: 再生核希尔伯特空间(RKHS)
3. **Mercer定理**: 核函数的正定条件
4. **泛函分析**: 特征空间映射

### 关键定义

- **核函数**: $K(x, x') = \langle \phi(x), \phi(x') \rangle$
- **间隔(margin)**: 超平面到最近样本的距离

---

## 问题描述

### 线性分类问题

给定训练数据 $\{(x_i, y_i)\}_{i=1}^n$，其中 $y_i \in \{-1, +1\}$，寻找分类超平面 $w^T x + b = 0$。

**最大间隔原则**: 选择使训练数据间隔最大的超平面。

### 核心问题

1. 如何处理线性不可分数据？
2. 特征空间映射的计算复杂度问题？
3. 对偶问题的优势是什么？

---

## 数学模型

### 原始优化问题（软间隔SVM）

**目标**: 最大化间隔同时最小化分类错误

$$\min_{w, b, \xi} \frac{1}{2}\|w\|^2 + C\sum_{i=1}^n \xi_i$$

**约束**:

$$y_i(w^T x_i + b) \geq 1 - \xi_i, \quad i = 1, ..., n$$
$$\xi_i \geq 0, \quad i = 1, ..., n$$

其中:

- $\|w\|$ 的倒数与间隔成正比

- $\xi_i$ 是松弛变量
- $C$ 控制间隔与错误的权衡

### 拉格朗日对偶

**拉格朗日函数**:

$$\mathcal{L}(w, b, \xi, \alpha, \mu) = \frac{1}{2}\|w\|^2 + C\sum_{i=1}^n \xi_i - \sum_{i=1}^n \alpha_i[y_i(w^T x_i + b) - 1 + \xi_i] - \sum_{i=1}^n \mu_i \xi_i$$

其中 $\alpha_i \geq 0, \mu_i \geq 0$ 是拉格朗日乘子。

**KKT条件**:

$$\frac{\partial \mathcal{L}}{\partial w} = w - \sum_{i=1}^n \alpha_i y_i x_i = 0 \Rightarrow w = \sum_{i=1}^n \alpha_i y_i x_i$$

$$\frac{\partial \mathcal{L}}{\partial b} = -\sum_{i=1}^n \alpha_i y_i = 0$$

$$\frac{\partial \mathcal{L}}{\partial \xi_i} = C - \alpha_i - \mu_i = 0$$

### 对偶问题

代入KKT条件，得到对偶问题：

$$\boxed{\max_\alpha \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i,j=1}^n \alpha_i \alpha_j y_i y_j x_i^T x_j}$$

**约束**:

$$\sum_{i=1}^n \alpha_i y_i = 0$$
$$0 \leq \alpha_i \leq C, \quad i = 1, ..., n$$

### 核技巧

**特征映射**: $\phi: \mathcal{X} \to \mathcal{H}$

**核函数**: $K(x, x') = \langle \phi(x), \phi(x') \rangle_\mathcal{H}$

**核化对偶问题**:

$$\max_\alpha \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i,j=1}^n \alpha_i \alpha_j y_i y_j K(x_i, x_j)$$

**常用核函数**:

| 核函数 | 形式 | 参数 |
|--------|------|------|
| **线性** | $K(x, x') = x^T x'$ | 无 |
| **多项式** | $K(x, x') = (x^T x' + c)^d$ | $c \geq 0, d \in \mathbb{N}$ |
| **RBF/高斯** | $K(x, x') = \exp(-\frac{\|x-x'\|^2}{2\sigma^2})$ | $\sigma > 0$ |
| **Sigmoid** | $K(x, x') = \tanh(\kappa x^T x' + \theta)$ | $\kappa, \theta$ |

---

## 求解过程

### 步骤1：Mercer定理验证

**定理**: 对称函数 $K$ 是有效核函数当且仅当对任意 $n$ 和样本 $\{x_i\}_{i=1}^n$，Gram矩阵 $G_{ij} = K(x_i, x_j)$ 是半正定的。

**RBF核验证**:

$$G = (e^{-\|x_i - x_j\|^2/2\sigma^2})_{i,j}$$

由Bochner定理，高斯函数的傅里叶变换为正，故 $G \succeq 0$。

### 步骤2：SMO算法（序列最小优化）

**核心思想**: 每次优化两个拉格朗日乘子，固定其他。

**子问题**: 选择 $\alpha_i, \alpha_j$，求解二次规划：

$$\min_{\alpha_i, \alpha_j} W(\alpha_i, \alpha_j)$$

**约束**:

$$y_i \alpha_i + y_j \alpha_j = \text{const}$$
$$0 \leq \alpha_i, \alpha_j \leq C$$

**解析解**: 闭式更新公式，无需数值优化器。

### 步骤3：决策函数

**权重向量**:

$$w = \sum_{i=1}^n \alpha_i y_i \phi(x_i)$$

**决策函数**:

$$f(x) = \text{sign}\left(\sum_{i=1}^n \alpha_i y_i K(x_i, x) + b\right)$$

**支持向量**: 满足 $\alpha_i > 0$ 的样本。

**偏置项计算**:

对任意支持向量 $x_j$ 满足 $0 < \alpha_j < C$:

$$b = y_j - \sum_{i=1}^n \alpha_i y_i K(x_i, x_j)$$

---

## 结果分析

### 核方法的优势

1. **隐式高维映射**: 无需显式计算 $\phi(x)$，直接通过内积工作
2. **计算效率**: 复杂度取决于支持向量数，而非特征维数
3. **灵活性**: 通过选择不同核函数实现不同决策边界

### 核选择指南

| 数据特点 | 推荐核 | 理由 |
|----------|--------|------|
| 高维稀疏 | 线性 | 已足够，避免过拟合 |
| 中等维数 | RBF | 通用，非线性能力强 |
| 图像/信号 | RBF, 自定义 | 捕捉局部特征 |
| 文本/序列 | 线性、字符串核 | 高维稀疏特性 |

### VC维与泛化界

**RBF SVM的VC维**: 理论上无限，但通过间隔最大化控制复杂度。

**泛化误差界**:

$$R[f] \leq R_{emp}[f] + O\left(\sqrt{\frac{d_{VC}}{n}}\right)$$

**结构风险最小化**: SVM通过最大化间隔最小化泛化误差上界。

### 计算复杂度

| 阶段 | 复杂度 | 说明 |
|------|--------|------|
| **训练** | $O(n^2)$ - $O(n^3)$ | 依赖求解算法 |
| **预测** | $O(s)$ | $s$ = 支持向量数 |
| **核矩阵计算** | $O(n^2 d)$ | 可并行 |

---

## 参考资源

### 原始论文

- **Cortes, C. & Vapnik, V.** (1995). "Support-vector networks". *Machine Learning*.
- **Boser, B.E., Guyon, I.M., & Vapnik, V.N.** (1992). "A training algorithm for optimal margin classifiers". *COLT*.

### 推荐教材

- **Schölkopf, B. & Smola, A.J.** *Learning with Kernels* (2002).
- **Cristianini, N. & Shawe-Taylor, J.** *An Introduction to Support Vector Machines*.
- **Bishop, C.M.** *Pattern Recognition and Machine Learning* — 第7章

---

**创建日期**: 2026年4月2日
**最后更新**: 2026年4月2日
