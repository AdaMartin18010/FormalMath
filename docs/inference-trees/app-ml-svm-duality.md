---
msc_primary: 00

  - 00A99
title: SVM对偶理论推导链
processed_at: '2026-04-05'
---
# SVM对偶理论推导链

## 概述
本推理树展示支持向量机（SVM）的优化对偶理论，包括最大间隔分类、拉格朗日对偶、KKT条件、核技巧等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 原始问题
        A1[线性可分<br/>yᵢw·xᵢ + b ≥ 1] --> A2[最大间隔<br/>max 2/\|w\|]
        A2 --> A3[凸优化<br/>min ½\|w\|²]

        A3 --> A4[约束条件<br/>yᵢw·xᵢ + b ≥ 1]
    end
    
    subgraph 拉格朗日函数
        A4 --> B1[拉格朗日乘子<br/>αᵢ ≥ 0]
        B1 --> B2[Lagrangian<br/>L = ½\|w\|² - Σαᵢgᵢ]

        B2 --> B3[对偶函数<br/>gα = inf_w L]
    end
    
    subgraph 对偶问题
        B3 --> C1[w的极值<br/>∇_w L = 0]
        C1 --> C2[w = Σαᵢyᵢxᵢ]
        C2 --> C3[对偶目标<br/>max Σαᵢ - ½ΣΣαᵢαⱼyᵢyⱼxᵢ·xⱼ]
        C3 --> C4[约束<br/>Σαᵢyᵢ = 0, αᵢ ≥ 0]
    end
    
    subgraph KKT条件
        C2 --> D1[原始可行<br/>yᵢw·xᵢ + b ≥ 1]
        D1 --> D2[对偶可行<br/>αᵢ ≥ 0]
        D2 --> D3[互补松弛<br/>αᵢ1-yᵢw·xᵢ+b = 0]
        D3 --> D4[支持向量<br/>αᵢ > 0的点]
    end
    
    subgraph 核技巧
        C3 --> E1[内积替换<br/>xᵢ·xⱼ → Kxᵢ,xⱼ]
        E1 --> E2[核函数<br/>Mercer条件]
        E2 --> E3[常见核<br/>RBF, 多项式, Sigmoid]
        E3 --> E4[隐式特征空间<br/>Kx,y = φx·φy]
    end
    
    subgraph 软间隔
        A4 --> F1[松弛变量<br/>ξᵢ ≥ 0]
        F1 --> F2[正则化<br/>min ½\|w\|² + CΣξᵢ]

        F2 --> F3[软间隔对偶<br/>0 ≤ αᵢ ≤ C]
        F3 --> D3
    end
    
    style C3 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px
    style D4 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style E4 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style F3 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：最大间隔分类器

**线性可分假设**：给定训练集 $\{(x_i, y_i)\}_{i=1}^n$，$y_i \in \{-1, +1\}$

**分类超平面**：$w^T x + b = 0$

**间隔定义**：
$$\text{margin} = \min_i \frac{y_i(w^T x_i + b)}{\|w\|} = \frac{1}{\|w\|}$$

（在标准化约束 $\min_i y_i(w^T x_i + b) = 1$ 下）

**原始优化问题**：
$$\min_{w,b} \frac{1}{2}\|w\|^2$$

约束：
$$y_i(w^T x_i + b) \geq 1, \quad i = 1, \ldots, n$$

**几何意义**：最小化 $\|w\|$ 等价于最大化间隔。

### 第二步：拉格朗日对偶

**拉格朗日函数**：
$$L(w, b, \alpha) = \frac{1}{2}\|w\|^2 - \sum_{i=1}^n \alpha_i [y_i(w^T x_i + b) - 1]$$

其中 $\alpha_i \geq 0$ 为拉格朗日乘子。

**对偶函数**：
$$g(\alpha) = \inf_{w,b} L(w, b, \alpha)$$

**求极值条件**：
1. $\frac{\partial L}{\partial w} = w - \sum_{i=1}^n \alpha_i y_i x_i = 0 \Rightarrow w = \sum_{i=1}^n \alpha_i y_i x_i$
2. $\frac{\partial L}{\partial b} = -\sum_{i=1}^n \alpha_i y_i = 0 \Rightarrow \sum_{i=1}^n \alpha_i y_i = 0$

### 第三步：对偶问题

将对偶条件代入拉格朗日函数：

$$g(\alpha) = \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i=1}^n\sum_{j=1}^n \alpha_i \alpha_j y_i y_j (x_i^T x_j)$$

**对偶优化问题**：
$$\max_{\alpha} \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i,j} \alpha_i \alpha_j y_i y_j K_{ij}$$

约束：
- $\sum_{i=1}^n \alpha_i y_i = 0$
- $\alpha_i \geq 0$

其中 $K_{ij} = x_i^T x_j$ 为Gram矩阵。

### 第四步：KKT条件

**强对偶性**：SVM为凸优化问题，满足Slater条件，原始问题与对偶问题等价。

**KKT条件**：
1. **原始可行**：$y_i(w^T x_i + b) \geq 1$
2. **对偶可行**：$\alpha_i \geq 0$
3. **互补松弛**：$\alpha_i [y_i(w^T x_i + b) - 1] = 0$

**支持向量**：满足 $\alpha_i > 0$ 的样本点

由互补松弛：$\alpha_i > 0 \Rightarrow y_i(w^T x_i + b) = 1$

**决策函数**：
$$f(x) = \text{sign}\left(\sum_{i: \alpha_i > 0} \alpha_i y_i x_i^T x + b\right)$$

**偏置计算**：
$$b = y_j - \sum_{i} \alpha_i y_i x_i^T x_j$$
其中 $j$ 为任意支持向量（$0 < \alpha_j < C$）

### 第五步：核技巧

**特征映射**：$\phi: \mathcal{X} \to \mathcal{H}$，将输入映射到高维特征空间

**核函数定义**：$K(x, y) = \langle \phi(x), \phi(y) \rangle_{\mathcal{H}}$

**Mercer条件**：对称函数 $K$ 是有效核当且仅当对任意有限点集，Gram矩阵半正定。

**常用核函数**：

| 核类型 | 表达式 | 参数 |
|--------|--------|------|
| 线性核 | $K(x, y) = x^T y$ | - |
| 多项式核 | $K(x, y) = (\gamma x^T y + r)^d$ | $d, \gamma, r$ |
| RBF/高斯核 | $K(x, y) = \exp(-\gamma\|x-y\|^2)$ | $\gamma$ |
| Sigmoid核 | $K(x, y) = \tanh(\gamma x^T y + r)$ | $\gamma, r$ |

**核SVM对偶**：
$$\max_{\alpha} \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i,j} \alpha_i \alpha_j y_i y_j K(x_i, x_j)$$

**决策函数**：
$$f(x) = \text{sign}\left(\sum_{i: \alpha_i > 0} \alpha_i y_i K(x_i, x) + b\right)$$

### 第六步：软间隔SVM

**松弛变量**：$\xi_i \geq 0$ 允许部分样本违反间隔约束

**原始问题**：
$$\min_{w,b,\xi} \frac{1}{2}\|w\|^2 + C\sum_{i=1}^n \xi_i$$

约束：
- $y_i(w^T x_i + b) \geq 1 - \xi_i$
- $\xi_i \geq 0$

**对偶问题**：
$$\max_{\alpha} \sum_{i=1}^n \alpha_i - \frac{1}{2}\sum_{i,j} \alpha_i \alpha_j y_i y_j K_{ij}$$

约束：
- $\sum_{i=1}^n \alpha_i y_i = 0$
- $0 \leq \alpha_i \leq C$

**样本分类**：
- $\alpha_i = 0$：非支持向量（分类正确）
- $0 < \alpha_i < C$：边界支持向量
- $\alpha_i = C$：违反间隔（误分类或边界内）

---

## SVM优化求解

**SMO算法（Sequential Minimal Optimization）**：
1. 每次优化两个乘子 $\alpha_i, \alpha_j$
2. 解析求解二维子问题
3. 更新阈值 $b$
4. 检查KKT条件收敛

---

## 依赖关系图

```

线性分类基础
    ↓
最大间隔原理
    ↓
凸优化原始问题
    ↓
拉格朗日对偶 ← 优化理论
    ↓
KKT条件 ← 变分分析
    ↓
支持向量概念
    ↓
核技巧 ← RKHS理论
    ↓
非线性分类 + 软间隔

```

---

## 关键公式汇总

| 名称 | 公式 | 作用 |
|------|------|------|
| 原始目标 | $\min \frac{1}{2}\|w\|^2$ | 最大间隔 |
| 对偶目标 | $\max \sum\alpha_i - \frac{1}{2}\sum\alpha_i\alpha_j y_i y_j K_{ij}$ | 可解优化 |
| 权重 | $w = \sum\alpha_i y_i x_i$ | 支持向量组合 |
| 决策 | $f(x) = \text{sign}(\sum\alpha_i y_i K(x_i, x) + b)$ | 分类预测 |

---

## 参考

- Vapnik, V. (1995). *The Nature of Statistical Learning Theory*
- Cortes, C. & Vapnik, V. (1995). "Support-Vector Networks"
- Schölkopf, B. & Smola, A. J. (2002). *Learning with Kernels*
- Boyd, S. & Vandenberghe, L. (2004). *Convex Optimization* (对偶理论)
- Platt, J. (1998). "Sequential Minimal Optimization"

---

*生成时间：2026年4月*
