---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 率失真理论推导链
processed_at: '2026-04-05'
---
# 率失真理论推导链

## 概述
本推理树展示Shannon率失真理论的完整数学推导，包括失真度量、率失真函数、失真率函数、高斯信源、向量量化等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 失真度量
        A1[失真函数<br/>dx, x̂ ≥ 0] --> A2[汉明失真<br/>dx, x̂ = 1x≠x̂]
        A2 --> A3[平方误差<br/>dx, x̂ = x - x̂²]
        A3 --> A4[期望失真<br/>EdX, X̂]
    end
    
    subgraph 率失真函数
        A4 --> B1[信息率失真<br/>RX,D = min I(X;X̂)]
        B1 --> B2[约束<br/>EdX, X̂ ≤ D]
        B2 --> B3[率失真定理<br/>R > R(D) ⇔ 可达]
        B3 --> B4[R(D)性质<br/>凸、单调减]
    end
    
    subgraph 典型序列方法
        B3 --> C1[失真典型性<br/>A_{d,ε}^n]
        C1 --> C2[码本设计<br/>2^{nR}个重建码字]
        C2 --> C3[编码器<br/>找最小失真码字]
        C3 --> C4[逆定理<br/>R < R(D) ⇒ P_ed → 1]
    end
    
    subgraph 高斯信源
        B1 --> D1[高斯RDF<br/>X ~ N0,σ²]
        D1 --> D2[平方误差<br/>d = x - x̂²]
        D2 --> D3[反向水填充<br/>R(D) = ½ logσ²/D]
        D3 --> D4[Shannon下界<br/>R(D) ≥ hX - ½ log2πeD]
    end
    
    subgraph 向量量化
        D2 --> E1[Lloyd算法<br/>k-means]
        E1 --> E2[质心条件<br/>x̂ = Ex|Q(x)]

        E2 --> E3[最近邻条件<br/>Qx = argmin d(x, x̂)]
        E3 --> E4[Lloyd-Max量化<br/>最优标量量化]
    end
    
    subgraph 多描述编码
        B3 --> F1[多描述<br/>多重建版本]
        F1 --> F2[边失真<br/>单个描述失真]
        F2 --> F3[中心失真<br/>联合描述失真]
        F3 --> F4[率失真区域<br/>可达三元组]
    end
    
    style B1 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style B3 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style D3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style E4 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：失真度量

**失真函数**：$d: \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}^+$

**常用失真度量**：

| 类型 | 定义 | 适用场景 |
|------|------|----------|
| 汉明失真 | $d(x, \hat{x}) = \mathbb{1}[x \neq \hat{x}]$ | 离散信源 |
| 绝对误差 | $d(x, \hat{x}) = |x - \hat{x}|$ | 鲁棒编码 |
| 平方误差 | $d(x, \hat{x}) = (x - \hat{x})^2$ | 连续信源 |
| 加权误差 | $d(x, \hat{x}) = (x - \hat{x})^T W (x - \hat{x})$ | 向量信源 |

**序列失真**：$d(x^n, \hat{x}^n) = \frac{1}{n}\sum_{i=1}^n d(x_i, \hat{x}_i)$

### 第二步：率失真函数定义

**$(2^{nR}, n)$ 率失真码**：
- 编码器：$f_n: \mathcal{X}^n \to \{1, 2, \ldots, 2^{nR}\}$
- 译码器：$g_n: \{1, \ldots, 2^{nR}\} \to \hat{\mathcal{X}}^n$
- 重建：$\hat{X}^n = g_n(f_n(X^n))$

**期望失真**：
$$D = E[d(X^n, \hat{X}^n)]$$

**率失真函数**：
$$R(D) = \min_{p(\hat{x}|x): E[d(X, \hat{X})] \leq D} I(X; \hat{X})$$

**失真率函数**：
$$D(R) = \min_{p(\hat{x}|x): I(X; \hat{X}) \leq R} E[d(X, \hat{X})]$$

### 第三步：率失真定理

**定理（Shannon, 1959）**：

$$R(D) = \min_{p(\hat{x}|x): E[d] \leq D} I(X; \hat{X})$$

是满足以下条件的速率下界：
- 对任意 $R > R(D)$，存在码使得 $E[d] \leq D + \epsilon$
- 对任意 $R < R(D)$，不存在满足失真约束的码

**证明概要（可达性）**：

1. 生成码本：$2^{nR}$ 个码字独立 $\sim p(\hat{x})$ i.i.d.
2. 编码器：找到与信源序列失真典型的码字
3. 若 $R > I(X; \hat{X})$，则高概率找到满足失真约束的码字

**逆定理**：

$$nR \geq I(X^n; \hat{X}^n) \geq \sum_{i=1}^n I(X_i; \hat{X}_i) \geq nR(D)$$

### 第四步：高斯信源的率失真函数

**信源**：$X \sim \mathcal{N}(0, \sigma^2)$

**失真度量**：$d(x, \hat{x}) = (x - \hat{x})^2$

**率失真函数**：

$$R(D) = \begin{cases} \frac{1}{2}\log\frac{\sigma^2}{D}, & 0 \leq D \leq \sigma^2 \\ 0, & D > \sigma^2 \end{cases}$$

**逆函数（失真率函数）**：

$$D(R) = \sigma^2 2^{-2R}$$

**推导**：

设 $X = \hat{X} + Z$，其中 $Z \sim \mathcal{N}(0, D)$ 独立于 $\hat{X}$。

则：
$$I(X; \hat{X}) = h(X) - h(X|\hat{X}) = \frac{1}{2}\log(2\pi e \sigma^2) - \frac{1}{2}\log(2\pi e D)$$

$$= \frac{1}{2}\log\frac{\sigma^2}{D}$$

**反向水填充**（多变量高斯）：

对协方差矩阵特征值 $\{\lambda_i\}$：
$$R(D) = \sum_{i=1}^n \frac{1}{2}\log\frac{\lambda_i}{D_i}$$

其中 $D_i = \min(D, \lambda_i)$，按特征值大小分配失真。

### 第五步：Shannon下界

**定理**：对任意信源 $X$ 与平方误差失真：
$$R(D) \geq h(X) - \frac{1}{2}\log(2\pi e D)$$

**证明**：

$$I(X; \hat{X}) = h(X) - h(X|\hat{X}) \geq h(X) - h(X - \hat{X})$$

由最大熵定理，给定方差 $D$，高斯分布熵最大：
$$h(X - \hat{X}) \leq \frac{1}{2}\log(2\pi e D)$$

**紧性**：对高斯信源取等。

### 第六步：Lloyd-Max量化

**最优标量量化**：$K$ 个量化电平，边界 $\{b_k\}$，电平 $\{y_k\}$

**必要条件**：

1. **最近邻条件**（编码器）：
$$Q(x) = y_k, \quad \text{if } b_{k-1} < x \leq b_k$$
边界为相邻电平中点：$b_k = \frac{y_k + y_{k+1}}{2}$

2. **质心条件**（译码器）：
$$y_k = E[X | Q(X) = y_k] = \frac{\int_{b_{k-1}}^{b_k} x p(x) dx}{\int_{b_{k-1}}^{b_k} p(x) dx}$$

**Lloyd算法**：
1. 初始化电平
2. 固定电平，更新边界（最近邻）
3. 固定边界，更新电平（质心）
4. 重复直至收敛

### 第七步：多描述编码

**问题设置**：
- 两个描述（编码器输出）
- 三种重建：来自描述1、描述2、两者联合
- 边失真 $D_1, D_2$，中心失真 $D_0$

**率失真区域**：可达 $(R_1, R_2, D_0, D_1, D_2)$ 五元组

**El Gamal-Cover内界**：
$$R_1 > I(X; X_1), \quad R_2 > I(X; X_2)$$
$$R_1 + R_2 > I(X; X_0, X_1, X_2) + I(X_1; X_2)$$

---

## 率失真函数对比

| 信源 | 失真度量 | $R(D)$ | 达到条件 |
|------|----------|--------|----------|
| Bernoulli(p) | 汉明 | $H(p) - H(D)$ | $D \leq \min(p, 1-p)$ |
| 高斯$\mathcal{N}(0,\sigma^2)$ | 平方 | $\frac{1}{2}\log\frac{\sigma^2}{D}$ | $D \leq \sigma^2$ |
| 拉普拉斯 | 绝对 | $-\log(\alpha D)$ | 指数分布 |
| 均匀$[0,a]$ | 平方 | $\frac{1}{2}\log\frac{a^2}{12D}$ | 高分辨率近似 |

---

## 依赖关系图

```

信息论基础 ← 熵与互信息
    ↓
失真度量 ← 应用领域
    ↓
率失真函数定义 ← 优化理论
    ↓
率失真定理 ← 典型序列方法
    ↓
高斯信源分析 ← 最大熵原理
    ↓
向量量化 ← 迭代算法
    ↓
多描述编码 ← 网络信息论

```

---

## 关键公式汇总

| 名称 | 公式 | 意义 |
|------|------|------|
| 率失真函数 | $R(D) = \min I(X;\hat{X})$ | 最小可达速率 |
| 高斯R(D) | $\frac{1}{2}\log\frac{\sigma^2}{D}$ | 平方误差最优 |
| Shannon下界 | $h(X) - \frac{1}{2}\log(2\pi e D)$ | 通用下界 |
| Lloyd条件 | 质心+最近邻 | 最优量化必要条件 |

---

## 参考

- Shannon, C. E. (1959). "Coding Theorems for a Discrete Source with a Fidelity Criterion"
- Berger, T. (1971). *Rate Distortion Theory: A Mathematical Basis for Data Compression*
- Cover, T. M. & Thomas, J. A. (2006). *Elements of Information Theory* (Chapter 13)
- Gersho, A. & Gray, R. M. (1992). *Vector Quantization and Signal Compression*
- El Gamal, A. & Kim, Y. H. (2011). *Network Information Theory*

---

*生成时间：2026年4月*
