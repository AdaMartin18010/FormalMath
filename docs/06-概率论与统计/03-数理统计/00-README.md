---
title: "数理统计 (Mathematical Statistics)"
msc_primary: "62A01"
msc_secondary: ['62F03', '62F10', '62J05', '62G08']
processed_at: '2026-04-05'
---

# 数理统计 (Mathematical Statistics)

**最后更新**: 2026年4月5日  
**MSC分类**: 62-XX (统计学), 涵盖估计、检验、回归等核心主题

---

## 1. 引言

数理统计是应用数学的重要分支，研究如何从数据中提取信息、进行推断和做出决策。从Fisher的极大似然估计到Neyman-Pearson的假设检验理论，从最小二乘法到现代机器学习，数理统计为科学研究和社会决策提供了严谨的数学基础。

---

## 2. 统计推断基础

### 2.1 统计模型

**定义 2.1** (统计模型): 统计模型是概率分布族 $\mathcal{P} = \{P_\theta : \theta \in \Theta\}$，其中 $\Theta$ 是参数空间。

**定义 2.2** (样本): 从 $P_\theta$ 中独立同分布抽取的 $X_1, \ldots, X_n$ 称为容量为 $n$ 的样本。

**定义 2.3** (统计量): 统计量 $T = T(X_1, \ldots, X_n)$ 是不依赖于未知参数的样本函数。

---

### 2.2 充分统计量

**定义 2.4** (充分统计量): 统计量 $T$ 对参数 $\theta$ 充分，若：
$$P(X_1, \ldots, X_n | T = t, \theta) = P(X_1, \ldots, X_n | T = t)$$
即给定 $T$ 后，样本不包含关于 $\theta$ 的额外信息。

**定理 2.1** (Neyman-Fisher因子分解定理): 统计量 $T$ 充分当且仅当：
$$f(x; \theta) = g(T(x), \theta) \cdot h(x)$$

---

## 3. 点估计

### 3.1 估计方法

**定义 3.1** (矩估计法): 用样本矩估计总体矩：
$$\hat{\mu}_k = \frac{1}{n}\sum_{i=1}^n X_i^k \approx E[X^k]$$

**定义 3.2** (极大似然估计): 似然函数 $L(\theta) = f(X_1, \ldots, X_n; \theta)$，MLE为：
$$\hat{\theta}_{MLE} = \arg\max_{\theta} L(\theta) = \arg\max_{\theta} \ell(\theta)$$
其中 $\ell(\theta) = \log L(\theta)$ 是对数似然函数。

**定理 3.1** (MLE的渐近正态性): 在正则条件下：
$$\sqrt{n}(\hat{\theta}_{MLE} - \theta) \xrightarrow{d} N(0, I(\theta)^{-1})$$
其中 $I(\theta)$ 是Fisher信息矩阵。

---

### 3.2 估计的优良性

**定义 3.3** (无偏性): 估计量 $\hat{\theta}$ 是无偏的，若 $E[\hat{\theta}] = \theta$。

**定义 3.4** (均方误差): 
$$\text{MSE}(\hat{\theta}) = E[(\hat{\theta} - \theta)^2] = \text{Var}(\hat{\theta}) + \text{Bias}^2(\hat{\theta})$$

**定理 3.2** (Rao-Blackwell定理): 设 $\hat{\theta}$ 是无偏估计，$T$ 是充分统计量，则 $\tilde{\theta} = E[\hat{\theta}|T]$ 优于 $\hat{\theta}$（方差更小或相等）。

**定理 3.3** (Cramér-Rao下界): 在正则条件下，任何无偏估计 $\hat{\theta}$ 满足：
$$\text{Var}(\hat{\theta}) \geq \frac{1}{nI(\theta)}$$

---

## 4. 假设检验

### 4.1 Neyman-Pearson框架

**定义 4.1** (假设检验): 原假设 $H_0: \theta \in \Theta_0$ vs 备择假设 $H_1: \theta \in \Theta_1$。

**定义 4.2** (检验函数): 检验函数 $\phi(x) \in \{0, 1\}$，拒绝域 $R = \{x : \phi(x) = 1\}$。

**定义 4.3** (两类错误):
- **第一类错误** (拒真): $\alpha = P_{\theta}(\text{拒绝 } H_0 | H_0 \text{ 真})$
- **第二类错误** (纳伪): $\beta = P_{\theta}(\text{接受 } H_0 | H_1 \text{ 真})$
- **功效**: $1 - \beta$

---

### 4.2 Neyman-Pearson引理

**定理 4.1** (Neyman-Pearson引理): 对简单假设 $H_0: \theta = \theta_0$ vs $H_1: \theta = \theta_1$，似然比检验：
$$\phi(x) = \begin{cases} 1 & \text{if } \Lambda(x) = \frac{L(\theta_1)}{L(\theta_0)} > k \\ 0 & \text{if } \Lambda(x) < k \end{cases}$$
是水平 $\alpha$ 的一致最优势检验。

---

### 4.3 常用检验

**定义 4.4** (t检验): 检验 $H_0: \mu = \mu_0$（方差未知）：
$$t = \frac{\bar{X} - \mu_0}{S/\sqrt{n}} \sim t_{n-1}$$

**定义 4.5** ($\chi^2$检验): 检验方差 $H_0: \sigma^2 = \sigma_0^2$：
$$\chi^2 = \frac{(n-1)S^2}{\sigma_0^2} \sim \chi^2_{n-1}$$

**定义 4.6** (似然比检验): 
$$\Lambda = \frac{\sup_{\theta \in \Theta_0} L(\theta)}{\sup_{\theta \in \Theta} L(\theta)}$$
在 $H_0$ 下，$-2\log\Lambda \xrightarrow{d} \chi^2_{\dim(\Theta) - \dim(\Theta_0)}$。

---

## 5. 区间估计

### 5.1 置信区间

**定义 5.1** (置信区间): 随机区间 $(L(X), U(X))$ 是 $\theta$ 的 $1-\alpha$ 置信区间，若：
$$P_\theta(L(X) \leq \theta \leq U(X)) = 1 - \alpha, \quad \forall \theta \in \Theta$$

**定理 5.1** (枢轴量法): 若 $Q(X, \theta)$ 的分布不依赖于 $\theta$，则：
$$P(q_{\alpha/2} \leq Q(X, \theta) \leq q_{1-\alpha/2}) = 1 - \alpha$$
反解出 $\theta$ 的置信区间。

---

### 5.2 正态总体参数置信区间

| 参数 | 条件 | 置信区间 |
|------|------|----------|
| $\mu$ | $\sigma^2$ 已知 | $\bar{X} \pm z_{\alpha/2}\frac{\sigma}{\sqrt{n}}$ |
| $\mu$ | $\sigma^2$ 未知 | $\bar{X} \pm t_{\alpha/2, n-1}\frac{S}{\sqrt{n}}$ |
| $\sigma^2$ | $\mu$ 未知 | $\left(\frac{(n-1)S^2}{\chi^2_{1-\alpha/2}}, \frac{(n-1)S^2}{\chi^2_{\alpha/2}}\right)$ |

---

## 6. 回归分析

### 6.1 线性回归

**定义 6.1** (线性模型): 
$$Y = X\beta + \varepsilon, \quad \varepsilon \sim N(0, \sigma^2I)$$
其中 $X$ 是 $n \times p$ 设计矩阵，$\beta$ 是 $p \times 1$ 参数向量。

**定理 6.1** (最小二乘估计): 
$$\hat{\beta}_{OLS} = (X^TX)^{-1}X^TY$$
在Gauss-Markov假设下，BLUE（最佳线性无偏估计）。

**定理 6.2**: $\hat{\beta} \sim N(\beta, \sigma^2(X^TX)^{-1})$。

---

### 6.2 假设检验与模型诊断

**定义 6.2** (回归显著性检验): 
$$F = \frac{SSR/p}{SSE/(n-p-1)} \sim F_{p, n-p-1}$$
其中 $SSR$ 是回归平方和，$SSE$ 是误差平方和。

**定义 6.3** ($R^2$): 决定系数
$$R^2 = \frac{SSR}{SST} = 1 - \frac{SSE}{SST}$$

---

## 7. 贝叶斯统计

### 7.1 贝叶斯推断

**定义 7.1** (先验与后验): 
$$\pi(\theta|x) = \frac{f(x|\theta)\pi(\theta)}{\int f(x|\theta)\pi(\theta)d\theta} = \frac{f(x|\theta)\pi(\theta)}{m(x)}$$

**定义 7.2** (贝叶斯估计):
- **后验均值**: $\hat{\theta} = E[\theta|X]$
- **MAP估计**: $\hat{\theta} = \arg\max_\theta \pi(\theta|X)$

**定理 7.1** (共轭先验): 
| 似然 | 共轭先验 | 后验 |
|------|----------|------|
| 二项分布 | Beta | Beta |
| 正态(均值) | 正态 | 正态 |
| 正态(方差) | 逆Gamma | 逆Gamma |
| Poisson | Gamma | Gamma |

---

## 8. 目录结构

```
docs/06-概率论与统计/03-数理统计/
├── 00-README.md                    # 本文件
├── 01-参数估计.md                   # 点估计与区间估计
├── 02-假设检验.md                   # Neyman-Pearson理论
├── 03-回归分析.md                   # 线性回归
├── 04-方差分析.md                   # ANOVA
├── 05-贝叶斯统计.md                 # 贝叶斯推断
└── 06-实战问题.md                   # 统计分析案例
```

---

## 9. 学习路径

### 9.1 基础路径
**概率论基础** → **点估计** → **假设检验** → **回归分析** → **贝叶斯统计**

### 9.2 应用领域
- **生物统计**: 临床试验、流行病学
- **经济计量**: 时间序列、面板数据
- **机器学习**: 统计学习理论、贝叶斯方法

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
