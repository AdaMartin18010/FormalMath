---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 梯度下降收敛性推导链

## 概述
本推理树展示梯度下降算法收敛性的完整数学分析，包括凸优化收敛率、强凸性加速、随机梯度下降收敛性等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 优化基础
        A1[光滑函数<br/>L-Lipschitz梯度] --> A2[凸函数<br/>fλ+(1-λ)f ≤ fλ]
        A2 --> A3[强凸函数<br/>f(y) ≥ f(x) + ∇f·(y-x) + μ/2\|y-x\|²]

        A3 --> A4[最优解存在<br/>x* = argmin f]
    end
    
    subgraph 梯度下降
        A4 --> B1[迭代格式<br/>xₖ₊₁ = xₖ - αₖ∇fₖ]
        B1 --> B2[步长选择<br/>固定/递减/线搜索]
        B2 --> B3[下降引理<br/>fₖ₊₁ ≤ fₖ - α\|∇fₖ\|²/2]

    end
    
    subgraph 凸函数收敛
        B3 --> C1[收敛到最优<br/>fₖ - f* → 0]
        C1 --> C2[次线性收敛<br/>fₖ - f* = O(1/k)]
        C2 --> C3[最优步长<br/>α = 1/L]
    end
    
    subgraph 强凸加速
        A3 --> D1[二次下界<br/>f(y) - f* ≥ μ/2\|y-x*\|²]
        D1 --> D2[线性收敛<br/>\|xₖ - x*\|² ≤ ρᵏ\|x₀ - x*\|²]

        D2 --> D3[条件数<br/>κ = L/μ]
        D3 --> D4[收敛率<br/>ρ = (κ-1)/(κ+1)]
    end
    
    subgraph 加速方法
        D4 --> E1[动量法<br/>vₖ = βvₖ₋₁ + ∇fₖ]
        E1 --> E2[Nesterov加速<br/>yₖ = xₖ + β(xₖ - xₖ₋₁)]
        E2 --> E3[最优收敛率<br/>O(1/k²)凸 / O(ρᵏ)强凸]
    end
    
    subgraph 随机梯度
        B1 --> F1[SGD迭代<br/>xₖ₊₁ = xₖ - αₖgₖ]
        F1 --> F2[无偏梯度<br/>E[gₖ] = ∇fₖ]
        F2 --> F3[方差控制<br/>E[\|gₖ\|²] ≤ σ²]

        F3 --> F4[递减步长<br/>αₖ = O(1/√k)]
        F4 --> F5[收敛性<br/>E[fₖ] - f* = O(1/√k)]
    end
    
    style C3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style D4 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style E3 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px
    style F5 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：函数性质定义

**L-光滑性（Lipschitz梯度）**：
$$\|\nabla f(x) - \nabla f(y)\| \leq L \|x - y\|, \quad \forall x, y$$

等价表述：
$$f(y) \leq f(x) + \nabla f(x)^T(y-x) + \frac{L}{2}\|y-x\|^2$$

**凸性**：
$$f(\lambda x + (1-\lambda)y) \leq \lambda f(x) + (1-\lambda)f(y)$$

等价表述：
$$f(y) \geq f(x) + \nabla f(x)^T(y-x)$$

**强凸性（参数 $\mu > 0$）**：
$$f(y) \geq f(x) + \nabla f(x)^T(y-x) + \frac{\mu}{2}\|y-x\|^2$$

**条件数**：$\kappa = \frac{L}{\mu} \geq 1$

### 第二步：梯度下降迭代

**标准格式**：
$$x_{k+1} = x_k - \alpha_k \nabla f(x_k)$$

**最优固定步长**：$\alpha = \frac{1}{L}$

**下降引理**（由光滑性）：
$$f(x_{k+1}) \leq f(x_k) - \alpha\left(1 - \frac{\alpha L}{2}\right)\|\nabla f(x_k)\|^2$$

当 $\alpha = \frac{1}{L}$ 时：
$$f(x_{k+1}) \leq f(x_k) - \frac{1}{2L}\|\nabla f(x_k)\|^2$$

### 第三步：凸函数收敛分析

**定理（凸函数收敛率）**：设 $f$ 为凸且 $L$-光滑，步长 $\alpha = \frac{1}{L}$，则：

$$f(x_k) - f(x^*) \leq \frac{2L\|x_0 - x^*\|^2}{k}$$

**证明概要**：
1. 由凸性：$f(x_k) - f(x^*) \leq \nabla f_k^T(x_k - x^*)$
2. 由下降引理累加
3. 利用 $\sum_{i=1}^k \|\nabla f_i\|^2 \geq \frac{1}{k}(\sum_{i=1}^k \|\nabla f_i\|)^2$

**收敛速度**：$O(1/k)$ —— 次线性收敛

### 第四步：强凸函数收敛分析

**定理（强凸函数线性收敛）**：设 $f$ 为 $\mu$-强凸且 $L$-光滑，则：

$$\|x_{k+1} - x^*\|^2 \leq \left(1 - \frac{\mu}{L}\right)\|x_k - x^*\|^2$$

即：
$$\|x_k - x^*\|^2 \leq \left(1 - \frac{1}{\kappa}\right)^k \|x_0 - x^*\|^2$$

**证明**：
1. $x_{k+1} - x^* = (x_k - x^*) - \frac{1}{L}\nabla f_k$
2. 由强凸性：$\|\nabla f_k\|^2 \geq \mu^2\|x_k - x^*\|^2$

3. 结合光滑性得收敛界

**收敛速度**：$O(\rho^k)$，其中 $\rho = 1 - \frac{1}{\kappa} < 1$ —— 线性收敛

### 第五步：Nesterov加速梯度

**动量法（Polyak）**：
$$v_{k+1} = \beta v_k + \nabla f(x_k)$$
$$x_{k+1} = x_k - \alpha v_{k+1}$$

**Nesterov加速**：
$$y_k = x_k + \beta_k(x_k - x_{k-1})$$
$$x_{k+1} = y_k - \alpha \nabla f(y_k)$$

**收敛率**：
- 凸函数：$f(x_k) - f(x^*) = O(1/k^2)$（最优）
- 强凸函数：$\|x_k - x^*\|^2 = O((1 - \frac{1}{\sqrt{\kappa}})^k)$

### 第六步：随机梯度下降

**SGD迭代**：
$$x_{k+1} = x_k - \alpha_k g_k$$

其中 $E[g_k | x_k] = \nabla f(x_k)$（无偏性）

**假设**：$E[\|g_k\|^2] \leq \sigma^2 + c\|\nabla f_k\|^2$

**递减步长**：$\alpha_k = \frac{\alpha_0}{\sqrt{k}}$ 或 $\frac{\alpha_0}{k}$

**收敛定理**：
- 凸函数：$E[f(\bar{x}_k)] - f(x^*) = O(1/\sqrt{k})$
- 强凸函数：$E[\|x_k - x^*\|^2] = O(1/k)$

---

## 收敛率对比

| 算法 | 凸函数 | 强凸函数 | 计算复杂度 |
|------|--------|----------|------------|
| 梯度下降 | $O(1/k)$ | $O(\rho^k)$ | 每步全梯度 |
| 加速梯度 | $O(1/k^2)$ | $O(\rho_{opt}^k)$ | 每步全梯度 |
| SGD | $O(1/\sqrt{k})$ | $O(1/k)$ | 每步随机梯度 |
| SVRG | $O(1/k)$ | $O(\rho^k)$ | 周期性全梯度 |

---

## 依赖关系图

```

凸分析基础
    ↓
光滑性条件 ← Lipschitz梯度
    ↓
梯度下降基本迭代
    ↓
凸函数: O(1/k)  强凸函数: O(ρᵏ)
    ↓                ↓
    └──── Nesterov加速 ────┘
              ↓
        最优收敛率
              ↓
        随机梯度扩展

```

---

## 关键不等式汇总

| 不等式 | 形式 | 用途 |
|--------|------|------|
| 下降引理 | $f_{k+1} \leq f_k - \frac{1}{2L}\|\nabla f_k\|^2$ | 收敛基础 |
| 强凸性 | $\|\nabla f\|^2 \geq 2\mu(f - f^*)$ | 线性收敛 |
| Polyak-Lojasiewicz | $\|\nabla f\|^2 \geq 2\mu(f - f^*)$ | 非凸收敛 |
| 共轭梯度 | $O(\sqrt{\kappa}\ln(1/\epsilon))$ | 最优迭代复杂度 |

---

## 参考

- Nesterov, Y. (2004). *Introductory Lectures on Convex Optimization*
- Boyd, S. & Vandenberghe, L. (2004). *Convex Optimization*
- Bottou, L., Curtis, F. E., & Nocedal, J. (2018). "Optimization Methods for Large-Scale Machine Learning"
- Bubeck, S. (2015). "Convex Optimization: Algorithms and Complexity"

---

*生成时间：2026年4月*
