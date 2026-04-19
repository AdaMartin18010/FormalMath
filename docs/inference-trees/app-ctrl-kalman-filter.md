---
msc_primary: 00

  - 00A99
title: Kalman滤波推导链
processed_at: '2026-04-05'
---
# Kalman滤波推导链

## 概述
本推理树展示Kalman滤波器的完整数学推导，包括最小均方误差估计、正交投影原理、递推更新方程、Riccati方程等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 系统模型
        A1[状态方程<br/>x_k = Fx_{k-1} + w_{k-1}] --> A2[观测方程<br/>z_k = Hx_k + v_k]
        A2 --> A3[噪声假设<br/>w ~ N0,Q, v ~ N0,R]
        A3 --> A4[高斯性质<br/>保持高斯分布]
    end
    
    subgraph 估计问题
        A4 --> B1[预测估计<br/>x̂_k^- = Fx̂_{k-1}]
        B1 --> B2[预测误差<br/>e_k^- = x_k - x̂_k^-]
        B2 --> B3[预测协方差<br/>P_k^- = Ee_k^-e_k^{-T}]
    end
    
    subgraph 更新方程
        B3 --> C1[卡尔曼增益<br/>K_k = P_k^-H^THP_k^-H^T + R^{-1}]
        C1 --> C2[状态更新<br/>x̂_k = x̂_k^- + K_kz_k - Hx̂_k^-]
        C2 --> C3[协方差更新<br/>P_k = I - K_kHP_k^-]
        C3 --> C4[Joseph形式<br/>数值稳定版本]
    end
    
    subgraph 正交投影
        B1 --> D1[线性估计<br/>x̂ = Az]
        D1 --> D2[正交原理<br/>Ee - x̂z^T = 0]
        D2 --> D3[投影定理<br/>最小方差 = 正交投影]
        D3 --> C1
    end
    
    subgraph Riccati方程
        C3 --> E1[离散Riccati<br/>P_k = FP_{k-1}F^T + Q - KHP_{k-1}F^T]
        E1 --> E2[稳态分析<br/>P = lim P_k]
        E2 --> E3[代数Riccati<br/>P = FPF^T + Q - FPH^THPH^T + R^{-1}HPF^T]
        E3 --> E4[可检测性+可稳性<br/>解存在唯一]
    end
    
    subgraph 扩展方法
        A1 --> F1[EKF<br/>非线性一阶展开]
        F1 --> F2[UKF<br/>无迹变换]
        F2 --> F3[粒子滤波<br/>蒙特卡洛]
    end
    
    style C2 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style C1 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style D3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style E4 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：离散时间状态空间模型

**状态方程**：
$$x_k = F_{k-1}x_{k-1} + G_{k-1}u_{k-1} + w_{k-1}$$

**观测方程**：
$$z_k = H_k x_k + v_k$$

其中：
- $x_k \in \mathbb{R}^n$：状态向量
- $z_k \in \mathbb{R}^m$：观测向量
- $w_{k-1} \sim \mathcal{N}(0, Q_{k-1})$：过程噪声
- $v_k \sim \mathcal{N}(0, R_k)$：观测噪声
- 假设 $w$ 与 $v$ 独立，且与初始状态独立

### 第二步：估计问题定义

**符号定义**：
- $\hat{x}_k^-$：先验估计（预测）
- $\hat{x}_k$：后验估计（更新）
- $e_k^- = x_k - \hat{x}_k^-$：先验估计误差
- $e_k = x_k - \hat{x}_k$：后验估计误差
- $P_k^- = E[e_k^- e_k^{-T}]$：先验误差协方差
- $P_k = E[e_k e_k^T]$：后验误差协方差

**目标**：最小化 $E[\|e_k\|^2] = \text{tr}(P_k)$

### 第三步：预测步骤

**状态预测**：
$$\hat{x}_k^- = F_{k-1}\hat{x}_{k-1} + G_{k-1}u_{k-1}$$

**误差协方差预测**：
$$P_k^- = F_{k-1}P_{k-1}F_{k-1}^T + Q_{k-1}$$

**推导**：
$$e_k^- = x_k - \hat{x}_k^- = F_{k-1}e_{k-1} + w_{k-1}$$

$$P_k^- = E[(F_{k-1}e_{k-1} + w_{k-1})(F_{k-1}e_{k-1} + w_{k-1})^T]$$
$$= F_{k-1}P_{k-1}F_{k-1}^T + Q_{k-1}$$

（交叉项 $E[e_{k-1}w_{k-1}^T] = 0$ 由独立性）

### 第四步：更新步骤

**新息（Innovation）**：
$$\tilde{y}_k = z_k - H_k\hat{x}_k^- = H_k e_k^- + v_k$$

**新息协方差**：
$$S_k = E[\tilde{y}_k\tilde{y}_k^T] = H_k P_k^- H_k^T + R_k$$

**卡尔曼增益推导**：

设状态更新：$\hat{x}_k = \hat{x}_k^- + K_k\tilde{y}_k$

后验误差：
$$e_k = x_k - \hat{x}_k = (I - K_kH_k)e_k^- - K_kv_k$$

后验协方差：
$$P_k = (I - K_kH_k)P_k^-(I - K_kH_k)^T + K_kR_kK_k^T$$

**最优增益**（最小化 $\text{tr}(P_k)$）：

$$\frac{\partial \text{tr}(P_k)}{\partial K_k} = 0 \Rightarrow K_k = P_k^-H_k^T(H_kP_k^-H_k^T + R_k)^{-1}$$

**简化协方差更新**：
$$P_k = (I - K_kH_k)P_k^-$$

### 第五步：正交投影解释

**投影定理**：最小均方误差估计等价于在观测空间上的正交投影。

**正交性条件**：
$$E[(x_k - \hat{x}_k)z_j^T] = 0, \quad j = 1, \ldots, k$$

**新息正交性**：
$$E[\tilde{y}_k \tilde{y}_j^T] = 0, \quad k \neq j$$

新息序列 $\{\tilde{y}_k\}$ 为白噪声过程。

### 第六步：离散Riccati方程

将卡尔曼增益代入协方差更新：

$$P_k = F_{k-1}P_{k-1}F_{k-1}^T + Q_{k-1}$$
$$- F_{k-1}P_{k-1}H_{k-1}^T(H_{k-1}P_{k-1}H_{k-1}^T + R_{k-1})^{-1}H_{k-1}P_{k-1}F_{k-1}^T$$

**稳态分析**（时不变系统）：

若 $(F, H)$ 可检测，$(F, Q^{1/2})$ 可稳，则 $P_k \to P$（唯一正定解）。

**代数Riccati方程**：
$$P = FPF^T + Q - FPH^T(HPH^T + R)^{-1}HPF^T$$

**稳态卡尔曼增益**：
$$K = PH^T(HPH^T + R)^{-1}$$

### 第七步：数值稳定性改进

**Joseph形式**（保证协方差矩阵对称正定）：
$$P_k = (I - K_kH_k)P_k^-(I - K_kH_k)^T + K_kR_kK_k^T$$

**平方根滤波**：直接传播 $P^{1/2}$，避免数值问题。

---

## Kalman滤波算法总结

```

初始化: x̂₀, P₀

对每个时间步 k = 1, 2, ...:
    # 预测
    x̂ₖ⁻ = F_{k-1}x̂_{k-1} + G_{k-1}u_{k-1}
    Pₖ⁻ = F_{k-1}P_{k-1}F_{k-1}^T + Q_{k-1}
    
    # 更新
    Kₖ = Pₖ⁻Hₖ^T(HₖPₖ⁻Hₖ^T + Rₖ)^{-1}
    x̂ₖ = x̂ₖ⁻ + Kₖ(zₖ - Hₖx̂ₖ⁻)
    Pₖ = (I - KₖHₖ)Pₖ⁻

```

---

## 依赖关系图

```

线性系统理论
    ↓
随机过程基础 ← 高斯分布
    ↓
最小均方估计 ← 正交投影
    ↓
预测方程 ← 状态传播
    ↓
卡尔曼增益 ← 优化理论
    ↓
更新方程
    ↓
Riccati方程 ← 稳定性分析

```

---

## 关键公式汇总

| 名称 | 公式 | 作用 |
|------|------|------|
| 状态预测 | $\hat{x}_k^- = F\hat{x}_{k-1}$ | 时间更新 |
| 协方差预测 | $P_k^- = FP_{k-1}F^T + Q$ | 不确定性增长 |
| 卡尔曼增益 | $K_k = P_k^-H^T(HP_k^-H^T + R)^{-1}$ | 最优权重 |
| 状态更新 | $\hat{x}_k = \hat{x}_k^- + K_k(z_k - H\hat{x}_k^-)$ | 观测融合 |
| 协方差更新 | $P_k = (I - K_kH)P_k^-$ | 不确定性减小 |

---

## 扩展方法对比

| 方法 | 非线性处理 | 计算复杂度 | 精度 |
|------|-----------|-----------|------|
| 标准KF | 不适用 | $O(n^3)$ | 精确 |
| EKF | 一阶泰勒 | $O(n^3)$ | 近似 |
| UKF | 无迹变换 | $O(n^3)$ | 二阶近似 |
| 粒子滤波 | 蒙特卡洛 | $O(N)$ | 渐近精确 |

---

## 参考

- Kalman, R. E. (1960). "A New Approach to Linear Filtering and Prediction Problems"
- Kalman, R. E. & Bucy, R. S. (1961). "New Results in Linear Filtering and Prediction Theory"
- Anderson, B. D. O. & Moore, J. B. (1979). *Optimal Filtering*
- Grewal, M. S. & Andrews, A. P. (2015). *Kalman Filtering: Theory and Practice*
- Simon, D. (2006). *Optimal State Estimation: Kalman, H∞, and Nonlinear Approaches*

---

*生成时间：2026年4月*
