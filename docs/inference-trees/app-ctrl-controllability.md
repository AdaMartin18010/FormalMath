---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 可控性判定理论推导链

## 概述
本推理树展示线性系统可控性的完整理论，包括可控性矩阵判据、PBH判据、Kalman分解、可控标准型等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 系统描述
        A1[状态空间<br/>ẋ = Ax + Bu] --> A2[解的形式<br/>xt = e^{At}x₀ + ∫e^{At-τ}Buτdτ]
        A2 --> A3[可达集<br/>R_t = x: 存在u, xt = x]
        A3 --> A4[完全可控<br/>R_∞ = Rⁿ]
    end
    
    subgraph 可控性矩阵
        A1 --> B1[可控性矩阵<br/>C = [B AB A²B ... A^{n-1}B]]
        B1 --> B2[秩判据<br/>rankC = n]
        B2 --> B3[Gram矩阵<br/>W_t = ∫e^{Aτ}BB^Te^{A^Tτ}dτ]
        B3 --> B4[W_t正定<br/>⇔ 系统可控]
    end
    
    subgraph PBH判据
        B2 --> C1[特征值分析<br/>λᵢA]
        C1 --> C2[PBH秩判据<br/>rank[λI-A, B] = n, ∀λ]
        C2 --> C3[PBH特征向量<br/>v^TA = λv^T ⇒ v^TB ≠ 0]
        C3 --> C4[不可控模态<br/>v^TB = 0]
    end
    
    subgraph Kalman分解
        B2 --> D1[可控子空间<br/>ImC]
        D1 --> D2[坐标变换<br/>T = [C的基, 补空间基]]
        D2 --> D3[Kalman分解<br/>ẋ̃ = Ãx̃ + B̃u]
        D3 --> D4[标准形<br/>[A_c *; 0 A_ū], [B_c; 0]]
    end
    
    subgraph 可控标准型
        D4 --> E1[SISO系统<br/>单输入单输出]
        E1 --> E2[相伴矩阵<br/>A_c的特征多项式]
        E2 --> E3[可控标准型<br/>特定A,B结构]
        E3 --> E4[极点配置<br/>状态反馈]
    end
    
    subgraph 多变量扩展
        B1 --> F1[Kronecker指数<br/>μ₁,...,μ_m]
        F1 --> F2[Brunovsky标准型<br/>多块相伴矩阵]
        F2 --> F3[解耦控制<br/>多输入处理]
    end
    
    style B2 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style C2 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style D3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style E4 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：线性系统描述

**状态空间模型**：
$$\dot{x}(t) = Ax(t) + Bu(t)$$

其中：
- $x \in \mathbb{R}^n$：状态向量
- $u \in \mathbb{R}^m$：控制输入
- $A \in \mathbb{R}^{n \times n}$：系统矩阵
- $B \in \mathbb{R}^{n \times m}$：输入矩阵

**解的形式**：
$$x(t) = e^{At}x_0 + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**可控性定义**：系统在 $t_0$ 时刻可控，如果对任意 $x_0, x_f \in \mathbb{R}^n$，存在控制 $u(t)$ 使得 $x(t_f) = x_f$。

### 第二步：可控性矩阵判据

**可控性矩阵**：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**Kalman秩判据（定理）**：
$$(A, B) \text{ 可控} \Leftrightarrow \text{rank}(\mathcal{C}) = n$$

**证明概要**：

由Cayley-Hamilton定理，$A^n$ 可表示为 $I, A, \ldots, A^{n-1}$ 的线性组合。

状态转移：
$$x(t_f) = e^{At_f}x_0 + \int_0^{t_f} e^{A(t_f-\tau)}Bu(\tau)d\tau$$

展开指数矩阵：
$$e^{At} = \sum_{k=0}^{\infty} \frac{t^k A^k}{k!} = \sum_{k=0}^{n-1} A^k \phi_k(t)$$

因此：
$$x(t_f) - e^{At_f}x_0 = \sum_{k=0}^{n-1} A^k B \int_0^{t_f} \phi_k(t_f-\tau)u(\tau)d\tau$$

可达集 = $\text{Im}(\mathcal{C})$，当且仅当 $\text{rank}(\mathcal{C}) = n$ 时等于全空间。

### 第三步：Gram矩阵判据

**可控性Gram矩阵**：
$$W_c(t) = \int_0^t e^{A\tau}BB^Te^{A^T\tau}d\tau$$

**判据**：$(A, B)$ 可控当且仅当 $W_c(t)$ 正定（对任意 $t > 0$）。

**最优控制**：从 $x_0$ 到 $x_f$ 的最小能量控制：
$$u^*(t) = B^T e^{A^T(t_f-t)} W_c^{-1}(t_f)(x_f - e^{At_f}x_0)$$

### 第四步：PBH判据

**PBH秩判据（Popov-Belevitch-Hautus）**：

$$(A, B) \text{ 可控} \Leftrightarrow \text{rank}[\lambda I - A, B] = n, \quad \forall \lambda \in \mathbb{C}$$

**等价形式（特征向量判据）**：
对任意左特征向量 $v^T A = \lambda v^T$，有 $v^T B \neq 0$。

**证明**：
若存在 $\lambda$ 使得 $\text{rank}[\lambda I - A, B] < n$，则存在非零 $v$：
$$v^T[\lambda I - A, B] = 0 \Rightarrow v^T A = \lambda v^T, v^T B = 0$$

则：$v^T A^k B = \lambda^k v^T B = 0$，故 $v^T \mathcal{C} = 0$，不可控。

**不可控模态**：若 $v^T B = 0$，则模态 $v^T x$ 不受控制影响。

### 第五步：Kalman分解

**可控子空间**：$\mathcal{R} = \text{Im}(\mathcal{C})$

**坐标变换**：选择基变换矩阵 $T$ 使得：
- 前 $r = \dim(\mathcal{R})$ 列为 $\mathcal{R}$ 的基
- 后 $n-r$ 列补全为 $\mathbb{R}^n$ 的基

**Kalman标准形**：
$$\tilde{A} = T^{-1}AT = \begin{bmatrix} A_c & A_{12} \\ 0 & A_{\bar{c}} \end{bmatrix}, \quad \tilde{B} = T^{-1}B = \begin{bmatrix} B_c \\ 0 \end{bmatrix}$$

其中 $(A_c, B_c)$ 可控，$\dot{x}_{\bar{c}} = A_{\bar{c}}x_{\bar{c}}$ 不可控。

### 第六步：可控标准型

**SISO系统**（$m=1$）：

设特征多项式：$\det(sI - A) = s^n + a_{n-1}s^{n-1} + \cdots + a_0$

**可控标准型**：
$$A_c = \begin{bmatrix} 0 & 1 & 0 & \cdots & 0 \\ 0 & 0 & 1 & \cdots & 0 \\ \vdots & & & \ddots & \vdots \\ 0 & 0 & 0 & \cdots & 1 \\ -a_0 & -a_1 & -a_2 & \cdots & -a_{n-1} \end{bmatrix}, \quad b_c = \begin{bmatrix} 0 \\ 0 \\ \vdots \\ 0 \\ 1 \end{bmatrix}$$

**极点配置**：状态反馈 $u = -Kx$ 可任意配置闭环特征值。

---

## 可控性判据汇总

| 判据 | 条件 | 计算复杂度 |
|------|------|------------|
| Kalman秩 | $\text{rank}[B, AB, \ldots, A^{n-1}B] = n$ | $O(n^3)$ |
| Gram矩阵 | $W_c(t) > 0$ | 需积分 |
| PBH秩 | $\text{rank}[\lambda I - A, B] = n, \forall \lambda$ | $O(n^3)$ |
| PBH特征向量 | 无左特征向量与 $B$ 正交 | 需特征分解 |

---

## 依赖关系图

```

线性系统理论
    ↓
状态空间分析 ← 矩阵指数
    ↓
可控性矩阵 ← Cayley-Hamilton
    ↓
Kalman秩判据 = Gram矩阵判据
    ↓
PBH判据 ← 特征分析
    ↓
Kalman分解 ← 线性代数
    ↓
可控标准型 + 极点配置

```

---

## 关键引理汇总

| 引理/定理 | 内容 | 作用 |
|-----------|------|------|
| Cayley-Hamilton | $p_A(A) = 0$ | 降次展开 |
| 矩阵指数展开 | $e^{At} = \sum A^k \phi_k(t)$ | 解的表达 |
| PBH判据 | 特征向量与B非正交 | 模态分析 |
| Kalman分解 | 可控与不可控分离 | 系统简化 |

---

## 参考

- Kalman, R. E. (1963). "Mathematical Description of Linear Dynamical Systems"
- Hautus, M. L. J. (1969). "Controllability and Observability Conditions"
- Wonham, W. M. (1985). *Linear Multivariable Control*
- Kailath, T. (1980). *Linear Systems*
- Sontag, E. D. (1998). *Mathematical Control Theory*

---

*生成时间：2026年4月*
