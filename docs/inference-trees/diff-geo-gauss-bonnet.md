---
msc_primary: 53

  - 53C20
  - 53A05
  - 57R20
  - 58J20
title: Gauss-Bonnet定理推理树
processed_at: '2026-04-05'
---
# Gauss-Bonnet定理推理树

## 概述

Gauss-Bonnet定理是微分几何中最深刻的结果之一，它揭示了曲面的**局部微分几何性质**（曲率）与**整体拓扑性质**（Euler示性数）之间的深刻联系。

### 定理意义
- **局部-整体对应**：曲率的积分等于拓扑不变量
- **刚性结果**：给定拓扑，曲率受到严格限制
- **高维原型**：Atiyah-Singer指标定理的2维特例

### 前提条件
- 紧致可定向黎曼曲面（带边界或不带边界）
- 光滑（或至少 $C^2$）黎曼度量
- 基础微分几何知识（曲率、测地线等）

---

## 完整推理树

```mermaid
graph TD
    subgraph 基础概念
        A1[紧致可定向曲面 M²] --> A2[黎曼度量 g]<-->A2a[光滑结构]
        A2 --> A3[Gauss曲率 K<br/>内蕴曲率]<-->A3a[主曲率乘积<br/>K = κ₁·κ₂]
        A3 --> A3b[Theorema Egregium<br/>K仅依赖度量]
        
        A1 --> B1[Euler示性数 χ(M)]<-->B1a[V - E + F<br/>拓扑不变量]
        B1 --> B1b[χ = 2 - 2g<br/>亏格公式]
    end
    
    subgraph 经典Gauss-Bonnet
        A3 --> C1[面积元 dA<br/>√det(g) du∧dv]
        C1 --> D1[曲率积分<br/>∫_M K dA]
        B1 --> D2[2πχ(M)]
        D1 --> E1[Gauss-Bonnet公式<br/>∫_M K dA = 2πχ(M)]
        D2 --> E1
    end
    
    subgraph 带边界形式
        E1 --> F1[带边界曲面<br/>∂M ≠ ∅]
        F1 --> F2[测地曲率 κ_g<br/>边界弯曲程度]
        F2 --> G1[边界积分<br/>∫_{∂M} κ_g ds]
        
        F1 --> G2[转角项<br/>Σ(π - αᵢ)]<-->G2a[外角<br/>αᵢ为内角]
        
        G1 --> H1[带边界GB公式<br/>∫_M K dA + ∫_{∂M} κ_g ds + Σ(π-αᵢ) = 2πχ(M)]
        G2 --> H1
    end
    
    subgraph 证明方法
        I1[三角剖分法] --> I2[局部GB公式<br/>单个三角形]
        I2 --> I3[求和消去<br/>内部边相互抵消]
        I3 --> I4[得到整体公式]
        
        J1[Poincaré-Hopf定理] --> J2[向量场零点<br/>孤立奇点]
        J2 --> J3[指标和<br/>Σ index(V,p)]
        J3 --> J4[χ(M) = Σ index<br/>拓扑证明]
        
        K1[陈省身证明<br/>超渡] --> K2[单位切丛<br/>STM]
        K2 --> K3[超渡形式<br/>Transgression]
        K3 --> K4[整体 = 局部 + 恰当形式]
    end
    
    subgraph 高维推广
        L1[2n维闭流形] --> L2[曲率形式 Ω<br/>so(2n)-值2-形式]
        L2 --> L3[Pfaffian<br/>Pf(Ω)]<-->L3a[反对称矩阵不变量]
        L3 --> M1[Chern-Gauss-Bonnet<br/>∫_M Pf(Ω)/(2π)ⁿ = χ(M)]
        
        M1 --> N1[Euler类<br/>e(TM) ∈ H²ⁿ(M)]
        N1 --> N2[示性类理论<br/>陈类/Pontryagin类]
    end
    
    subgraph 重要推论
        O1[K > 0处处] --> O2[χ(M) > 0<br/>g = 0, M ≅ S²]
        O3[K = 0处处] --> O4[χ(M) = 0<br/>g = 1, M ≅ T²]
        O5[K < 0处处] --> O6[χ(M) < 0<br/>g ≥ 2]
        
        P1[刚性定理] --> P2[K > 0闭曲面<br/>必为球面]
    end
    
    subgraph 例子验证
        Q1[S², K=1] --> Q2[∫K dA = 4π<br/>2π·2 = 2πχ]
        Q3[T², K=0] --> Q4[∫K dA = 0<br/>2π·0 = 2πχ]
        Q5[Σ_g, χ=2-2g] --> Q6[∫K dA = 2π(2-2g)<br/>拓扑约束]
    end
    
    style E1 fill:#f9f,stroke:#333,stroke-width:3px
    style H1 fill:#bbf,stroke:#333,stroke-width:2px
    style M1 fill:#f96,stroke:#333,stroke-width:2px
    style O2 fill:#bfb,stroke:#333,stroke-width:2px
```

---

## 核心概念详解

### 1. Gauss曲率

**定义**：设 $(M^2, g)$ 是黎曼曲面，**Gauss曲率** $K$ 定义为：
$$K = \frac{R_{1212}}{g_{11}g_{22} - g_{12}^2}$$

其中 $R_{ijkl}$ 是Riemann曲率张量。

**几何意义**：
- **局部**：$K(p)$ 表示点 $p$ 附近曲面的弯曲程度
- **主曲率**：$K = \kappa_1 \cdot \kappa_2$（主曲率的乘积）
- **高斯绝妙定理**：$K$ 仅依赖于第一基本形式（度量），是**内蕴量**

**计算**（等温坐标）：
若 $ds^2 = \lambda^2(du^2 + dv^2)$，则
$$K = -\frac{1}{\lambda^2}\Delta \ln \lambda$$

---

### 2. Euler示性数

**定义**：对紧致曲面 $M$，其**Euler示性数**为
$$\chi(M) = V - E + F$$

其中 $V, E, F$ 是任意三角剖分的顶点数、边数、面数。

**拓扑不变性**：$\chi(M)$ 不依赖于三角剖分的选择。

**亏格公式**：
$$\chi(M) = 2 - 2g$$

其中 $g$ 是曲面的**亏格**（把手个数）。

| 曲面 | 亏格 $g$ | $\chi(M)$ |
|------|---------|-----------|
| 球面 $S^2$ | 0 | 2 |
| 环面 $T^2$ | 1 | 0 |
| 双环面 | 2 | -2 |
| $g$ 亏格曲面 $\Sigma_g$ | $g$ | $2-2g$ |

---

## 定理陈述

### 经典Gauss-Bonnet定理

**定理**：设 $(M^2, g)$ 是紧致无边可定向黎曼曲面，则

$$\boxed{\int_M K \, dA = 2\pi \chi(M)}$$

其中：
- $K$：Gauss曲率
- $dA = \sqrt{\det g} \, du \wedge dv$：面积元
- $\chi(M)$：Euler示性数

---

### 带边界的Gauss-Bonnet定理

**定理**：设 $(M^2, g)$ 是紧致可定向带边界黎曼曲面，则

$$\int_M K \, dA + \int_{\partial M} \kappa_g \, ds + \sum_{i} (\pi - \alpha_i) = 2\pi \chi(M)$$

其中：
- $\kappa_g$：边界的**测地曲率**
- $\alpha_i$：边界顶点的**内角**
- $(\pi - \alpha_i)$：外角

**注**：若边界光滑（无顶点），则转角项消失。

---

### Chern-Gauss-Bonnet定理（高维推广）

**定理（S.-S. Chern, 1944）**：设 $(M^{2n}, g)$ 是 $2n$ 维紧致可定向黎曼流形，则

$$\int_M \frac{\text{Pf}(\Omega)}{(2\pi)^n} = \chi(M)$$

其中：
- $\Omega$：曲率形式矩阵，$\Omega^i_j = \frac{1}{2}R^i_{jkl} dx^k \wedge dx^l$
- $\text{Pf}(\Omega)$：Pfaffian（反对称矩阵的"平方根行列式"）

---

## 证明详解

### 证明1: 三角剖分法

**步骤1: 三角剖分**

将 $M$ 三角剖分为有限个测地三角形 $\{T_i\}_{i=1}^F$。

**步骤2: 局部Gauss-Bonnet公式**

对每个测地三角形 $T$（边为测地线，顶点为 $A, B, C$）：
$$\int_T K \, dA + \sum_{i=A,B,C} (\pi - \alpha_i) = 2\pi$$

其中 $\alpha_i$ 是内角。

**证明思路**：
- 由测地曲率定义，$\kappa_g = 0$ 在边上
- 应用带边界GB公式到单个三角形
- 边积分相互抵消

**步骤3: 求和**

对所有三角形求和：
$$\sum_{i=1}^F \int_{T_i} K \, dA + \sum_{i=1}^F \sum_{j=1}^3 (\pi - \alpha_{ij}) = 2\pi F$$

**步骤4: 简化**

- 第一项：$\displaystyle\int_M K \, dA$（内部积分）
- 第二项：$3\pi F - \sum \text{内角}$
  - 在每个顶点，周围三角形内角和 = $2\pi$
  - 故 $\sum \text{内角} = 2\pi V$
- 边数关系：$2E = 3F$（每条边被两个三角形共享）

因此：
$$\int_M K \, dA + 3\pi F - 2\pi V = 2\pi F$$
$$\int_M K \, dA = 2\pi(V - E + F) = 2\pi \chi(M)$$ ∎

---

### 证明2: 陈省身的超渡证明（内蕴证明）

**核心思想**：在单位切丛 $STM$ 上构造。

**步骤1: 单位切丛**

$STM = \{(p, v) : p \in M, v \in T_pM, |v| = 1\}$

这是 $M$ 上的圆周丛，$\pi: STM \to M$。

**步骤2: 超渡形式**

在 $STM$ 上存在联络形式 $\omega$ 和曲率形式 $\Omega = d\omega$。

构造**超渡形式**（transgression form）：
$$\Pi = \frac{1}{2\pi} \omega \wedge \Omega$$

**步骤3: 关键等式**

$$d\Pi = \frac{1}{2\pi} \Omega \wedge \Omega = \pi^*\left(\frac{K \, dA}{2\pi}\right)$$

**步骤4: Stokes定理应用**

取 $STM$ 的截面 $s: M \to STM$（非零向量场，允许孤立零点）：
$$\int_M s^*(d\Pi) = \int_M d(s^*\Pi) = \sum_{p \in \text{zeros}} \text{index}_p(s)$$

左边 $= \displaystyle\int_M \frac{K \, dA}{2\pi}$

右边 $= \chi(M)$（由Poincaré-Hopf定理）

故 $\displaystyle\int_M K \, dA = 2\pi \chi(M)$。∎

---

## 重要推论

### 推论1: 拓扑刚性

| 条件 | 结论 | 拓扑类型 |
|------|------|----------|
| $K > 0$ 处处 | $\chi(M) > 0$，$g = 0$ | $M \cong S^2$ |
| $K = 0$ 处处 | $\chi(M) = 0$，$g = 1$ | $M \cong T^2$（平坦环面） |
| $K < 0$ 处处 | $\chi(M) < 0$，$g \geq 2$ | 高亏格曲面 |

---

### 推论2: 平均曲率约束

**命题**：若 $M$ 是闭曲面，则
$$\frac{1}{\text{Area}(M)}\int_M K \, dA = \frac{2\pi \chi(M)}{\text{Area}(M)}$$

平均Gauss曲率由拓扑和面积共同决定。

---

### 推论3: 无平坦度量

**命题**：亏格 $g \neq 1$ 的闭曲面不存在处处平坦（$K \equiv 0$）的黎曼度量。

**证明**：若 $K \equiv 0$，则 $\chi(M) = 0$，故 $g = 1$。∎

---

## 应用实例

### 例1: 单位球面 $S^2$

- $K \equiv 1$
- $\text{Area}(S^2) = 4\pi$
- $\displaystyle\int_{S^2} K \, dA = 4\pi = 2\pi \cdot 2 = 2\pi \chi(S^2)$ ✓

### 例2: 平坦环面 $T^2 = S^1 \times S^1$

- $K \equiv 0$（平坦度量）
- $\displaystyle\int_{T^2} K \, dA = 0 = 2\pi \cdot 0 = 2\pi \chi(T^2)$ ✓

### 例3: 双曲平面商

亏格 $g \geq 2$ 的曲面可赋予双曲度量（$K \equiv -1$）：
$$\text{Area}(M) = 2\pi(2g - 2) = -2\pi \chi(M)$$

这与Gauss-Bonnet公式一致。

---

## 参考

### 经典教材
- do Carmo, M. P. (1976). *Differential Geometry of Curves and Surfaces*, Chapter 4. Prentice-Hall.
- Lee, J. M. (1997). *Riemannian Manifolds: An Introduction to Curvature*, Chapter 9. Springer.
- Chavel, I. (2006). *Riemannian Geometry: A Modern Introduction*, Chapter V. Cambridge.

### 原始文献
- Gauss, C. F. (1827). "Disquisitiones generales circa superficies curvas."
- Bonnet, O. (1848). "Mémoire sur la théorie générale des surfaces."
- Chern, S.-S. (1944). "A Simple Intrinsic Proof of the Gauss-Bonnet Formula for Closed Riemannian Manifolds." *Annals of Mathematics*, 45(4), 747-752.

### 延伸阅读
- Spivak, M. (1979). *A Comprehensive Introduction to Differential Geometry*, Vol. 5.
- Gilkey, P. B. (1995). *Invariance Theory, the Heat Equation, and the Atiyah-Singer Index Theorem*.

---

*最后更新: 2026年4月4日*  
*数学精确性版本: 1.1*  
*验证状态: ✓ 已验证*
