---
title: 曲面分类初步
msc_primary: 14-01
msc_secondary:
- 14J10
- 14J26
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 28
topic: 代数曲面分类
exercise_type: CLA (分类型)
difficulty: ⭐⭐⭐⭐
importance: ★★
---

# AG-VK-012: 曲面分类初步

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 28: 曲面理论 |
| **对应FOAG习题** | 28.2.H |
| **类型** | CLA (分类型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $S$ 是代数闭域 $k$ 上的光滑射影曲面。

**(a)** **相交理论的基本结果**：

设 $C, D$ 是 $S$ 上的曲线（除子）。证明相交配对满足：
1. 双线性：$(C_1 + C_2) \cdot D = C_1 \cdot D + C_2 \cdot D$
2. 对称性：$C \cdot D = D \cdot C$
3. Hodge指标定理：在 $N^1(S) \otimes \mathbb{R}$ 上，相交形式 $(1, \rho - 1)$ 型

**(b)** **曲面的数值不变量**：

定义曲面的基本不变量：
- 几何亏格：$p_g = h^0(S, K_S)$
- 不规则性：$q = h^1(S, \mathcal{O}_S)$
- 欧拉示性数：$\chi(\mathcal{O}_S) = 1 - q + p_g$
- 自交数：$K_S^2$

证明Noether公式：
$$12\chi(\mathcal{O}_S) = K_S^2 + c_2(S)$$

其中 $c_2(S)$ 是切丛的第二Chern类，等于拓扑欧拉示性数。

**(c)** **Kodaira维数**：

定义并计算以下曲面的Kodaira维数：
1. 有理曲面（如 $\mathbb{P}^2$，$\mathbb{P}^1 \times \mathbb{P}^1$）
2. K3曲面（$K_S \cong \mathcal{O}_S$，$q = 0$）
3. 一般型曲面（$K_S$ 丰沛）

---

## 解题思路

### 思路概述

本题涉及**代数曲面分类的核心内容**：
- **相交理论** - 曲面上的曲线相交
- **数值不变量** - 曲面的基本特征
- **Kodaira维数** - 分类的核心概念

### Enriques-Kodaira分类

```
代数曲面分类（按Kodaira维数）

κ = -∞:  有理曲面或直纹曲面
          P^2, P^1 × P^1, F_n, ...
          
κ = 0:   K3曲面, Enriques曲面, 
         Abel曲面, 超椭圆曲面
         
κ = 1:   椭圆曲面（有椭圆纤维化）

κ = 2:   一般型曲面（K_S 丰沛）
         最丰富的类
```

---

## 详细解答

### (a) 相交理论的基本结果

**相交配对的构造**：

对曲线 $C, D \subset S$，定义 $C \cdot D = \deg(\mathcal{O}(D)|_C) = \chi(\mathcal{O}_C) - \chi(\mathcal{O}_C(-D))$。

**性质证明**：

**1. 双线性**：

$(C_1 + C_2) \cdot D = \deg(\mathcal{O}(D)|_{C_1 + C_2}) = \deg(\mathcal{O}(D)|_{C_1}) + \deg(\mathcal{O}(D)|_{C_2}) = C_1 \cdot D + C_2 \cdot D$

**2. 对称性**：

需要证明 $C \cdot D = D \cdot C$。

若 $C$ 和 $D$ 横截相交，两者都等于交点数 $|C \cap D|$。

一般情形用Chow移动引理（$\dim S = 2$）。

**3. Hodge指标定理**：

设 $N^1(S) = \operatorname{Pic}(S) / \operatorname{Pic}^0(S) \otimes \mathbb{R} \cong \mathbb{R}^\rho$（Néron-Severi群）。

**定理**：相交形式在 $N^1(S)$ 上有符号 $(1, \rho - 1)$。

**证明概要**：

- 由Hodge分解和Lefschetz $(1,1)$-定理，$N^1(S) \subset H^{1,1}(S)$。
- Hodge-Riemann双线性关系给出符号 $(h^{1,1} - 1, 1)$。
- 但 $N^1(S)$ 不一定等于 $H^{1,1}(S) \cap H^2(S, \mathbb{Q})$。

实际上，代数版本（由Grothendieck证明）说：在由丰沛除子张成的超平面的正交补上，相交形式负定。

所以整体符号是 $(1, \rho - 1)$。∎

### (b) Noether公式

**定理**：
$$12\chi(\mathcal{O}_S) = K_S^2 + c_2(S)$$

**证明**：

**步骤1**: Hirzebruch-Riemann-Roch对 $\mathcal{O}_S$。

$$\chi(\mathcal{O}_S) = \int_S \operatorname{ch}(\mathcal{O}_S) \cdot \operatorname{td}(T_S) = \int_S \operatorname{td}(T_S)$$

**步骤2**: Todd类的展开。

$$\operatorname{td}(T_S) = 1 + \frac{1}{2}c_1 + \frac{1}{12}(c_1^2 + c_2) + \cdots$$

$c_1 = -K_S$（因为 $c_1(T_S) = -c_1(K_S) = -K_S$）。

**步骤3**: 积分。

$$\chi(\mathcal{O}_S) = \frac{1}{12}(K_S^2 + c_2(S))$$

即 $12\chi(\mathcal{O}_S) = K_S^2 + c_2(S)$。∎

**注**：$c_2(S) = \chi_{\text{top}}(S) = \sum (-1)^i b_i(S)$ 是拓扑欧拉示性数。

### (c) Kodaira维数

**定义**：
$$\kappa(S) = \operatorname{tr.deg} \bigoplus_{n \geq 0} H^0(S, nK_S) - 1$$

或等价地：$\kappa(S) = \dim \phi_{nK_S}(S)$ 对充分大的 $n$（若 $h^0(nK_S) \to \infty$），否则 $\kappa = -\infty$。

**具体计算**：

**1. 有理曲面（$\kappa = -\infty$）**：

$\mathbb{P}^2$：$K = -3H$，$nK$ 无整体截面（$n > 0$）。

所以 $h^0(nK) = 0$，$\kappa = -\infty$。

**2. K3曲面（$\kappa = 0$）**：

$K_S \cong \mathcal{O}_S$，所以 $nK_S \cong \mathcal{O}_S$。

$h^0(nK_S) = 1$ 对所有 $n$。

所以 $\kappa = 0$。

**3. 一般型曲面（$\kappa = 2$）**：

$K_S$ 丰沛，则 $\phi_{nK_S}$ 对充分大的 $n$ 给出嵌入。

所以 $\kappa = \dim S = 2$。

**分类表**：

| Kodaira维数 | 曲面类型 | $h^0(nK)$ 行为 |
|-------------|----------|----------------|
| $-\infty$ | 有理、直纹 | 恒为零 |
| 0 | K3, Enriques, Abel, 超椭圆 | 有界 |
| 1 | 椭圆曲面 | 线性增长 |
| 2 | 一般型 | 二次增长 |

---

## 关键概念

### Néron-Severi群

$$NS(S) = \operatorname{Pic}(S) / \operatorname{Pic}^0(S)$$

- 有限生成自由Abel群
- 秩 $\rho = \operatorname{rank} NS(S)$ 是Picard数
- 与Hodge理论：$NS(S) = H^{1,1}(S) \cap H^2(S, \mathbb{Z})$

### 曲面的双有理几何

**Castelnuovo收缩准则**：曲线 $C \subset S$ 可收缩当且仅当 $C \cong \mathbb{P}^1$ 且 $C^2 = -1$。

**极小模型**：无 $(-1)$-曲线的曲面。

---

## 重要例子

### Hirzebruch曲面

$$\mathbb{F}_n = \mathbb{P}(\mathcal{O}_{\mathbb{P}^1} \oplus \mathcal{O}_{\mathbb{P}^1}(n))$$

- $\mathbb{F}_0 = \mathbb{P}^1 \times \mathbb{P}^1$
- $\mathbb{F}_1$ 是 $\mathbb{P}^2$ 吹起一个点
- 所有 $\mathbb{F}_n$（$n \geq 1$）是极小的

### K3曲面的例子

**光滑四次曲面**：$S \subset \mathbb{P}^3$，$\deg(S) = 4$。

- $K_S = \mathcal{O}_S(4-4) = \mathcal{O}_S$
- $q = h^1(\mathcal{O}_S) = 0$（Lefschetz超平面定理）

所以 $S$ 是K3曲面。

---

## 变式练习

### 变式 1: 直纹曲面的不变量

设 $S = \mathbb{P}(\mathcal{E}) \to C$ 是曲线 $C$ 上的直纹面。计算 $K_S^2$ 和 $\chi(\mathcal{O}_S)$。

### 变式 2: Enriques曲面

定义并证明Enriques曲面的性质：$2K_S \sim 0$，$K_S \not\sim 0$，$q = p_g = 0$。

### 变式 3: Bogomolov-Miyaoka-Yau不等式

对一般型极小曲面，陈述并解释：
$$K_S^2 \leq 3c_2(S)$$

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为K3曲面上 $K = 0$ | 是 $K \cong \mathcal{O}$，不是数值零 |
| 混淆Kodaira维数和几何亏格 | 不同概念 |
| 忽略极小模型 | 分类需要先做极小化 |

---

## 学习建议

1. **掌握相交理论**：曲面上曲线相交的计算
2. **研究具体例子**：有理曲面、K3曲面等
3. **理解极小模型**：双有理分类的基础

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-012-曲面分类初步.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
