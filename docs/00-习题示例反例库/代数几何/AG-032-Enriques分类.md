---
习题编号: AG-032
学科: 代数几何
知识点: 曲面理论-Enriques分类
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Enriques曲面分类

## 题目

设 $S$ 是极小光滑射影曲面，$K_S$ 是典范除子。

**(a)** 定义Kodaira维数 $\kappa(S)$ 为 $\dim \varphi_{nK}(S)$ 对 $n$ 大的增长。

**(b)** 陈述Enriques分类：曲面按 $\kappa = -\infty, 0, 1, 2$ 分类，并给出各类例子。

**(c)** 证明Castelnuovo判据：$S$ 是有理曲面当且仅当 $P_2 = q = 0$。

## 解答

### (a) Kodaira维数

**定义：**

$\kappa(S) = \text{tr.deg} \bigoplus_{n \geq 0} H^0(S, nK_S) - 1$，或 $-\infty$ 若所有 $P_n = 0$。

分类：
- $\kappa = -\infty$：有理或直纹曲面
- $\kappa = 0$：K3、Enriques、Abel、双椭圆曲面
- $\kappa = 1$：椭圆曲面
- $\kappa = 2$：一般型曲面

### (b) 分类详述

**$\kappa = -\infty$：**

$\mathbb{P}^2$，$\mathbb{P}^1$-丛。

**$\kappa = 0$：**

- K3：$K \sim 0$，$q = 0$
- Enriques：$2K \sim 0$，$K \not\sim 0$
- Abel：$S = \mathbb{C}^2/\Lambda$
- 双椭圆：$S = (E \times F)/G$

**$\kappa = 1$：**

椭圆纤维化，一般纤维椭圆曲线。

**$\kappa = 2$：**

$K^2 > 0$，$\varphi_{nK}$ 对 $n$ 大是双有理嵌入。

### (c) Castelnuovo判据

**证明概要：**

**($\Rightarrow$)**：有理曲面 $">\mathbb{P}^2$ 或Hirzebruch曲面，计算不变量。

**($\Leftarrow$)**：设 $P_2 = q = 0$。

由Noether公式和Riemann-Roch，$\chi(\mathcal{O}) = 1$。

$|nK| = \emptyset$ 对所有 $n \geq 1$，故 $\kappa = -\infty$。

若直纹，由 $q = 0$ 是有理直纹，故有理。
