---
msc_primary: 00A99
习题编号: TOP-076
学科: 拓扑
知识点: 同伦论-广义上同调谱序列
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Atiyah-Hirzebruch谱序列

## 题目

设 $h^*$ 是广义上同调理论。

**(a)** 陈述Atiyah-Hirzebruch谱序列：对CW复形 $X$，
$$E_2^{p,q} = H^p(X; h^q(\text{pt})) \Rightarrow h^{p+q}(X)$$

**(b)** 计算 $K^*(\mathbb{C}P^n)$（复K理论）。

**(c)** 讨论AHSS的微分与Steenrod运算的关系。

## 解答

### (a) AHSS陈述

**构造：**

由 $X$ 的骨架滤过 $X^{(0)} \subset X^{(1)} \subset \cdots$。

正合对 $(D, E)$，$D = \bigoplus h^*(X^{(p)})$，$E = \bigoplus h^*(X^{(p)}, X^{(p-1)})$。

$E_1^{p,q} = h^{p+q}(X^{(p)}, X^{(p-1)}) \cong C^p(X; h^q(\text{pt}))$。

$d_1$ 是胞腔上边缘，故 $E_2^{p,q} = H^p(X; h^q(\text{pt}))$。

### (b) 复射影空间的K理论

**计算：**

$h^0(\text{pt}) = \mathbb{Z}$，$h^1(\text{pt}) = 0$（复K理论）。

$E_2^{p,q} = H^p(\mathbb{C}P^n; \mathbb{Z})$ 对 $q$ 偶，0对 $q$ 奇。

$H^*(\mathbb{C}P^n) = \mathbb{Z}[x]/(x^{n+1})$，$|x| = 2$。

微分 $d_{2r+1} = 0$（奇数页）。

$d_2$ 由Atiyah-Hirzebruch公式，此处为0。

故谱序列退化，$K^0(\mathbb{C}P^n) = \mathbb{Z}^{n+1}$。

实际上 $K^0(\mathbb{C}P^n) = \mathbb{Z}[\xi]/((\xi-1)^{n+1})$。

### (c) 微分与Steenrod运算

**关系：**

对通常上同调 $h^* = H^*$，AHSS退化。

对拓扑K理论，$d_3$ 与 $Sq^3$ 有关。

一般：微分由Postnikov塔的 $k$-不变量决定。
