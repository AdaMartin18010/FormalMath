---
习题编号: TOP-074
学科: 拓扑
知识点: 同伦论-Postnikov塔
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Postnikov塔

## 题目

**(a)** 定义Postnikov塔：空间序列 $\cdots \to X_n \to X_{n-1} \to \cdots \to X_1$，其中
- $X_n \to X_{n-1}$ 是纤维化，纤维 $K(\pi_n(X), n)$
- $\pi_i(X_n) = 0$ 对 $i > n$
- $X \to X_n$ 诱导同构 $\pi_i(X) \cong \pi_i(X_n)$ 对 $i \leq n$

**(b)** 证明任意道路连通CW复形有Postnikov塔。

**(c)** 用Postnikov塔计算 $[X, K(\pi, n)]$。

## 解答

### (a) Postnikov塔定义

**构造：**

通过逐次附着高维胞腔杀死高阶同伦群。

$X_n$ 有万有性质：从 $X$ 到 $n$-截断空间的映射。

### (b) 存在性证明

**证明概要：**

对CW复形 $X$，归纳构造 $X_n$。

$X_1 = K(\pi_1(X), 1)$。

假设 $X_{n-1}$ 已构造，$k$-不变量 $k_n \in H^{n+1}(X_{n-1}; \pi_n(X))$。

$X_n$ 为 $k_n$ 的homotopy fiber。

### (c) Eilenberg-MacLane空间的映射

**解答：**

$$[X, K(\pi, n)] \cong H^n(X; \pi)$$

由Hurewicz定理和万有系数：

$K(\pi, n)$ 是 $(n-1)$-连通，$H_n(K(\pi, n)) = \pi$。

映射的同伦类由诱导的上同调类决定。
