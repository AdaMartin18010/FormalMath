---
习题编号: TOP-060
学科: 拓扑
知识点: 示性类-Chern类
难度: ⭐⭐⭐⭐⭐
预计时间: 40分钟
---

# Chern类

## 题目

设 $E \to B$ 是复向量丛，秩 $n$。

**(a)** 定义Chern类 $c_i(E) \in H^{2i}(B; \mathbb{Z})$，$c_0 = 1$，$c_i = 0$（$i>n$）。

**(b)** 证明公理并计算 $c(T\mathbb{C}P^n)$。

**(c)** 证明分裂原理：复丛的示性类计算可化到线丛直和。

## 解答

### (a) Chern类的定义

**构造**：

用Euler类或曲率（微分几何）。

拓扑构造：$c(E) = 1 + c_1(E) + c_2(E) + \cdots \in H^{2*}(B; \mathbb{Z})$。

通过分类空间 $BU(n)$。

$H^*(BU(n); \mathbb{Z}) = \mathbb{Z}[c_1, \ldots, c_n]$，$|c_i| = 2i$。

$c_i(E) = f_E^*(c_i)$，$f_E: B \to BU(n)$ 分类映射。$\square$

### (b) 切丛的Chern类

**公式**：

$0 \to \gamma^1 \to \epsilon^{n+1} \to Q \to 0$ 于 $\mathbb{C}P^n$。

$Q = T\mathbb{C}P^n \otimes (\gamma^1)^*$。

$c(\gamma^1) = 1 + x$，$x \in H^2(\mathbb{C}P^n)$ 生成元。

$c(Q) = c(\epsilon^{n+1})/c(\gamma^1) = (1+x)^{n+1}/(1+x) = (1+x)^n$。

$c(T\mathbb{C}P^n) = c(Q \otimes \gamma^1) = c(Q) \cdot c(\gamma^1)^n = (1+x)^{n+1}$。

即：$c_i(T\mathbb{C}P^n) = \binom{n+1}{i} x^i$。$\square$

### (c) 分裂原理

**定理**：

对复丛 $E \to B$，存在 $f: B' \to B$ 使得：
(i) $f^*E = L_1 \oplus \cdots \oplus L_n$（线丛）；
(ii) $f^*: H^*(B) \to H^*(B')$ 单射。

**证明**：

归纳于秩。

射影丛构造：$\mathbb{P}(E) = \{(b, \ell) : \ell \subset E_b \text{ 直线}\}$。

$\pi: \mathbb{P}(E) \to B$，拉回 $\pi^*E$ 有tautological子丛 $S$。

$\pi^*E/S$ 秩降低。

重复得到完全标志丛。

$H^*(\mathbb{F}(E))$ 作为 $H^*(B)$-模自由，故 $\pi^*$ 单射。$\square$

## 证明技巧

1. **分类空间**：示性类的万能构造
2. **正合列的Chern类**：Whitney和公理
3. **射影丛的迭代**：分裂的几何实现

## 常见错误

- ❌ 忘记Chern类的偶数维数
- ❌ 射影丛与对偶丛的混淆
- ❌ 分裂原理的单射方向

## 变式练习

**变式1：** 用Chern类证明复流形的Hirzebruch符号差定理。

**变式2：** 计算 $c(E \otimes F)$ 的分裂公式。
