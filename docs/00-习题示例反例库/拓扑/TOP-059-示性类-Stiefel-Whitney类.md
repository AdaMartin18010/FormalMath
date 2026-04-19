---
msc_primary: 00A99
习题编号: TOP-059
学科: 拓扑
知识点: 示性类-Stiefel-Whitney
难度: ⭐⭐⭐⭐⭐
预计时间: 40分钟
---

# Stiefel-Whitney类

## 题目

设 $E \to B$ 是实向量丛，秩 $n$。

**(a)** 定义Stiefel-Whitney类 $w_i(E) \in H^i(B; \mathbb{Z}/2)$，$w_0 = 1$，$w_i = 0$（$i>n$）。

**(b)** 证明公理：自然性、Whitney和公式、$w(\gamma^1) = 1 + x$（ tautological丛）。

**(c)** 应用：证明 $\mathbb{R}P^n$ 可平行化当且仅当 $n+1 = 2^k$。

## 解答

### (a) SW类的定义

**构造**：

用Euler类或分裂原理。

$w(E) = 1 + w_1(E) + w_2(E) + \cdots \in H^*(B; \mathbb{Z}/2)$。

总SW类。

**分裂原理**：

存在 $f: B' \to B$ 使得 $f^*E$ 分裂为线丛，$f^*$ 单射。

$w(L_1 \oplus \cdots \oplus L_n) = (1+x_1)\cdots(1+x_n)$。$\square$

### (b) 公理

**自然性**：$w(f^*E) = f^*w(E)$。

由构造显然。

**Whitney和**：
$w(E \oplus F) = w(E) \smile w(F)$。

由分裂原理，只需对线丛验证。

**标准丛**：

$\gamma^1 \to \mathbb{R}P^\infty$，$w(\gamma^1) = 1 + x$，$x \in H^1(\mathbb{R}P^\infty)$ 生成元。$\square$

### (c) 平行化条件

**定理**：$\mathbb{R}P^n$ 可平行化 $\Leftrightarrow$ $n+1 = 2^k$。

**证明**：

$\mathbb{R}P^n$ 可平行化 $\Leftrightarrow$ $T\mathbb{R}P^n$ 平凡。

$$T\mathbb{R}P^n \oplus \epsilon^1 = \gamma^1 \oplus \cdots \oplus \gamma^1 \quad (n+1 \text{次})$$

$w(T\mathbb{R}P^n) = (1+x)^{n+1}$。

平凡当且仅当 $(1+x)^{n+1} = 1$ 于 $H^*(\mathbb{R}P^n) = \mathbb{Z}/2[x]/(x^{n+1})$。

$(1+x)^{n+1} = \sum_{i=0}^{n+1} \binom{n+1}{i} x^i$。

$= 1$ 当且仅当 $\binom{n+1}{i}$ 偶对所有 $0 < i \leq n$。

当且仅当 $n+1 = 2^k$（Lucas定理）。$\square$

## 证明技巧

1. **分裂原理**：丛论计算的核心
2. **二项式系数**：模2组合数学
3. **切丛公式**：射影空间的经典计算

## 常见错误

- ❌ 忘记模2系数
- ❌ 分裂原理的逆向应用
- ❌ Lucas定理的条件

## 变式练习

**变式1：** 计算 $w(T\mathbb{C}P^n)$（模2）。

**变式2：** 证明 $\mathbb{C}P^2$ 不可嵌入 $\mathbb{R}^5$。
