---
习题编号: TOP-057
学科: 拓扑
知识点: 代数拓扑-Lefschetz不动点
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Lefschetz不动点定理

## 题目

设 $X$ 是有限CW复形，$f: X \to X$ 是连续映射。

**(a) Lefschetz数**：
$$\Lambda(f) = \sum_{k \geq 0} (-1)^k \text{tr}(f_*: H_k(X; \mathbb{Q}) \to H_k(X; \mathbb{Q}))$$

证明若 $f$ 无不动点，则 $\Lambda(f) = 0$。

**(b)** 设 $f \simeq \text{id}_X$，计算 $\Lambda(f)$。

**(c) 应用**：证明Brouwer不动点定理。

## 解答

### (a) Lefschetz不动点定理

**证明概要**：

**胞腔逼近**：$f$ 同伦于胞腔映射。

**Lefschetz数的局部计算**：

若 $f$ 无不动点，可构造链映射的迹为零。

用Hopf迹公式：
$$\Lambda(f) = \sum_{\sigma} (-1)^{\dim \sigma} \text{tr}(f_\#: \mathbb{Z}\sigma \to \mathbb{Z}\sigma)$$

无不动点，迹为零。

因此 $\Lambda(f) = 0$。$\square$

### (b) 同伦于恒等

**计算**：

$f \simeq \text{id}$，则 $f_* = \text{id}$ 于同调。

$$\Lambda(f) = \sum_k (-1)^k \dim H_k(X; \mathbb{Q}) = \chi(X)$$

Euler示性数。

**推论**：若 $\chi(X) \neq 0$，则任何与恒等同伦的映射有不动点。$\square$

### (c) Brouwer不动点定理

**证明**：

$D^n$ 是有限CW复形，$\chi(D^n) = 1 \neq 0$。

设 $f: D^n \to D^n$ 连续。

若 $f$ 无不动点，考虑边界限制。

或用：$D^n$ 可缩，$H_k(D^n) = 0$（$k>0$）。

$\Lambda(f) = \text{tr}(f_*: H_0 \to H_0) = 1 \neq 0$。

因此 $f$ 有不动点。$\square$

## 证明技巧

1. **Hopf迹公式**：同调与链复形的联系
2. **胞腔逼近**：计算的简化
3. **Euler示性数**：拓扑不变量的应用

## 常见错误

- ❌ 忘记有理系数的必要性
- ❌ 不动点与周期点的混淆
- ❌ 反例构造中的边界条件

## 变式练习

**变式1：** 证明紧Lie群的Euler示性数为0（若非平凡）。

**变式2：** 计算Torus上映射的Lefschetz数。
