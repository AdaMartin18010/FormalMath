---
number: "ANA-059"
category: 实分析
topic: 一致收敛应用
difficulty: ⭐⭐⭐
title: Stone-Weierstrass逼近定理
keywords: [Stone-Weierstrass, 多项式逼近, 代数, 分离点, 一致稠密]
prerequisites: [ANA-058, ANA-034]
source: 经典分析习题
---

## 题目

**Stone-Weierstrass定理（实版本）：** 设 $K$ 是紧致Hausdorff空间，$\mathcal{A} \subset C(K, \mathbb{R})$ 是子代数（对加、乘、数乘封闭），满足：
- **分离点：** 对任意 $x \neq y$，存在 $f \in \mathcal{A}$ 使 $f(x) \neq f(y)$
- **含常数：** $1 \in \mathcal{A}$

则 $\mathcal{A}$ 在 $C(K)$ 中一致稠密。

**(a)** 用Stone-Weierstrass定理证明Weierstrass逼近定理：$[a,b]$ 上的连续函数可用多项式一致逼近。

**(b)** 证明 $C([0,1] \times [0,1])$ 中的函数可用形如 $\sum_{i=1}^n f_i(x)g_i(y)$ 的函数一致逼近。

**(c)** 设 $K = \{z \in \mathbb{C} : |z| = 1\}$（单位圆），$\mathcal{A}$ 是三角多项式 $\sum_{k=-n}^n c_k e^{ik\theta}$ 的集合。证明 $\mathcal{A}$ 在 $C(K)$ 中稠密。

**(d)** 构造反例说明：去掉"分离点"条件，定理不成立。

## 详细解答

### (a) Weierstrass逼近定理

**证明：**

设 $K = [a,b]$，$\mathcal{A} = \{\text{多项式函数}\}$。

验证Stone-Weierstrass条件：

**子代数：** 多项式对加、乘、数乘封闭。

**含常数：** 常数多项式在 $\mathcal{A}$ 中。

**分离点：** 取 $f(x) = x$（一次多项式），则 $f(x) \neq f(y)$ 当 $x \neq y$。

由Stone-Weierstrass定理，$\mathcal{A}$ 在 $C([a,b])$ 中一致稠密。

即 $[a,b]$ 上的连续函数可用多项式一致逼近。

**证毕。**

### (b) 二元函数的逼近

**证明：**

设 $K = [0,1] \times [0,1]$，$\mathcal{A} = \left\{\sum_{i=1}^n f_i(x)g_i(y) : f_i, g_i \text{ 多项式}\right\}$。

**子代数验证：**
- $(f_1(x)g_1(y)) \cdot (f_2(x)g_2(y)) = (f_1f_2)(x) \cdot (g_1g_2)(y) \in \mathcal{A}$
- 其他运算类似封闭

**含常数：** $1 = 1 \cdot 1 \in \mathcal{A}$。

**分离点：** 设 $(x_1, y_1) \neq (x_2, y_2)$。

- 若 $x_1 \neq x_2$，取 $f(x) = x$，$g(y) = 1$，则 $f(x_1)g(y_1) = x_1 \neq x_2 = f(x_2)g(y_2)$
- 若 $y_1 \neq y_2$，类似处理

由Stone-Weierstrass定理，$\mathcal{A}$ 一致稠密。

**证毕。**

### (c) 单位圆上的三角多项式

**证明：**

设 $K = \{e^{i\theta} : \theta \in [0, 2\pi]\}$，$\mathcal{A}$ 是三角多项式集合。

**子代数：** 注意 $e^{ik\theta} \cdot e^{il\theta} = e^{i(k+l)\theta}$，封闭。

**含常数：** $e^{i0\theta} = 1 \in \mathcal{A}$。

**分离点：** 设 $e^{i\theta_1} \neq e^{i\theta_2}$，取 $f(e^{i\theta}) = e^{i\theta}$，则：
$$f(e^{i\theta_1}) = e^{i\theta_1} \neq e^{i\theta_2} = f(e^{i\theta_2})$$

由Stone-Weierstrass定理，$\mathcal{A}$ 稠密。

**注：** 这就是Fourier分析中三角多项式稠密性的结论。

**证毕。**

### (d) 分离点条件的必要性

**反例：** 设 $K = [0,1]$，$\mathcal{A} = \{\text{常数函数}\}$。

**验证：**
- 子代数：常数函数对运算封闭
- 含常数：满足
- 不分离点：对任意 $x \neq y$，$f(x) = f(y)$ 对所有 $f \in \mathcal{A}$

$\mathcal{A}$ 的闭包就是 $\mathcal{A}$ 本身（已闭），不等于 $C([0,1])$。

例如 $f(x) = x$ 不能用常数一致逼近：$\|x - c\|_{\infty} \geq \frac{1}{2}$ 对所有常数 $c$。

## 证明技巧

1. **应用Stone-Weierstrass的模板：**
   - 明确函数代数 $\mathcal{A}$
   - 逐一验证三个条件
   - 得出稠密性结论

2. **分离点的验证策略：**
   - 坐标函数通常能分离点
   - 考虑乘积空间的分量函数

3. **复版本注意：** Stone-Weierstrass复版本需要额外条件（对共轭封闭）

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆代数与向量空间 | 代数需要对乘法封闭 |
| 复函数忘记共轭条件 | 复版本需额外假设 |
| 验证分离点时选错函数 | 函数必须在代数中 |

## 变式练习

**变式1：** 证明 $[0,1]$ 上的连续函数可用分段线性函数一致逼近。

**变式2：** 设 $K \subset \mathbb{R}^n$ 紧致，证明坐标多项式在 $C(K)$ 中稠密。

**变式3：** 证明复Stone-Weierstrass定理：若 $\mathcal{A}$ 还满足 $f \in \mathcal{A} \Rightarrow \bar{f} \in \mathcal{A}$，则复版本成立。
