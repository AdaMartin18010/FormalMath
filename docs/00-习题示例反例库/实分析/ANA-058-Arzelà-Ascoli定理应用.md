---
number: "ANA-058"
category: 实分析
topic: 一致收敛应用
difficulty: ⭐⭐⭐⭐
title: Arzelà-Ascoli紧致性定理
msc_primary: 00A99
keywords: [Arzelà-Ascoli, 等度连续, 一致有界, 紧致性, 子列收敛]
prerequisites: [ANA-057, ANA-033]
source: 经典分析习题
---

## 题目

**Arzelà-Ascoli定理：** 设 $K$ 是紧致度量空间，$\mathcal{F} \subset C(K)$ 满足：
- **一致有界：** 存在 $M$ 使得 $|f(x)| \leq M$ 对所有 $f \in \mathcal{F}, x \in K$
- **等度连续：** 对任意 $\varepsilon > 0$，存在 $\delta > 0$ 使得 $d(x,y) < \delta$ 时 $|f(x) - f(y)| < \varepsilon$ 对所有 $f \in \mathcal{F}$

则 $\mathcal{F}$ 中任意序列有在 $C(K)$ 中一致收敛的子列。

**(a)** 证明：若 $f_n: [0,1] \to \mathbb{R}$ 一致有界且 $|f_n'(x)| \leq M$ 对所有 $n, x$，则 $\{f_n\}$ 有一致收敛子列。

**(b)** 构造反例说明：去掉"一致有界"条件，定理不成立。

**(c)** 构造反例说明：去掉"等度连续"条件，定理不成立。

**(d)** 证明：$\{f_n(x) = \sin(nx)\}$ 在 $[0,1]$ 上无一致收敛子列。

## 详细解答

### (a) Lipschitz条件下的紧致性

**证明：**

验证Arzelà-Ascoli的两个条件。

**一致有界：** 已知条件。

**等度连续性：** 由中值定理，对任意 $x, y \in [0,1]$：
$$|f_n(x) - f_n(y)| = |f_n'(\xi)| \cdot |x - y| \leq M|x - y|$$

给定 $\varepsilon > 0$，取 $\delta = \frac{\varepsilon}{M}$，则 $|x - y| < \delta$ 时：
$$|f_n(x) - f_n(y)| < \varepsilon$$

这对所有 $n$ 同时成立，故等度连续。

由Arzelà-Ascoli定理，$\{f_n\}$ 有紧致的闭包，即有一致收敛子列。

**证毕。**

### (b) 无界反例

**反例：** $f_n(x) = n$（常数函数）

**验证：**
- 等度连续：常数函数显然等度连续（任意两点函数值差为0）
- 非一致有界：$|f_n(x)| = n \to \infty$
- 无收敛子列：$\|f_n - f_m\|_{\infty} = |n - m| \geq 1$（$n \neq m$），无Cauchy子列

### (c) 非等度连续反例

**反例：** $f_n(x) = x^n$ 在 $[0,1]$ 上

**验证：**
- 一致有界：$|f_n(x)| \leq 1$
- 非等度连续：在 $x=1$ 附近，函数变化剧烈
  
  具体验证：取 $\varepsilon = \frac{1}{2}$，对任意 $\delta > 0$，取 $n$ 大使 $1 - \frac{1}{n} < 1$ 接近1。
  
  $x_n = 1 - \frac{1}{n}$，$y_n = 1$，则 $|x_n - y_n| = \frac{1}{n} < \delta$（$n$ 大时）
  
  但 $f_n(x_n) = (1-\frac{1}{n})^n \to e^{-1}$，$f_n(y_n) = 1$
  
  故 $|f_n(x_n) - f_n(y_n)| \to 1 - e^{-1} > \frac{1}{2}$

- 无一致收敛子列：任何子列逐点收敛到不连续函数，由ANA-056知非一致收敛

### (d) 正弦序列无收敛子列

**证明：**

**方法1：** 验证不满足等度连续

取 $x = 0$，$y_n = \frac{\pi}{2n}$，则 $|0 - y_n| = \frac{\pi}{2n} \to 0$

但 $f_n(0) = 0$，$f_n(y_n) = \sin(\frac{\pi}{2}) = 1$

故 $|f_n(0) - f_n(y_n)| = 1$ 不趋于0，非等度连续。

**方法2：** 直接验证无收敛子列

假设 $f_{n_k} \to f$ 一致收敛，则 $f$ 连续。

但 $\int_0^1 \sin^2(n_k x) dx = \frac{1}{2} - \frac{\sin(2n_k)}{4n_k} \to \frac{1}{2}$

若一致收敛，则 $\int f_{n_k}^2 \to \int f^2$。

同时 $\int f_{n_k} \cdot f_{n_{k+1}} \to 0$（正交性）。

这导致矛盾，说明无一致收敛子列。

## 证明技巧

1. **等度连续的验证策略：**
   - Lipschitz条件：$|f(x) - f(y)| \leq L|x - y|$
   - 一致连续的函数族（导数一致有界保证）

2. **Arzelà-Ascoli的应用步骤：**
   - 验证一致有界
   - 验证等度连续
   - 得出紧致性结论

3. **构造反例的思路：** 针对性地违反单个条件

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆等度连续与一致连续 | 等度连续要求$\delta$对所有函数同时有效 |
| 忽略定义域紧致性 | 定理要求$K$紧致 |
| 认为逐点有界足够 | 需要一致有界（上界不依赖于$x$） |

## 变式练习

**变式1：** 设 $f_n: [0,1] \to \mathbb{R}$ 满足 $|f_n(x) - f_n(y)| \leq L|x - y|^{\alpha}$（Hölder连续），且一致有界，证明有收敛子列。

**变式2：** 证明 $C(K)$ 中的子集是紧致的当且仅当闭、有界、等度连续。

**变式3：** 用Arzelà-Ascoli证明Peano存在定理（ODE解的存在性）。
