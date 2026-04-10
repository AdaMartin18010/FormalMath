---
习题编号: ANA-120
学科: 实分析
知识点: 分布理论-Sobolev空间嵌入
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Sobolev空间嵌入定理

## 题目

设 $\Omega \subset \mathbb{R}^n$ 是有界光滑区域，Sobolev空间 $W^{k,p}(\Omega)$ 定义为：
$$W^{k,p}(\Omega) = \{f \in L^p(\Omega) : D^\alpha f \in L^p(\Omega), |\alpha| \leq k\}$$
配备范数 $\|f\|_{W^{k,p}} = \sum_{|\alpha| \leq k} \|D^\alpha f\|_{L^p}$。

**(a)** 证明Sobolev嵌入：若 $kp < n$，则
$$W^{k,p}(\mathbb{R}^n) \hookrightarrow L^q(\mathbb{R}^n), \quad \frac{1}{q} = \frac{1}{p} - \frac{k}{n}$$

**(b)** 证明Morrey嵌入：若 $kp > n$，则
$$W^{k,p}(\mathbb{R}^n) \hookrightarrow C^{0,\gamma}(\mathbb{R}^n), \quad \gamma = k - \frac{n}{p}$$

**(c)** 设 $n=3$，$p=2$，证明 $H^2(\mathbb{R}^3) \hookrightarrow C^{0,1/2}(\mathbb{R}^3)$。

## 解答

### (a) Sobolev嵌入（$kp < n$ 情形）

**证明概要：**

**Step 1**：只需证 $k=1$ 情形，然后用归纳法。

**Step 2**：Gagliardo-Nirenberg-Sobolev不等式。

对 $f \in C_c^\infty(\mathbb{R}^n)$，$1 \leq p < n$：
$$\|f\|_{L^{p^*}} \leq C \|\nabla f\|_{L^p}, \quad \frac{1}{p^*} = \frac{1}{p} - \frac{1}{n}$$

**Step 3**：证明GNS不等式。

对 $x = (x_1, \bar{x})$，$\bar{x} = (x_2, \ldots, x_n)$：
$$|f(x)| \leq \int_{-\infty}^{\infty} |\partial_1 f(t, \bar{x})| dt$$

对每个坐标方向类似：
$$|f(x)|^{n/(n-1)} \leq \prod_{i=1}^n \left( \int_{-\infty}^{\infty} |\partial_i f(x_1, \ldots, t, \ldots, x_n)| dt \right)^{1/(n-1)}$$

积分并对称化处理，用广义Hölder不等式得：
$$\|f\|_{L^{n/(n-1)}} \leq \prod_{i=1}^n \|\partial_i f\|_{L^1}^{1/n} \leq C \|\nabla f\|_{L^1}$$

对一般 $p$，用 $f = |g|^r$ 代入，适当选取 $r$。

**Step 4**：稠密性论证。

$C_c^\infty$ 在 $W^{1,p}$ 中稠密，不等式可延拓。$\square$

### (b) Morrey嵌入（$kp > n$ 情形）

**证明概要：**

**Step 1**：同样只需证 $k=1$。

**Step 2**：建立表示公式。

对 $f \in C^1$，球 $B = B(x,r)$：
$$f(x) = \frac{1}{|B|} \int_B f(y) dy + \frac{1}{|B|} \int_B (f(x) - f(y)) dy$$

**Step 3**：估计差分。

$$|f(x) - f(y)| \leq C \int_{B(x, 2|x-y|)} \frac{|\nabla f(z)|}{|z-x|^{n-1}} dz$$

这是Poincaré不等式的变形。

**Step 4**：Hölder估计。

由 $p > n$，用Hölder：
$$|f(x) - f(y)| \leq C |x-y|^{1-n/p} \|\nabla f\|_{L^p}$$

因此 $\gamma = 1 - n/p$。$\square$

### (c) 具体嵌入

**证明：**

$n=3$，$p=2$，$k=2$。

$kp = 4 > 3 = n$，满足Morrey嵌入条件。

$$\gamma = k - \frac{n}{p} = 2 - \frac{3}{2} = \frac{1}{2}$$

由(b)：$H^2(\mathbb{R}^3) = W^{2,2}(\mathbb{R}^3) \hookrightarrow C^{0,1/2}(\mathbb{R}^3)$。$\square$

## 证明技巧

1. **Gagliardo-Nirenberg技巧**：多变量积分表示
2. **尺度分析**：嵌入指标的可加性验证
3. **临界情形**：$kp = n$ 时需精细处理（BMO等）

## 常见错误

- ❌ 嵌入条件与维数关系混淆
- ❌ GNS不等式证明中的指数计算错误
- ❌ 紧嵌入与连续嵌入的区分不清

## 变式练习

**变式1：** 证明Rellich-Kondrachov紧嵌入定理。

**变式2：** 讨论 $kp = n$ 时的临界Sobolev嵌入。
