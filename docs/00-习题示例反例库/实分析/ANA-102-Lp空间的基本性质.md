---
msc_primary: 00A99
习题编号: ANA-102
学科: 实分析
知识点: 函数空间-Lp空间
难度: ⭐⭐⭐
预计时间: 25分钟
---

# L^p空间的基本性质

## 题目

设 $(X, \mathcal{M}, \mu)$ 是测度空间，$1 \leq p < \infty$。
$$L^p(X) = \left\{f: \|f\|_p = \left(\int_X |f|^p d\mu\right)^{1/p} < \infty\right\}$$

(a) 证明Hölder不等式：若 $\frac{1}{p} + \frac{1}{q} = 1$，则：
$$\|fg\|_1 \leq \|f\|_p \|g\|_q$$

(b) 证明Minkowski不等式：
$$\|f + g\|_p \leq \|f\|_p + \|g\|_p$$

(c) 证明简单函数在 $L^p$ 中稠密（当 $X = \mathbb{R}^n$，Lebesgue测度）。

## 解答

### (a) Hölder不等式

**证明：**

**Step 1**：Young不等式。

对 $a, b > 0$：
$$ab \leq \frac{a^p}{p} + \frac{b^q}{q}$$

由 $\ln$ 的凹性，或AM-GM不等式可得。

**Step 2**：归一化。

设 $\|f\|_p = \|g\|_q = 1$（一般情形用齐次性）。

令 $a = |f(x)|$，$b = |g(x)|$：
$$|f(x)g(x)| \leq \frac{|f(x)|^p}{p} + \frac{|g(x)|^q}{q}$$

**Step 3**：积分：
$$\int |fg| \leq \frac{1}{p}\int|f|^p + \frac{1}{q}\int|g|^q = \frac{1}{p} + \frac{1}{q} = 1$$

$\square$

### (b) Minkowski不等式

**证明：**

$$|f + g|^p \leq |f + g|^{p-1}(|f| + |g|)$$

令 $h = |f + g|^{p-1}$，则 $h \in L^q$（因 $q(p-1) = p$）。

$$\int |f + g|^p \leq \int |f| \cdot h + \int |g| \cdot h$$

由Hölder：
$$\leq \|f\|_p \|h\|_q + \|g\|_p \|h\|_q = (\|f\|_p + \|g\|_p) \||f+g|^{p-1}\|_q$$

$$= (\|f\|_p + \|g\|_p) \|f + g\|_p^{p/q}$$

若 $\|f + g\|_p > 0$，两边除以 $\|f + g\|_p^{p/q} = \|f+g\|_p^{p-1}$，得证。$\square$

### (c) 简单函数稠密性

**证明：**

设 $f \in L^p(\mathbb{R}^n)$，$f \geq 0$。

**Step 1**：用截断逼近。

令 $f_N = f \cdot \mathbf{1}_{\{|f| \leq N\}} \cdot \mathbf{1}_{B_N(0)}$。

由DCT，$\|f - f_N\|_p \to 0$。

**Step 2**：$f_N$ 有界支集且有界，可用简单函数一致逼近。

对可测集 $E$，$\mu(E) < \infty$，特征函数 $\mathbf{1}_E \in L^p$。

由可测集的定义，$E$ 可用方体（或区间）逼近。$\square$

## 证明技巧

1. **Young不等式**：Hölder的核心
2. **对偶性**：利用 $L^p$ 与 $L^q$ 的关系
3. **截断+逼近**：稠密性证明的标准套路

## 常见错误

- ❌ 在(a)中忘记归一化步骤
- ❌ 在(b)中 $p=1$ 情形需单独处理
- ❌ 稠密性证明中未验证 $L^p$ 收敛

## 变式练习

**变式1：** 证明 $L^p \subset L^q$ 当 $\mu(X) < \infty$ 且 $p > q$。

**变式2：** 证明 $(L^p)^* \cong L^q$（对 $\sigma$-有限测度空间）。
