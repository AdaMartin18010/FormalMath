---
习题编号: ANA-101
学科: 实分析
知识点: 积分论-Lebesgue控制收敛定理
难度: ⭐⭐⭐
预计时间: 20分钟
---

# Lebesgue控制收敛定理

## 题目

**Lebesgue控制收敛定理（DCT）**：设 $\{f_n\}$ 是可测函数列，$f_n \to f$ a.e.，且存在可积函数 $g$ 使得 $|f_n| \leq g$ a.e. 对所有 $n$。则：
$$\lim_{n\to\infty} \int f_n = \int \lim_{n\to\infty} f_n = \int f$$

(a) 证明DCT。

(b) 计算 $\displaystyle\lim_{n\to\infty} \int_0^1 \frac{n\sin(x/n)}{x} dx$。

(c) 举例说明控制函数的条件不可去掉。

## 解答

### (a) DCT的证明

**证明：**

**Step 1**：由 $|f_n| \leq g$，得 $|f| \leq g$ a.e.，故 $f$ 可积。

**Step 2**：考虑 $g + f_n \geq 0$ 和 $g - f_n \geq 0$。

由Fatou引理：
$$\int \liminf (g + f_n) \leq \liminf \int (g + f_n)$$

即：
$$\int g + \int f \leq \int g + \liminf \int f_n$$

故 $\displaystyle\int f \leq \liminf \int f_n$。

**Step 3**：对 $g - f_n$ 应用Fatou引理：
$$\int g - \int f \leq \liminf \int (g - f_n) = \int g - \limsup \int f_n$$

故 $\displaystyle\limsup \int f_n \leq \int f$。

**Step 4**：结合得：
$$\limsup \int f_n \leq \int f \leq \liminf \int f_n$$

因此极限存在且等于 $\int f$。$\square$

### (b) 极限计算

**解答：**

令 $f_n(x) = \frac{n\sin(x/n)}{x}$。

当 $n \to \infty$，$\frac{\sin(x/n)}{x/n} \to 1$，故 $f_n(x) \to 1$。

控制函数：对 $t > 0$，$|\frac{\sin t}{t}| \leq 1$，故 $|f_n(x)| \leq 1$。

由DCT：
$$\lim_{n\to\infty} \int_0^1 f_n(x) dx = \int_0^1 1 \cdot dx = 1$$
$\square$

### (c) 反例

**例子**：

设 $f_n = n \cdot \mathbf{1}_{(0,1/n)}$ 于 $[0,1]$。

则 $f_n \to 0$ a.e.（在 $x=0$ 外都趋于0）。

但 $\displaystyle\int_0^1 f_n = n \cdot \frac{1}{n} = 1 \not\to 0$。

**分析**：

控制函数需满足 $g \geq n$ 于 $(0, 1/n)$，故 $g$ 在0附近无界。

不存在可积的控制函数。$\square$

## 证明技巧

1. **Fatou引理双向应用**：得到上下界
2. **非负化**：$g \pm f_n$ 的技巧
3. **极限上/下确界**：控制极限存在性

## 常见错误

- ❌ 忘记验证 $f_n \to f$ a.e.
- ❌ 控制函数依赖 $n$
- ❌ 在(b)中错误估计收敛速度

## 变式练习

**变式1：** 计算 $\displaystyle\lim_{n\to\infty} \int_0^n \left(1+\frac{x}{n}\right)^n e^{-2x} dx$。

**变式2：** 证明 $f \in L^1$ 时，$\sum_{n=1}^\infty f(nx)$ 对 a.e. $x$ 收敛。
