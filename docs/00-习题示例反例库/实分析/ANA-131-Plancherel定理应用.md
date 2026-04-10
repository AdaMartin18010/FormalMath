---
习题编号: ANA-131
学科: 实分析
知识点: Fourier分析-Plancherel定理
难度: ⭐⭐⭐
预计时间: 25分钟
---

# Plancherel定理应用

## 题目

**(a)** 证明Plancherel定理：Fourier变换 $\mathcal{F}: L^1 \cap L^2(\mathbb{R}^n) \to L^2(\mathbb{R}^n)$ 可延拓为酉算子，即
$$\|\hat{f}\|_{L^2} = \|f\|_{L^2}$$

**(b)** 用Plancherel定理证明Heisenberg不确定性原理：对 $f \in \mathcal{S}(\mathbb{R})$，$\|f\|_{L^2} = 1$：
$$\left(\int x^2 |f(x)|^2 dx\right)^{1/2} \left(\int \xi^2 |\hat{f}(\xi)|^2 d\xi\right)^{1/2} \geq \frac{1}{4\pi}$$

**(c)** 计算 $\int_{-\infty}^{\infty} \frac{\sin^2 x}{x^2} dx$。

## 解答

### (a) Plancherel定理

**证明：**

对 $f, g \in \mathcal{S}(\mathbb{R}^n)$：
$$\int \hat{f}(\xi) \overline{\hat{g}(\xi)} d\xi = \int\int f(x) e^{-2\pi i x \cdot \xi} \overline{\hat{g}(\xi)} dx d\xi$$

$$= \int f(x) \overline{\int \hat{g}(\xi) e^{2\pi i x \cdot \xi} d\xi} dx = \int f(x) \overline{g(x)} dx$$

取 $f = g$ 得 $\|\hat{f}\|_2 = \|f\|_2$ 对Schwartz函数。

由 $\mathcal{S}$ 在 $L^2$ 中稠密，延拓为酉算子。$\square$

### (b) Heisenberg不确定性原理

**证明：**

由 $\|f\|_2 = 1$，$\int |f|^2 = 1$。

设 $A = \int x^2 |f|^2$，$B = \int \xi^2 |\hat{f}|^2$。

由Plancherel：$B = \frac{1}{4\pi^2} \int |f'|^2$。

由分部积分（边界项消失）：
$$1 = \int |f|^2 = -\int x (|f|^2)' = -2\text{Re}\int x f \bar{f'}$$

由Cauchy-Schwarz：
$$1 \leq 2 \left(\int x^2 |f|^2\right)^{1/2} \left(\int |f'|^2\right)^{1/2} = 2 \sqrt{A} \cdot 2\pi \sqrt{B}$$

因此 $\sqrt{AB} \geq \frac{1}{4\pi}$。$\square$

### (c) sinc函数积分

**解答：**

设 $f(x) = \chi_{[-1,1]}(x)$，则
$$\hat{f}(\xi) = \int_{-1}^{1} e^{-2\pi i x \xi} dx = \frac{\sin(2\pi \xi)}{\pi \xi}$$

由Plancherel：
$$\int_{-\infty}^{\infty} \left(\frac{\sin(2\pi \xi)}{\pi \xi}\right)^2 d\xi = \int_{-1}^{1} 1 dx = 2$$

换元 $x = 2\pi \xi$：
$$\int_{-\infty}^{\infty} \frac{\sin^2 x}{(x/2)^2} \frac{dx}{2\pi} = 2$$

$$\frac{2}{\pi} \int_{-\infty}^{\infty} \frac{\sin^2 x}{x^2} dx = 2$$

因此 $\int_{-\infty}^{\infty} \frac{\sin^2 x}{x^2} dx = \pi$。$\square$
