---
msc_primary: 00A99
习题编号: ANA-117
学科: 实分析
知识点: Fourier分析-变换性质
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Fourier变换性质

## 题目

设 $f \in L^1(\mathbb{R})$，定义其Fourier变换为：
$$\hat{f}(\xi) = \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx$$

**(a)** 证明：若 $f \in L^1(\mathbb{R}) \cap C^1(\mathbb{R})$ 且 $f' \in L^1(\mathbb{R})$，则
$$\widehat{f'}(\xi) = 2\pi i \xi \cdot \hat{f}(\xi)$$

**(b)** 设 $g(x) = xf(x)$，证明：若 $g \in L^1(\mathbb{R})$，则 $\hat{f}$ 可微且
$$\frac{d}{d\xi}\hat{f}(\xi) = -2\pi i \cdot \widehat{xf(x)}(\xi)$$

**(c)** 计算Gauss函数 $f(x) = e^{-\pi x^2}$ 的Fourier变换。

## 解答

### (a) 导数的Fourier变换

**证明：**

分部积分：
$$\widehat{f'}(\xi) = \int_{-\infty}^{\infty} f'(x) e^{-2\pi i x \xi} dx$$

$$= \left[ f(x) e^{-2\pi i x \xi} \right]_{-\infty}^{\infty} - \int_{-\infty}^{\infty} f(x) (-2\pi i \xi) e^{-2\pi i x \xi} dx$$

由 $f \in L^1$ 和 $f'$ 存在，$f(x) \to 0$ 当 $|x| \to \infty$（因为 $f(x) = f(0) + \int_0^x f'(t)dt$，且 $f' \in L^1$ 保证极限存在，$f \in L^1$ 要求极限为0）。

因此边界项为0：
$$\widehat{f'}(\xi) = 2\pi i \xi \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx = 2\pi i \xi \cdot \hat{f}(\xi)$$
$\square$

### (b) 乘积的Fourier变换

**证明：**

形式计算：
$$\frac{d}{d\xi}\hat{f}(\xi) = \frac{d}{d\xi} \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx$$

交换导数与积分（需验证条件）：
$$= \int_{-\infty}^{\infty} f(x) (-2\pi i x) e^{-2\pi i x \xi} dx = -2\pi i \int_{-\infty}^{\infty} xf(x) e^{-2\pi i x \xi} dx$$

$$= -2\pi i \cdot \widehat{xf(x)}(\xi)$$

**验证交换合法性**：
由 $xf(x) \in L^1$，被积函数对$\xi$的偏导数 $|xf(x) \cdot (-2\pi i x)e^{-2\pi i x\xi}| = 2\pi |xf(x)|$ 可积，故可用控制收敛定理。$\square$

### (c) Gauss函数的Fourier变换

**解答：**

设 $f(x) = e^{-\pi x^2}$，则 $\hat{f}(\xi) = \int_{-\infty}^{\infty} e^{-\pi x^2 - 2\pi i x \xi} dx$

配方：
$$-\pi x^2 - 2\pi i x \xi = -\pi(x^2 + 2ix\xi) = -\pi(x + i\xi)^2 - \pi \xi^2$$

因此：
$$\hat{f}(\xi) = e^{-\pi \xi^2} \int_{-\infty}^{\infty} e^{-\pi(x+i\xi)^2} dx$$

**围道积分**：考虑矩形围道 $\gamma_R$ 顶点在 $\pm R$ 和 $\pm R + i\xi$。

$e^{-\pi z^2}$ 全纯，故：
$$\oint_{\gamma_R} e^{-\pi z^2} dz = 0$$

垂直边当 $R \to \infty$ 时趋于0（因 $|e^{-\pi(R+iy)^2}| = e^{-\pi R^2 + \pi y^2} \to 0$）。

因此：
$$\int_{-\infty}^{\infty} e^{-\pi(x+i\xi)^2} dx = \int_{-\infty}^{\infty} e^{-\pi x^2} dx = 1$$

故 $\hat{f}(\xi) = e^{-\pi \xi^2} = f(\xi)$。

Gauss函数是Fourier变换的本征函数！$\square$

## 证明技巧

1. **分部积分**：将微分转化为乘法
2. **控制收敛**：积分与微分交换的理论基础
3. **围道积分**：计算特殊函数变换的有力工具

## 常见错误

- ❌ 忽略边界项在无穷远处的衰减条件
- ❌ 积分与微分交换时未验证控制条件
- ❌ 围道积分中垂直边的估计错误

## 变式练习

**变式1：** 证明 $\widehat{f * g} = \hat{f} \cdot \hat{g}$（卷积定理）。

**变式2：** 计算 $f(x) = e^{-a|x|}$（$a > 0$）的Fourier变换。
