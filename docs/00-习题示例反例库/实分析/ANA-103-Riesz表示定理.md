---
msc_primary: 00A99
习题编号: ANA-103
学科: 实分析
知识点: 泛函分析-Riesz表示定理
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# Riesz表示定理

## 题目

**定理**：设 $H$ 是Hilbert空间，$\varphi \in H^*$（连续线性泛函）。则存在唯一的 $y \in H$ 使得：
$$\varphi(x) = \langle x, y \rangle, \quad \forall x \in H$$
且 $\|\varphi\| = \|y\|$。

(a) 证明存在性（可分情形可用正交基，一般情形用闭子空间）。

(b) 证明唯一性和等距性。

(c) 设 $H = L^2[0,1]$，$\varphi(f) = \int_0^1 f(x) \sin(2\pi x) dx$，求表示元 $g$。

## 解答

### (a) 存在性证明

**证明：**

**情形1**：$\varphi = 0$。取 $y = 0$。

**情形2**：$\varphi \neq 0$。

令 $N = \ker(\varphi)$，是闭子空间（因 $\varphi$ 连续）。

由正交分解：$H = N \oplus N^\perp$。

$N^\perp \neq \{0\}$（否则 $N = H$，$\varphi = 0$）。

取 $z \in N^\perp$，$\|z\| = 1$。

**关键观察**：对任意 $x \in H$，$x - \frac{\varphi(x)}{\varphi(z)}z \in N$。

因此与 $z$ 正交：
$$\left\langle x - \frac{\varphi(x)}{\varphi(z)}z, z \right\rangle = 0$$

$$\langle x, z \rangle = \frac{\varphi(x)}{\varphi(z)} \langle z, z \rangle = \frac{\varphi(x)}{\varphi(z)}$$

令 $y = \overline{\varphi(z)} \cdot z$：
$$\varphi(x) = \langle x, y \rangle$$

$\square$

### (b) 唯一性与等距性

**唯一性**：

设 $\langle x, y_1 \rangle = \langle x, y_2 \rangle$ 对所有 $x$。

则 $\langle x, y_1 - y_2 \rangle = 0$，取 $x = y_1 - y_2$，得 $y_1 = y_2$。

**等距性**：

$|\varphi(x)| = |\langle x, y \rangle| \leq \|x\| \|y\|$，故 $\|\varphi\| \leq \|y\|$。

取 $x = y/\|y\|$（若 $y \neq 0$）：
$$\varphi(x) = \frac{\langle y, y \rangle}{\|y\|} = \|y\|$$

故 $\|\varphi\| = \|y\|$。$\square$

### (c) 具体计算

**解答：**

由Riesz表示，$g(x) = \sin(2\pi x)$。

验证：
$$\langle f, g \rangle = \int_0^1 f(x) \sin(2\pi x) dx = \varphi(f)$$

范数：
$$\|\varphi\| = \|g\|_2 = \left(\int_0^1 \sin^2(2\pi x) dx\right)^{1/2} = \frac{1}{\sqrt{2}}$$
$\square$

## 证明技巧

1. **核空间的正交补**：关键的几何观察
2. **构造性证明**：直接给出表示元
3. **等距验证**：双向不等式

## 常见错误

- ❌ 忘记核空间是闭的（需连续性）
- ❌ 在(c)中混淆 $L^2$ 与连续函数空间
- ❌ 复Hilbert空间中忘记共轭

## 变式练习

**变式1：** 设 $H = \ell^2$，$\varphi(x) = \sum_{n=1}^\infty \frac{x_n}{n^2}$，求表示元。

**变式2：** 证明 $H^{**} \cong H$（Hilbert空间的自反性）。
