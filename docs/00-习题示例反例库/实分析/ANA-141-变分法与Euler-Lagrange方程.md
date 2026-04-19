---
msc_primary: 00A99
习题编号: ANA-141
学科: 实分析
知识点: 算子理论-变分法
难度: ⭐⭐⭐
预计时间: 30分钟
---

# 变分法与Euler-Lagrange方程

## 题目

设泛函 $I[u] = \int_\Omega L(x, u, \nabla u) dx$，其中 $L$ 是Lagrange量。

**(a)** 推导Euler-Lagrange方程：若 $u$ 是 $I$ 的临界点，则
$$-\text{div}(\nabla_p L) + \partial_u L = 0$$

**(b)** 对 $L = \frac{1}{2}|\nabla u|^2 - F(u)$，写出E-L方程并分析其形式。

**(c)** 证明Dirichlet原理：在 $W^{1,2}_0(\Omega)$ 中，$\Delta u = 0$ 的解最小化Dirichlet能量 $\int |\nabla u|^2$。

## 解答

### (a) Euler-Lagrange方程

**推导：**

设 $u$ 是临界点，$\varphi \in C_c^\infty(\Omega)$。

$$\frac{d}{d\varepsilon} I[u + \varepsilon \varphi]|_{\varepsilon = 0} = 0$$

计算：
$$\int_\Omega \left(\partial_u L \cdot \varphi + \nabla_p L \cdot \nabla \varphi\right) dx = 0$$

分部积分：
$$\int_\Omega \left(\partial_u L - \text{div}(\nabla_p L)\right) \varphi dx = 0$$

由 $\varphi$ 任意性：
$$-\text{div}(\nabla_p L) + \partial_u L = 0$$
$\square$

### (b) 具体Lagrange量

**解答：**

$L = \frac{1}{2}|\nabla u|^2 - F(u)$，$\nabla_p L = \nabla u$，$\partial_u L = -F'(u) = -f(u)$。

E-L方程：
$$-\Delta u = f(u)$$

这是**半线性椭圆方程**。

特例：
- $f(u) = 0$：Laplace方程
- $f(u) = u$：Helmholtz方程
- $f(u) = |u|^{p-1}u$：非线性Schrödinger方程$\square$

### (c) Dirichlet原理

**证明：**

设 $u$ 满足 $\Delta u = 0$，$u - g \in W^{1,2}_0(\Omega)$。

对任意 $v = u + \varphi$，$\varphi \in W^{1,2}_0$：
$$\int_\Omega |\nabla v|^2 = \int_\Omega |\nabla u + \nabla \varphi|^2$$

$$= \int_\Omega |\nabla u|^2 + 2\nabla u \cdot \nabla \varphi + |\nabla \varphi|^2$$

交叉项：
$$\int_\Omega \nabla u \cdot \nabla \varphi = -\int_\Omega \Delta u \cdot \varphi = 0$$

因此：
$$\int_\Omega |\nabla v|^2 = \int_\Omega |\nabla u|^2 + \int_\Omega |\nabla \varphi|^2 \geq \int_\Omega |\nabla u|^2$$

等号当且仅当 $\varphi = 0$。$\square$
