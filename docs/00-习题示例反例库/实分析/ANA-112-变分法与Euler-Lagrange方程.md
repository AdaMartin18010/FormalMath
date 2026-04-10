---
习题编号: ANA-112
学科: 实分析
知识点: 变分法-Euler-Lagrange方程
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# 变分法与Euler-Lagrange方程

## 题目

设 $L(x, u, p)$ 是Lagrange函数（$C^2$），考虑泛函：
$$I[u] = \int_\Omega L(x, u(x), \nabla u(x)) dx$$

于容许集 $\mathcal{A} = \{u \in C^1(\bar{\Omega}) : u = g \text{ 于 } \partial\Omega\}$。

(a) 推导Euler-Lagrange方程：若 $u$ 是极小元，则：
$$-\text{div}(\nabla_p L) + \partial_u L = 0$$

(b) 对 $L = \frac{1}{2}|\nabla u|^2 - fu$，写出E-L方程。

(c) 证明Dirichlet原理：$\int_\Omega |\nabla u|^2$ 的极小元满足Laplace方程。

## 解答

### (a) Euler-Lagrange方程推导

**推导：**

设 $u$ 是极小元，$v \in C_c^\infty(\Omega)$。

考虑变分 $u + \varepsilon v$，$i(\varepsilon) = I[u + \varepsilon v]$。

极小性要求 $i'(0) = 0$。

计算：
$$i'(0) = \int_\Omega \left(\partial_u L \cdot v + \nabla_p L \cdot \nabla v\right) dx = 0$$

分部积分：
$$= \int_\Omega \left(\partial_u L - \text{div}(\nabla_p L)\right) v dx = 0$$

对所有 $v \in C_c^\infty$ 成立。

由变分法基本引理：
$$-\text{div}(\nabla_p L) + \partial_u L = 0$$
$\square$

### (b) 具体例子

**解答：**

$L = \frac{1}{2}|\nabla u|^2 - fu$。

计算偏导：
- $\partial_u L = -f$
- $\nabla_p L = \nabla u$（注意 $p = \nabla u$）

E-L方程：
$$-\text{div}(\nabla u) - f = 0$$

即Poisson方程：
$$-\Delta u = f$$
$\square$

### (c) Dirichlet原理

**定理**：在 $u = g$ 于 $\partial\Omega$ 的边界条件下，$\int_\Omega |\nabla u|^2$ 的极小元满足：
$$\begin{cases} \Delta u = 0 & \text{于 } \Omega \\ u = g & \text{于 } \partial\Omega \end{cases}$$

**证明：**

由(b)，$f = 0$ 时E-L方程为 $-\Delta u = 0$。

或直接验证：设 $u$ 调和，$v = g$ 于 $\partial\Omega$。

$$\int_\Omega |\nabla v|^2 = \int_\Omega |\nabla u + \nabla(v-u)|^2$$

$$= \int_\Omega |\nabla u|^2 + 2\int_\Omega \nabla u \cdot \nabla(v-u) + \int_\Omega |\nabla(v-u)|^2$$

中间项：由 $v-u = 0$ 于 $\partial\Omega$，分部积分：
$$\int_\Omega \nabla u \cdot \nabla(v-u) = -\int_\Omega \Delta u \cdot (v-u) = 0$$

因此：
$$\int_\Omega |\nabla v|^2 = \int_\Omega |\nabla u|^2 + \int_\Omega |\nabla(v-u)|^2 \geq \int_\Omega |\nabla u|^2$$

$u$ 确实是极小元。$\square$

## 证明技巧

1. **变分法基本引理**：测试函数的任意性推出点态等式
2. **分部积分**：将导数从变分转移到被变分函数
3. **凸性**：Dirichlet泛函的严格凸性保证唯一性

## 常见错误

- ❌ 边界项处理不当（需要测试函数在边界为零）
- ❌ 混淆 $\nabla_p L$ 与 $\partial_u L$
- ❌ 忘记验证极小元的存在性

## 变式练习

**变式1：** 推导测地线方程：极小化 $\int \sqrt{g_{ij}\dot{x}^i\dot{x}^j} dt$。

**变式2：** 推导极小曲面方程：$L = \sqrt{1 + |\nabla u|^2}$。
