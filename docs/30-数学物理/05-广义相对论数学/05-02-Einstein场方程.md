---
msc_primary: "83C05"
msc_secondary: ['83C10', '83C15', '35Q75']
---

# Einstein场方程

**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: v1.0
**状态**: 完成

---

## 📋 概述

Einstein场方程是广义相对论的核心，将时空几何与物质-能量分布联系起来："时空告诉物质如何运动，物质告诉时空如何弯曲"。这一方程的数学结构——拟线性双曲偏微分方程组——决定了其解的性质，包括引力波、黑洞和宇宙学演化。

**核心思想**: Einstein方程 $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ 编码了引力与物质的动力学。

---

## 📝 基础概念

### 1.1 能量-动量张量

**定义 1.1** (能量-动量张量)
**能量-动量张量**（应力-能量张量）$T_{\mu\nu}$ 描述物质场的能量、动量和应力分布：

- $T_{00}$: 能量密度 $\rho$
- $T_{0i}$: 动量密度
- $T_{ij}$: 应力张量（压强和剪切应力）

**理想流体的能量-动量张量**:
$$T_{\mu\nu} = (\rho + p)u_\mu u_\nu + pg_{\mu\nu}$$

其中 $u^\mu$ 是四速度，$p$ 是压强。

---

### 1.2 Einstein场方程

**定义 1.2** (Einstein场方程)
**Einstein场方程**:
$$G_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G T_{\mu\nu}$$

或等价地：
$$R_{\mu\nu} - \frac{1}{2}g_{\mu\nu}R + \Lambda g_{\mu\nu} = 8\pi G T_{\mu\nu}$$

其中：
- $G_{\mu\nu}$ 是Einstein张量
- $\Lambda$ 是宇宙学常数
- $G$ 是Newton引力常数

**迹形式**: 取迹得 $-R + 4\Lambda = 8\pi G T$，代回得：
$$R_{\mu\nu} - \Lambda g_{\mu\nu} = 8\pi G(T_{\mu\nu} - \frac{1}{2}g_{\mu\nu}T)$$

真空情形（$T_{\mu\nu} = 0$，$\Lambda = 0$）：$R_{\mu\nu} = 0$。

---

### 1.3 作用量原理

**定义 1.3** (Einstein-Hilbert作用量)
**Einstein-Hilbert作用量**:
$$S_{EH} = \frac{1}{16\pi G}\int d^4x\sqrt{-g}(R - 2\Lambda)$$

**物质作用量** $S_M$ 依赖于度量和物质场。

**定理 1.1** (Einstein方程的变分推导)
$\delta(S_{EH} + S_M) = 0$ 导出Einstein场方程，其中：
$$T_{\mu\nu} = -\frac{2}{\sqrt{-g}}\frac{\delta S_M}{\delta g^{\mu\nu}}$$

---

## 🎯 核心定理

### 2.1 广义协变性

**定理 2.1** (广义协变性)
Einstein场方程在任意坐标变换下形式不变。

**证明**: 所有量（$G_{\mu\nu}$、$T_{\mu\nu}$、$g_{\mu\nu}$）都是张量，方程是张量等式。$\square$

---

### 2.2 Bianchi恒等式与守恒律

**定理 2.2** (contracted Bianchi恒等式)
$$\nabla^\mu G_{\mu\nu} = 0$$

**推论** (能量-动量守恒):
由Einstein方程，自动得到：
$$\nabla^\mu T_{\mu\nu} = 0$$

这是广义相对论中能量-动量守恒的表达式。

**注意**: 这与狭义相对论中的 $\partial^\mu T_{\mu\nu} = 0$ 不同，后者是全局守恒，前者是协变守恒（包含引力贡献）。

---

### 2.3 初值问题

**定理 2.3** (Choquet-Bruhat, 1952)
对适当的初值数据（初始空间度量和外曲率），Einstein方程存在唯一的（局部）解，即存在最大Cauchy发展。

**3+1分解**:
将时空分解为空间切片 $\Sigma_t$，度量写为：
$$ds^2 = -N^2 dt^2 + g_{ij}(dx^i + N^i dt)(dx^j + N^j dt)$$

其中：
- $N$: 时移函数（lapse）
- $N^i$: 位移矢量（shift）
- $g_{ij}$: 空间度量

**约束方程**（Gauss-Codazzi方程）:
$$R^{(3)} + K^2 - K_{ij}K^{ij} = 16\pi G \rho \quad \text{(Hamilton约束)}$$
$$\nabla_j(K^{ij} - g^{ij}K) = 8\pi G j^i \quad \text{(动量约束)}$$

其中 $K_{ij}$ 是外曲率。

**演化方程**: 由Einstein方程导出的 $g_{ij}$ 和 $K_{ij}$ 的时间演化。

---

## 💡 实战问题

### 问题1：Newton极限

**问题**: 证明Einstein方程在弱场、低速极限下退化为Newton引力方程。

**解答**:

假设：
- 弱场: $g_{\mu\nu} = \eta_{\mu\nu} + h_{\mu\nu}$，$|h| \ll 1$

- 静态: $\partial_0 g_{\mu\nu} = 0$
- 低速: $v \ll c$

能量-动量张量: $T_{00} \approx \rho$，其他分量小。

线性化Einstein张量（时间-时间分量）：
$$G_{00} \approx -\frac{1}{2}\nabla^2 h_{00}$$

Einstein方程给出：
$$\nabla^2 h_{00} = -16\pi G \rho$$

定义Newton势 $\Phi = -\frac{1}{2}h_{00}$，得到：
$$\nabla^2 \Phi = 4\pi G \rho$$

这就是Newton引力方程。$\square$

---

### 问题2：Friedmann方程

**问题**: 从Einstein方程推导Friedmann方程（均匀各向同性宇宙）。

**解答**:

FLRW度量：
$$ds^2 = -dt^2 + a(t)^2\left(\frac{dr^2}{1-kr^2} + r^2d\Omega^2\right)$$

非零Einstein张量分量：
$$G_{00} = 3\frac{\dot{a}^2 + k}{a^2}, \quad G_{ij} = -(2\frac{\ddot{a}}{a} + \frac{\dot{a}^2 + k}{a^2})g_{ij}$$

能量-动量张量（理想流体）：
$$T_{00} = \rho, \quad T_{ij} = pg_{ij}$$

Einstein方程给出：
$$3\frac{\dot{a}^2 + k}{a^2} = 8\pi G \rho \quad \text{(Friedmann方程)}$$
$$2\frac{\ddot{a}}{a} + \frac{\dot{a}^2 + k}{a^2} = -8\pi G p \quad \text{(加速度方程)}$$

能量守恒：$\dot{\rho} + 3\frac{\dot{a}}{a}(\rho + p) = 0$

---

### 问题3：引力波方程

**问题**: 在弱场近似下，推导引力波的波动方程。

**解答**:

设 $g_{\mu\nu} = \eta_{\mu\nu} + h_{\mu\nu}$，$|h| \ll 1$。

线性化Einstein方程在**谐和规范**（$\nabla^\mu h_{\mu\nu} = 0$）下：
$$\Box \bar{h}_{\mu\nu} = -16\pi G T_{\mu\nu}$$

其中 $\bar{h}_{\mu\nu} = h_{\mu\nu} - \frac{1}{2}\eta_{\mu\nu}h$ 是迹反转扰动。

真空情形（$T_{\mu\nu} = 0$）：
$$\Box h_{\mu\nu} = 0$$

引力波以光速传播，有两个极化态（螺旋度 $\pm 2$）。$\square$

---

## 📚 相关文献

1. **Wald, R.M.** (1984). *General Relativity*. University of Chicago Press.
2. **Misner, C.W., Thorne, K.S., & Wheeler, J.A.** (1973). *Gravitation*. W.H. Freeman.
3. **Hawking, S.W., & Ellis, G.F.R.** (1973). *The Large Scale Structure of Space-Time*. Cambridge University Press.

---

**最后更新**: 2026年4月4日
