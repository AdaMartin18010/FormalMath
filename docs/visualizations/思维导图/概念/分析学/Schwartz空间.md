---
msc_primary: 00A99
msc_secondary:
- 00A99
title: Schwartz空间 (Schwartz Space)
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# Schwartz空间 (Schwartz Space)

## 中心概念精确定义

**Schwartz空间**（速降函数空间）是Fourier分析中的核心函数空间，其上的函数及其各阶导数在无穷远处都以多项式速度衰减到零。

> **Schwartz空间** $\mathcal{S}(\mathbb{R}^n)$：所有 $C^\infty$ 函数 $f: \mathbb{R}^n \to \mathbb{C}$ 满足：
> $$\|f\|_{\alpha,\beta} = \sup_{x \in \mathbb{R}^n} |x^\alpha \partial^\beta f(x)| < \infty$$

> 对所有多重指标 $\alpha, \beta$ 成立。

等价表述：$f$ 及其所有导数比任何多项式的倒数衰减得都快。

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Schwartz空间<br/>Schwartz Space 𝒮))
    定义与性质
      速降条件

        |x^α ∂^β f|<∞

        多项式控制
      拓扑结构
        半范数族
        Fréchet空间
        度量完备
      包含关系
        C_c^∞ ⊂ 𝒮 ⊂ L^p
        稠密嵌入
    Fourier变换
      𝒮上同构
        双射
        连续逆
      性质保持
        微分⇔乘法
        平移⇔调制
      对偶性
        时频局部化
        不确定性原理
    分布理论
      缓增分布 𝒮'
        连续线性泛函
        广义函数
      运算扩展
        微分
        Fourier变换
        卷积
      例子
        δ函数
        多项式
        e^{iax}
    应用
      偏微分方程
        常系数线性PDE
        基本解
      量子力学
        波函数
        不确定性原理
      信号处理
        时频分析
        Gabor变换
    拓扑性质
      Montel空间
        有界⇒相对紧
      核定理
        双线性形式
        张量积

```

---

## 核心要素详解

### 1. Schwartz空间的拓扑结构

**半范数族**：对多重指标 $\alpha, \beta$，定义：
$$\|f\|_{\alpha,\beta} = \sup_{x \in \mathbb{R}^n} |x^\alpha \partial^\beta f(x)|$$

**收敛性**：$f_k \to f$ 在 $\mathcal{S}$ 中 $\Leftrightarrow$ $\|f_k - f\|_{\alpha,\beta} \to 0$ 对所有 $\alpha, \beta$。

**Fréchet空间结构**：
- 完备度量空间
- 局部凸
- 不可赋范（无穷多半范数）

**重要包含关系**：
$$C_c^\infty(\mathbb{R}^n) \subset \mathcal{S}(\mathbb{R}^n) \subset L^p(\mathbb{R}^n) \text{ 对所有 } p \in [1,\infty]$$

且 $C_c^\infty$ 在 $\mathcal{S}$ 中稠密，$\mathcal{S}$ 在 $L^p$ 中稠密（$p < \infty$）。

### 2. 速降函数的刻画

**等价条件**：以下任一等价于 $f \in \mathcal{S}$：
1. 对所有 $k, m \in \mathbb{N}$：$|f(x)| \leq C_{k,m}(1+|x|)^{-k}$ 且 $|\partial^\beta f(x)| \leq C_{k,m}(1+|x|)^{-k}$

2. 对所有多项式 $P$ 和微分算子 $Q$：$P(x)Q(D)f \in L^\infty$
3. 对所有多项式 $P$：$P(D)f \in L^1$ 且 $Pf \in L^1$

**标准例子**：
- Gauss函数：$e^{-|x|^2} \in \mathcal{S}$

- 紧支光滑函数：$C_c^\infty \subset \mathcal{S}$
- 非例子：$e^{-|x|} \notin \mathcal{S}$（在0点不可微）

### 3. Fourier变换在 $\mathcal{S}$ 上的性质

**定理**：Fourier变换 $\mathcal{F}: \mathcal{S} \to \mathcal{S}$ 是拓扑同构（双射且双方连续）。

**证明要点**：
- 利用 $\mathcal{F}(x_j f) = i\partial_j \hat{f}$ 和 $\mathcal{F}(\partial_j f) = i\xi_j \hat{f}$
- 微分与乘法的交换保持速降性
- 反变换公式：$f(x) = \int \hat{f}(\xi) e^{2\pi i x \cdot \xi} d\xi$

**关键恒等式**：
- **微分与乘法**：$\widehat{\partial^\alpha f}(\xi) = (2\pi i \xi)^\alpha \hat{f}(\xi)$
- **多项式乘法**：$\widehat{x^\alpha f}(\xi) = (-2\pi i)^{-|\alpha|} \partial^\alpha \hat{f}(\xi)$

**Parseval等式**：在 $\mathcal{S}$ 上：
$$\int f \bar{g} = \int \hat{f} \bar{\hat{g}}$$

### 4. 缓增分布 $\mathcal{S}'$

**定义**：$\mathcal{S}'$（tempered distributions）是 $\mathcal{S}$ 上的连续线性泛函：
$$\langle T, \phi \rangle \in \mathbb{C}, \quad \phi \in \mathcal{S}$$

**连续性**：$\phi_k \to 0$ 在 $\mathcal{S}$ 中 $\Rightarrow$ $\langle T, \phi_k \rangle \to 0$。

**重要例子**：

| 分布 | 作用 | 说明 |
|------|------|------|
| **Dirac delta** | $\langle \delta, \phi \rangle = \phi(0)$ | 点质量 |
| **常数1** | $\langle 1, \phi \rangle = \int \phi$ | $L^\infty_{loc}$ |
| **多项式** | $\langle x^\alpha, \phi \rangle = \int x^\alpha \phi$ | 缓增函数 |
| **$e^{iax}$** | $\langle e^{iax}, \phi \rangle = \int e^{iax}\phi$ | 振荡函数 |
| **pv(1/x)** | 主值积分 | 奇异分布 |
| **$x_+^\lambda$** | 分数幂 | 解析延拓 |

### 5. 分布的运算

**微分**：$\langle \partial^\alpha T, \phi \rangle = (-1)^{|\alpha|} \langle T, \partial^\alpha \phi \rangle$

**Fourier变换**：$\langle \hat{T}, \phi \rangle = \langle T, \hat{\phi} \rangle$

**与函数的乘积**：$\langle fT, \phi \rangle = \langle T, f\phi \rangle$（$f$ 缓增光滑）

**卷积**（$T \in \mathcal{S}'$，$\phi \in \mathcal{S}$）：
$$(T * \phi)(x) = \langle T, \tau_x \tilde{\phi} \rangle, \quad \tilde{\phi}(y) = \phi(-y)$$

---

## 关键性质与定理

### 定理1：核定理（Schwartz核定理）

**定理**：从 $\mathcal{S}(\mathbb{R}^n)$ 到 $\mathcal{S}'(\mathbb{R}^m)$ 的连续线性映射 $K$ 对应唯一的分布 $K(x,y) \in \mathcal{S}'(\mathbb{R}^{n+m})$ 使得：
$$\langle K\phi, \psi \rangle = \langle K(x,y), \phi(y)\psi(x) \rangle$$

这是Fourier积分算子理论的基础。

### 定理2：分布的Fourier变换公式

**重要变换对**：

| 原函数/分布 | Fourier变换 |
|-------------|-------------|
| $\delta(x)$ | $1$ |
| $1$ | $\delta(\xi)$ |
| $e^{2\pi i a x}$ | $\delta(\xi - a)$ |
| $\delta(x - a)$ | $e^{-2\pi i a \xi}$ |
| $x^n$ | $(i/2\pi)^n \delta^{(n)}(\xi)$ |
| $\sin(2\pi a x)$ | $\frac{1}{2i}[\delta(\xi-a) - \delta(\xi+a)]$ |

### 定理3：不确定性原理（Heisenberg-Pauli-Weyl）

**定理**：对 $f \in \mathcal{S}(\mathbb{R})$，$\|f\|_2 = 1$：
$$\left(\int x^2 |f(x)|^2 dx\right)^{1/2} \left(\int \xi^2 |\hat{f}(\xi)|^2 d\xi\right)^{1/2} \geq \frac{1}{4\pi}$$

等号成立当且仅当 $f$ 是Gauss函数。

**物理意义**：位置和动量不能同时精确确定。

### 定理4：Paley-Wiener定理

**定理**：紧支分布 $T \in \mathcal{E}'(\mathbb{R}^n)$ 的Fourier变换 $\hat{T}$ 是指数型的整函数。

**逆定理**：指数型整函数是某紧支分布的Fourier变换。

---

## 典型例子

### 例子1：Dirac delta的导数

**作用**：$\langle \delta', \phi \rangle = -\phi'(0)$

**物理解释**：偶极子、点力矩。

**Fourier变换**：$\widehat{\delta'} = 2\pi i \xi$

### 例子2：常系微分方程的基本解

**问题**：求 $u$ 使得 $u'' + u = \delta$。

**解**：Fourier变换：$(-4\pi^2 \xi^2 + 1)\hat{u} = 1$

$$\hat{u}(\xi) = \frac{1}{1 - 4\pi^2 \xi^2}$$

反变换得：$u(x) = \frac{1}{2}\sin|x|$（基本解）。

### 例子3：振荡积分

考虑 $T = \int_0^\infty e^{ix\xi} d\xi$（作为分布）。

形式上，这是 $\frac{i}{x + i0}$，其实部是主值 $pv(1/x)$，虚部是 $\pi \delta(x)$。

---

## 关联概念网络

### 相似概念

| 概念 | 关系 | 说明 |
|------|------|------|
| **Gelfand-Shilov空间** | 细化 | 衰减速率更精细的类 |
| **Beurling空间** | 推广 | 超函数理论 |
| **Colombeau代数** | 新理论 | 分布的乘法结构 |

### 对偶概念

| 概念 | 对偶关系 | 说明 |
|------|----------|------|
| **$\mathcal{S} \leftrightarrow \mathcal{S}'$** | 对偶对 | 测试函数与分布 |
| **速降 ↔ 缓增** | 增长对偶 | 空间命名来源 |

### 推广概念

```

Schwartz空间 → Gelfand-Shilov空间
      ↓
   超函数(Sato)
      ↓
   微局部分析
      ↓
   代数分析(D-模)

```

---

## 课程对齐

### MIT 18.100
- **Supplementary**: Distribution theory basics
- **Related**: 18.155 (Differential Analysis)

### Princeton MAT 218
- **Topic**: Fourier analysis, distributions
- **Text**: Hörmander, *The Analysis of Linear Partial Differential Operators I*, Ch. 7
- **Key topics**: Schwartz space, tempered distributions, Fourier transform

---

## 总结

Schwartz空间是Fourier分析的天然舞台，其速降性质保证了Fourier变换的封闭性。作为Fréchet空间，$\mathcal{S}$ 拥有丰富的拓扑结构，其上的Fourier变换是拓扑同构。缓增分布 $\mathcal{S}'$ 将广义函数的概念扩展到允许多项式增长的情形，使得Fourier变换可以作用于常数函数、多项式、三角函数等重要的非可积函数。Schwartz空间与缓增分布构成了分析、PDE和量子力学中不可或缺的工具。

---

*创建日期：2026年4月*  
*相关概念：[Fourier分析](Fourier分析.md)、[分布理论](分布理论.md)、[卷积与逼近](卷积与逼近.md)*
