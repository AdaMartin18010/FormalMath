---
title: "02 Sobolev空间系统阐述"
msc_primary: "46E35"
msc_secondary: ['35D30', '35A15', '46B50']
processed_at: '2026-04-05'
---
# 02 Sobolev空间系统阐述 / Systematic Exposition of Sobolev Spaces

**主题编号**: B.03.06.02  
**创建日期**: 2026年4月3日  
**最后更新**: 2026年4月3日  
**MSC分类**: 46E35 (Sobolev空间), 35D30 (弱解), 35A15 (变分方法), 46B50 (紧性)  
**国际对齐**: Evans *PDE* Chapter 5; Brezis *Functional Analysis, Sobolev Spaces and PDE*; Mathlib4最新泛函分析扩展

---

## 目录 / Table of Contents

- 1 引言 / Introduction
- [2 Sobolev空间的定义与基本性质](#2-sobolev空间的定义与基本性质)
  - [2.1 弱导数](#21-弱导数)
  - [2.2 $W^{k,p}(\Omega)$ 的构造](#22-wkpoomega-的构造)
  - [2.3 Banach与Hilbert结构](#23-banach与hilbert结构)
- [3 逼近、延拓与迹定理](#3-逼近延拓与迹定理)
  - [3.1 Meyers–Serrin定理](#31-meyersserrin定理)
  - [3.2 延拓算子](#32-延拓算子)
  - [3.3 迹定理与Sobolev嵌入边界](#33-迹定理与sobolev嵌入边界)
- [4 嵌入定理与紧性](#4-嵌入定理与紧性)
  - [4.1 Sobolev嵌入](#41-sobolev嵌入)
  - 4.2 Rellich–Kondrachov定理
  - [4.3 Morrey嵌入与Hölder连续性](#43-morrey嵌入与hölder连续性)
- [5 对偶空间与负指数空间](#5-对偶空间与负指数空间)
- 6 例子 / Examples
- 7 参考文献 / References

---

## 1 引言 / Introduction

Sobolev空间是现代偏微分方程理论、变分学与数值分析的基石。自1930年代Sergei Sobolev开创性地引入这些函数空间以来，数学家们发现，即使解不具备经典意义下的光滑性，也可以在Sobolev空间中寻找“弱解”，从而极大地扩展了可解问题的范围。今天，无论是椭圆型方程的变分理论、抛物型方程的半群方法，还是双曲型方程的能量估计，Sobolev空间都提供了不可或缺的分析框架。

本系统阐述将从弱导数的严格定义出发，构造 $W^{k,p}(\Omega)$ 空间，讨论其Banach/Hilbert结构、逼近定理、延拓与迹定理，进而深入分析Sobolev嵌入、紧性定理以及对偶空间理论。所有内容对齐Lawrence Evans《Partial Differential Equations》第5章、Haim Brezis的泛函分析教材，以及Mathlib4在泛函分析方向的最新扩展。

---

## 2 Sobolev空间的定义与基本性质

### 2.1 弱导数

设 $\Omega \subset \mathbb{R}^n$ 为开集。

**定义 2.1** (弱导数)  
设 $u, v \in L^1_{\text{loc}}(\Omega)$，$\alpha$ 为多重指标。称 $v$ 为 $u$ 的 **$\alpha$ 阶弱导数**，记 $D^\alpha u = v$，如果：

$$
\int_\Omega u \, D^\alpha \phi \, dx = (-1)^{|\alpha|} \int_\Omega v \, \phi \, dx, \quad \forall \phi \in C_c^\infty(\Omega).

$$

**定理 2.1** (唯一性)  
若 $u$ 的弱导数 $D^\alpha u$ 存在，则它在几乎处处相等的意义下唯一。

*证明*：假设 $v_1, v_2$ 都满足上式，则对任意 $\phi$ 有 $\int_\Omega (v_1 - v_2) \phi = 0$。由检验函数的稠密性，$v_1 = v_2$ a.e.。

**定理 2.2** (与经典导数的一致性)  
若 $u \in C^k(\Omega)$，则其经典导数与弱导数在a.e.意义下相等。

### 2.2 $W^{k,p}(\Omega)$ 的构造

**定义 2.2** (Sobolev空间)  
对 $k \in \mathbb{N}$，$1 \le p \le \infty$，定义：

$$
W^{k,p}(\Omega) = \{ u \in L^p(\Omega) : D^\alpha u \in L^p(\Omega), \; \forall |\alpha| \le k \}.

$$

**Sobolev范数**：

$$
\|u\|_{W^{k,p}(\Omega)} =

\begin{cases}
\displaystyle \Bigl( \sum_{|\alpha| \le k} \|D^\alpha u\|_{L^p}^p \Bigr)^{1/p}, & 1 \le p < \infty, \\[1.2em]
\displaystyle \max_{|\alpha| \le k} \|D^\alpha u\|_{L^\infty}, & p = \infty.

\end{cases}
$$

**定义 2.3** (零边界Sobolev空间)  
$W_0^{k,p}(\Omega)$ 定义为 $C_c^\infty(\Omega)$ 在 $W^{k,p}(\Omega)$ 范数下的闭包。特别地，$H_0^1(\Omega) = W_0^{1,2}(\Omega)$。

### 2.3 Banach与Hilbert结构

**定理 2.3** (完备性)  
$W^{k,p}(\Omega)$ 是Banach空间。当 $p=2$ 时，$H^k(\Omega) = W^{k,2}(\Omega)$ 是Hilbert空间，内积为：

$$
(u, v)_{H^k} = \sum_{|\alpha| \le k} \int_\Omega D^\alpha u \, \overline{D^\alpha v} \, dx.

$$

*证明思路*：设 $\{u_m\}$ 为 $W^{k,p}$ 中的Cauchy列。则对每个 $|\alpha| \le k$，$\{D^\alpha u_m\}$ 是 $L^p$ 中的Cauchy列。由 $L^p$ 的完备性，$D^\alpha u_m \to v_\alpha$ 于 $L^p$。再验证 $v_\alpha = D^\alpha u$（其中 $u = v_0$），利用弱导数的定义和极限交换即可。

**定理 2.4** (可分性与自反性)  
对 $1 \le p < \infty$，$W^{k,p}(\Omega)$ 是可分的。对 $1 < p < \infty$，它是自反的（uniformly convex）。

---

## 3 逼近、延拓与迹定理

### 3.1 Meyers–Serrin定理

**定理 3.1** (Meyers–Serrin, $H = W$)  
设 $1 \le p < \infty$。则 $C^\infty(\Omega) \cap W^{k,p}(\Omega)$ 在 $W^{k,p}(\Omega)$ 中稠密。

*证明思路*：取 $\Omega$ 的一个局部有限开覆盖 $\{U_i\}$ 及从属于它的单位分解 $\{\eta_i\}$。对每个 $u \in W^{k,p}(\Omega)$，$\eta_i u$ 具有紧支集。用磨光核（mollifier）$\rho_\varepsilon * (\eta_i u)$ 逼近，然后取有限和。由于磨光在 $L^p$ 下保持范数收敛，且导数可交换，最终得到光滑逼近序列。

**注**：在边界上 $C^\infty(\overline{\Omega})$ 的稠密性要求 $\Omega$ 具有 **Lipschitz边界**（或更强，如 $C^1$ 边界）。

### 3.2 延拓算子

**定理 3.2** (延拓定理)  
设 $\Omega \subset \mathbb{R}^n$ 为有界Lipschitz区域。则存在有界线性算子 $E: W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^n)$ 使得 $Eu|_\Omega = u$ 且

$$
\|Eu\|_{W^{k,p}(\mathbb{R}^n)} \le C \, \|u\|_{W^{k,p}(\Omega)}.

$$

*证明思路*（半空间情形）：设 $\Omega = \mathbb{R}^n_+ = \{x_n > 0\}$。对 $x_n < 0$ 用反射延拓：

$$
Eu(x', x_n) =
\begin{cases}
u(x', x_n), & x_n > 0, \\[0.5em]
\displaystyle \sum_{j=1}^{k+1} c_j \, u(x', -j x_n), & x_n < 0,
\end{cases}
$$

其中系数 $c_j$ 由在 $x_n = 0$ 处匹配前 $k$ 阶导数的连续性条件确定。然后通过单位分解将局部图粘合为整体延拓算子。

### 3.3 迹定理与Sobolev嵌入边界

**定理 3.3** (迹定理)  
设 $\Omega$ 为有界Lipschitz区域，$1 \le p < \infty$。则存在有界线性 **迹算子** $T: W^{1,p}(\Omega) \to L^p(\partial\Omega)$ 使得对 $u \in C(\overline{\Omega}) \cap W^{1,p}(\Omega)$，$Tu = u|_{\partial\Omega}$。且：

$$
\ker T = W_0^{1,p}(\Omega).
$$

*证明思路*：先在半空间情形用Fubini定理与一维Sobolev嵌入证明 $u(x', 0)$ 可由 $u$ 在 $x_n > 0$ 上的积分控制：

$$
\int_{\mathbb{R}^{n-1}} |u(x', 0)|^p dx' \le C \int_{\mathbb{R}^n_+} (|u|^p + |\nabla u|^p) dx.

$$

然后通过局部图和分区单位推广到一般Lipschitz边界。

**定理 3.4** (高阶迹)  
对 $u \in W^{k,p}(\Omega)$，可定义迹 $T_j u = \frac{\partial^j u}{\partial \nu^j}|_{\partial\Omega} \in W^{k-j-1/p,p}(\partial\Omega)$，其中 $0 \le j \le k-1$，$\nu$ 为外法向。特别地，$T: H^1(\Omega) \to H^{1/2}(\partial\Omega)$ 是有界满射。

---

## 4 嵌入定理与紧性

### 4.1 Sobolev嵌入

**定理 4.1** (Sobolev嵌入定理)  
设 $\Omega \subset \mathbb{R}^n$ 为有界光滑区域，$k \in \mathbb{N}$，$1 \le p < \infty$。

- **次临界情形** ($kp < n$)：$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ 连续，其中 $q = p^* = \frac{np}{n-kp}$（Sobolev共轭指数）。
- **临界情形** ($kp = n$)：$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ 对所有 $1 \le q < \infty$ 连续嵌入。
- **超临界情形** ($kp > n$)：$W^{k,p}(\Omega) \hookrightarrow C^{k-\lfloor n/p \rfloor - 1, \gamma}(\overline{\Omega})$，其中 $\gamma = \lfloor n/p \rfloor + 1 - n/p$（若 $n/p \notin \mathbb{N}$），或任意 $\gamma < 1$（若 $n/p \in \mathbb{N}$）。

*证明思路*：核心不等式是 **Gagliardo–Nirenberg–Sobolev不等式**：对 $u \in C_c^\infty(\mathbb{R}^n)$，$1 \le p < n$，

$$
\|u\|_{L^{p^*}(\mathbb{R}^n)} \le C \, \|\nabla u\|_{L^p(\mathbb{R}^n)}.

$$

通过对各坐标方向应用Newton–Leibniz公式和Hölder不等式，再对 $n$ 个方向取几何平均，可得到该不等式。然后由延拓定理和逼近定理推广到一般 $W^{1,p}(\Omega)$。

### 4.2 Rellich–Kondrachov定理

**定理 4.2** (Rellich–Kondrachov)  
在次临界情形 $kp < n$ 且 $1 \le q < p^*$，嵌入 $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ 是 **紧的**。在超临界情形 $kp > n$，嵌入 $W^{k,p}(\Omega) \hookrightarrow C^{m,\gamma}(\overline{\Omega})$ 也是紧的（对适当的 $m, \gamma$）。

*证明思路*：紧性等价于：$W^{k,p}(\Omega)$ 中的有界序列必有在 $L^q$ 中强收敛的子列。利用Arzelà–Ascoli定理（超临界）或Kolmogorov紧性准则（次临界）。关键步骤是：对光滑区域，通过延拓和磨光，有界序列可被一致光滑地逼近，而一致光滑性加上 $L^p$ 有界性给出等度连续性，从而提取一致收敛子列。

### 4.3 Morrey嵌入与Hölder连续性

**定理 4.3** (Morrey不等式)  
设 $n < p \le \infty$。则存在常数 $C = C(n,p)$ 使得对所有 $u \in W^{1,p}(\mathbb{R}^n)$：

$$
\|u\|_{C^{0,\gamma}(\mathbb{R}^n)} \le C \, \|u\|_{W^{1,p}(\mathbb{R}^n)}, \qquad \gamma = 1 - \frac{n}{p}.

$$

这意味着 $W^{1,p}$ 函数在 $p > n$ 时自动具有Hölder连续性。这是Schauder正则性理论和非线性分析中Nemytskii算子连续性的基础。

---

## 5 对偶空间与负指数空间

**定义 5.1** ($W^{-k,p'}$)  
设 $1 \le p < \infty$，$p'$ 为共轭指数（$1/p + 1/p' = 1$）。定义 $W^{-k,p'}(\Omega)$ 为 $W_0^{k,p}(\Omega)$ 的对偶空间，配备算子范数：

$$
\|f\|_{W^{-k,p'}(\Omega)} = \sup_{\substack{u \in W_0^{k,p}(\Omega) \\ u \neq 0}} \frac{|\langle f, u \rangle|}{\|u\|_{W^{k,p}(\Omega)}}.

$$

**定理 5.1** (结构的刻画)  
任意 $f \in W^{-k,p'}(\Omega)$ 可表示为

$$
f = \sum_{|\alpha| \le k} (-1)^{|\alpha|} D^\alpha f_\alpha,

$$

其中 $f_\alpha \in L^{p'}(\Omega)$。即负指数Sobolev空间中的元素是低阶 $L^{p'}$ 函数的分布导数的有限和。

*证明思路*：应用Hahn–Banach定理将 $f$ 从 $W_0^{k,p}(\Omega)$ 延拓到乘积空间 $\prod_{|\alpha|\le k} L^p(\Omega)$，再利用Riesz表示定理，得到每个分量的 $L^{p'}$ 表示。

**例 5.1**：Dirac测度 $\delta_0 \in H^{-1}(\mathbb{R})$（对 $n=1$），因为

$$

|\langle \delta_0, u \rangle| = |u(0)| \le C \|u\|_{H^1(\mathbb{R})}

$$

由一维Sobolev嵌入。但在 $\mathbb{R}^n$ ($n \ge 2$) 中，$\delta_0 \in H^{-s}(\mathbb{R}^n)$ 仅当 $s > n/2$。

---

## 6 例子 / Examples

**例 6.1** ($|x|^{-\alpha}$ 的Sobolev正则性)  
设 $\Omega = B_1(0) \subset \mathbb{R}^n$，$u(x) = |x|^{-\alpha}$，$\alpha > 0$。计算得：

$$
\int_\Omega |u|^p \, dx = C \int_0^1 r^{-\alpha p} r^{n-1} dr < \infty \iff \alpha p < n.

$$

类似地，$|\nabla u| \sim |x|^{-\alpha-1}$，故 $|\nabla u| \in L^p$ 当且仅当 $(\alpha+1)p < n$。因此 $u \in W^{1,p}(\Omega)$ 当且仅当 $\alpha < \frac{n-p}{p}$。当 $p > n$ 时，不存在这样的奇点（因为 $u$ 本身已Hölder连续）。

**例 6.2** (三维嵌入)  
设 $n=3$，$p=2$，$k=1$。则 $kp = 2 < 3$，Sobolev共轭指数为

$$
p^* = \frac{np}{n-p} = \frac{6}{1} = 6.
$$

故 $H^1(\Omega) \hookrightarrow L^6(\Omega)$。这在量子力学Schrödinger方程的研究中至关重要：$|\psi|^6$ 的可积性保证了非线性项 $|\psi|^4 \psi$ 在 $H^1$ 中良定义。

**例 6.3** (迹的应用)  
设 $\Omega = \mathbb{R}^n_+ = \{x_n > 0\}$。对 $u \in H^1(\mathbb{R}^n_+)$，迹 $Tu \in H^{1/2}(\mathbb{R}^{n-1})$，且映射 $T: H^1(\mathbb{R}^n_+) \to H^{1/2}(\mathbb{R}^{n-1})$ 是连续满射。反之，对任意 $g \in H^{1/2}(\mathbb{R}^{n-1})$，存在 $u \in H^1(\mathbb{R}^n_+)$ 使得 $Tu = g$ 且 $\|u\|_{H^1} \le C \|g\|_{H^{1/2}}$。这是研究Dirichlet边值问题时边界数据正则性的精确描述。

---

## 7 参考文献 / References

### 经典教材

1. **Evans, L. C.** (2010). *Partial Differential Equations* (2nd ed.). American Mathematical Society. Chapter 5.
2. **Brezis, H.** (2011). *Functional Analysis, Sobolev Spaces and Partial Differential Equations*. Springer.
3. **Adams, R. A., & Fournier, J. J. F.** (2003). *Sobolev Spaces* (2nd ed.). Academic Press.
4. **Leoni, G.** (2017). *A First Course in Sobolev Spaces* (2nd ed.). AMS.

### 进阶文献

5. **Tartar, L.** (2007). *An Introduction to Sobolev Spaces and Interpolation Spaces*. Springer.
6. **Maz'ya, V.** (2011). *Sobolev Spaces with Applications to Elliptic Partial Differential Equations*. Springer.
7. **DiBenedetto, E.** (2002). *Real Analysis*. Birkhäuser.
8. **Mathlib4 Documentation**. https://leanprover-community.github.io/mathlib4_docs/[需更新[需更新]] (泛函分析与Sobolev空间形式化)

### 中文参考

9. **张恭庆、林源渠** (2004). *泛函分析讲义*（上、下）. 北京大学出版社.
10. **陈恕行** (2005). *现代偏微分方程导论*. 科学出版社.

---

**文档状态**: 完成  
**字数**: 约5,500字  
**数学公式数**: 40+  
**例子数**: 3  
**最后更新**: 2026年4月3日
