---
msc_primary: 53-01
msc_secondary:
  - 53A04
  - 53A05
  - 53C22
---

# UCLA 微分几何核心内容

UCLA Math 164（微分几何）涵盖曲线与曲面的局部理论、曲率、测地线与 Gauss-Bonnet 定理。本节提供该课程的严格数学内容，包括核心定义、定理证明与典型例子。

## 1. 曲线的局部理论

### 1.1 正则曲线与弧长参数

**定义 1.1（正则曲线）**. 参数曲线 $\gamma: I \to \mathbb{R}^3$ 称为正则的，若 $\gamma'(t) \neq 0$ 对所有 $t \in I$。正则曲线允许弧长参数化：
$$s(t) = \int_{t_0}^t |\gamma'(\tau)|\, d\tau.$$

**定理 1.2（Frenet-Serret）**. 对弧长参数化的正则曲线（曲率 $\kappa(s) > 0$），存在唯一正交标架 $\{T(s), N(s), B(s)\}$ 满足：
$$\frac{d}{ds}\begin{pmatrix} T \\ N \\ B \end{pmatrix} = \begin{pmatrix} 0 & \kappa & 0 \\ -\kappa & 0 & \tau \\ 0 & -\tau & 0 \end{pmatrix} \begin{pmatrix} T \\ N \\ B \end{pmatrix},$$
其中 $\kappa$ 为曲率，$\tau$ 为挠率。

*证明*. $T = \gamma'$ 为单位切向量。$T' \perp T$，定义 $N = T'/|T'|$，$\kappa = |T'|$。$B = T \times N$。求导 $B' = T' \times N + T \times N' = T \times N'$，故 $B' \perp T$ 且 $B' \perp B$，$B' = -\tau N$。由 $N = B \times T$ 求导得 $N' = -\kappa T + \tau B$。$\square$

**推论 1.3（曲线论基本定理）**. 给定光滑函数 $\kappa(s) > 0$ 和 $\tau(s)$，存在唯一（至多差刚体运动）的弧长参数曲线以 $\kappa, \tau$ 为曲率与挠率。

## 2. 曲面的局部理论

### 2.1 第一基本形式

**定义 2.1（第一基本形式）**. 曲面 $S \subset \mathbb{R}^3$ 的参数表示 $r(u,v)$ 诱导度量：
$$I = E\,du^2 + 2F\,du\,dv + G\,dv^2,$$
其中 $E = \langle r_u, r_u \rangle$，$F = \langle r_u, r_v \rangle$，$G = \langle r_v, r_v \rangle$。

第一基本形式决定曲面的内蕴几何：弧长、角度、面积均只依赖 $I$。

### 2.2 第二基本形式与曲率

**定义 2.2（Weingarten 映射与曲率）**. 设 $n$ 为单位法向量。Shape 算子（Weingarten 映射）$W = -Dn: T_pS \to T_pS$ 为自伴线性映射。其特征值 $k_1, k_2$ 为主曲率，行列式 $K = k_1 k_2$ 为 Gauss 曲率，迹的一半 $H = (k_1 + k_2)/2$ 为平均曲率。

用第二基本形式系数 $L = \langle r_{uu}, n \rangle$，$M = \langle r_{uv}, n \rangle$，$N = \langle r_{vv}, n \rangle$：
$$K = \frac{LN - M^2}{EG - F^2}.$$

**定理 2.3（Gauss 绝妙定理 / Theorema Egregium）**. Gauss 曲率 $K$ 是内蕴量，仅依赖于第一基本形式及其导数。

*证明概要*. 用第一基本形式的 Christoffel 符号 $\Gamma^k_{ij}$ 表达 $K$。Brioschi 公式给出
$$K = -\frac{1}{2\sqrt{EG-F^2}}\left[\frac{\partial}{\partial u}\left(\frac{G_u - 2F_v}{\sqrt{EG-F^2}}\right) + \frac{\partial}{\partial v}\left(\frac{E_v - 2F_u}{\sqrt{EG-F^2}}\right)\right] - \frac{1}{4(EG-F^2)^2}\begin{vmatrix} E & F & G \\ E_u & F_u & G_u \\ E_v & F_v & G_v \end{vmatrix}.$$
仅含 $E, F, G$ 及其导数。$\square$

## 3. Gauss-Bonnet 定理

**定理 3.1（局部 Gauss-Bonnet）**. 设 $D$ 为曲面上由分段光滑简单闭曲线 $\partial D$ 围成的区域，外角为 $\theta_1, \dots, \theta_n$，则
$$\int_D K\,dA + \oint_{\partial D} k_g\,ds + \sum_{i=1}^n \theta_i = 2\pi,$$
其中 $k_g$ 为测地曲率。

**定理 3.2（整体 Gauss-Bonnet）**. 设 $S$ 为紧定向曲面（无边），则
$$\int_S K\,dA = 2\pi \chi(S) = 2\pi (2 - 2g).$$

*证明概要*. 对三角剖分，每个三角形上应用局部 Gauss-Bonnet。边界项相消（每条边被两个三角形以相反方向遍历），顶点处外角和为 $2\pi$。得
$$\int_S K\,dA + \sum_{\text{顶点}} 2\pi = 2\pi F,$$
即 $\int_S K\,dA = 2\pi(F - E + V) = 2\pi\chi(S)$。$\square$

## 4. 测地线

**定义 4.1（测地线）**. 曲面上测地曲率为零的曲线，即"尽可能直"的曲线。在局部坐标下，测地线满足方程：
$$\frac{d^2 u^k}{dt^2} + \Gamma^k_{ij} \frac{du^i}{dt} \frac{du^j}{dt} = 0,$$
其中 $\Gamma^k_{ij}$ 为 Christoffel 符号。

**定理 4.2（测地线的变分特征）**. 测地线是弧长泛函的临界点：对固定端点的变分 $\gamma_\varepsilon$，
$$\left.\frac{d}{d\varepsilon}\right|_{\varepsilon=0} L(\gamma_\varepsilon) = 0 \iff \gamma_0 \text{ 为测地线}.$$

**定理 4.3（指数映射）**. 对 $p \in S$，$v \in T_pS$，存在唯一测地线 $\gamma_v$ 满足 $\gamma_v(0) = p$，$\gamma_v'(0) = v$。指数映射 $\exp_p(v) = \gamma_v(1)$ 在 $0 \in T_pS$ 附近为微分同胚。

## 5. 例子

### 5.1 球面

半径 $R$ 的球面：参数化 $r(\theta, \phi) = (R\sin\theta\cos\phi, R\sin\theta\sin\phi, R\cos\theta)$。

第一基本形式：$ds^2 = R^2\,d\theta^2 + R^2\sin^2\theta\,d\phi^2$。

Gauss 曲率：$K = 1/R^2$（常数）。整体 Gauss-Bonnet：$\int K\,dA = 4\pi = 2\pi \cdot 2$，$\chi(S^2) = 2$。

测地线为大圆。

### 5.2 环面

环面 $T^2$：参数化 $r(\theta, \phi) = ((R+r\cos\theta)\cos\phi, (R+r\cos\theta)\sin\phi, r\sin\theta)$。

Gauss 曲率 $K = \frac{\cos\theta}{r(R+r\cos\theta)}$ 变号。整体：$\int K\,dA = 0 = 2\pi \cdot 0$，$\chi(T^2) = 0$。

## 6. 交叉引用

- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 流形与联络
- [黎曼几何](docs/04-几何与拓扑/02-微分几何-扩展/02-黎曼几何/01-黎曼几何基础.md) — 测地线与曲率深化
- [张量分析](docs/03-分析学/张量分析-基础.md) — Christoffel 符号与曲率张量
- [指标定理](docs/04-几何与拓扑/指标定理应用.md) — Gauss-Bonnet 的高维推广
- [代数拓扑](docs/04-几何与拓扑/03-代数拓扑/同调论基础.md) — Euler 示性数与三角剖分

---

**适用**：docs/04-International-Alignment/
