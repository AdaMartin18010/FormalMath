---
msc_primary: 00A99
习题编号: GEO-054
学科: 几何
知识点: 几何-Kahler几何
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Kähler 几何基础

## 题目

**(a)** 证明 Kähler 度规的等价刻画。

**(b)** 计算 $\mathbb{P}^n$ 的 Fubini-Study 度规的曲率。

**(c)** 证明 Kähler 流形的 Hodge 分解。

## 解答

### (a) Kähler 度规的等价刻画

**设定**：设 $(M, J)$ 是近复流形（almost complex manifold），$\dim_{\mathbb{C}} M = n$。$g$ 是 $J$-不变 Riemann 度规，即 $g(JX, JY) = g(X, Y)$。定义基本 2-形式（fundamental form）：
$$\omega(X, Y) = g(JX, Y)$$

**定理（Kähler 条件等价刻画）**：以下等价：
1. $d\omega = 0$（$\omega$ 是闭形式）
2. $\nabla J = 0$（复结构关于 Levi-Civita 联络平行）
3. 局部存在光滑实函数 $\varphi$（Kähler 势），使得 $\omega = i\partial\bar{\partial}\varphi$
4. Levi-Civita 联络与 Cauchy-Riemann 算子相容：在局部全纯坐标下，$\Gamma^k_{ij} = \Gamma^k_{ji}$ 且仅对全纯指标有非零 Christoffel 符号

**证明**：

**(1) $\Leftrightarrow$ (2)**：计算 $d\omega$ 的显式公式。对向量场 $X, Y, Z$：
$$d\omega(X, Y, Z) = X\omega(Y, Z) - Y\omega(X, Z) + Z\omega(X, Y) - \omega([X, Y], Z) + \omega([X, Z], Y) - \omega([Y, Z], X)$$

利用 $g$ 的 Levi-Civita 联络和 $J$-不变性，可得（Kähler 恒等式）：
$$d\omega(X, Y, Z) = 2g((\nabla_X J)Y, Z)$$

因此 $d\omega = 0 \iff \nabla J = 0$。

**(2) $\Rightarrow$ (3)**：设 $\nabla J = 0$。在任意点 $p$ 附近取法坐标（normal coordinates），使得联络系数在 $p$ 为零。由 $\nabla J = 0$，$J$ 在该坐标系下为常值。于是 $g$ 在 $p$ 附近可写成 Hermitian 度量的标准形式。利用 $d\omega = 0$ 和 Poincaré 引理的复版本（$\partial\bar{\partial}$-引理），局部存在 $\varphi$ 使得 $\omega = i\partial\bar{\partial}\varphi$。

**(3) $\Rightarrow$ (1)**：直接计算：
$$d\omega = d(i\partial\bar{\partial}\varphi) = i(\partial + \bar{\partial})(\partial\bar{\partial}\varphi) = i(\partial^2\bar{\partial}\varphi - \partial\bar{\partial}^2\varphi) = 0$$
因 $\partial^2 = \bar{\partial}^2 = 0$。

**定义**：满足上述任一条件的度规称为 **Kähler 度规**，$(M, g, J)$ 称为 **Kähler 流形**。

### (b) Fubini-Study 度规的曲率

**定义**：在 $\mathbb{C}P^n$ 上，设 $[z_0 : z_1 : \cdots : z_n]$ 是齐次坐标。在仿射卡 $U_0 = \{z_0 \neq 0\}$ 上，令 $w_j = z_j/z_0$。Fubini-Study 度规的 Kähler 形式为：
$$\omega_{FS} = \frac{i}{2\pi} \partial\bar{\partial} \log(1 + |w|^2) = \frac{i}{2\pi} \partial\bar{\partial} \log(|z_0|^2 + \cdots + |z_n|^2)$$

**命题**：$\omega_{FS}$ 是整体定义的 Kähler 形式，且满足 $[\omega_{FS}] = c_1(\mathcal{O}(1)) \in H^2(\mathbb{C}P^n, \mathbb{Z})$。

**曲率计算**：

在 $U_0$ 上，记 $\rho = 1 + |w|^2 = 1 + \sum_{j=1}^n |w_j|^2$。计算：
$$\partial\bar{\partial}\log\rho = \partial\left(\frac{\sum_k w_k d\bar{w}_k}{\rho}\right) = \frac{\sum_j dw_j \wedge d\bar{w}_j}{\rho} - \frac{(\sum_j w_j d\bar{w}_j) \wedge (\sum_k \bar{w}_k dw_k)}{\rho^2}$$

即：
$$\omega_{FS} = \frac{i}{2\pi\rho^2}\left(\rho \sum_j dw_j \wedge d\bar{w}_j - \sum_{j,k} w_j \bar{w}_k dw_k \wedge d\bar{w}_j\right)$$

**定理**：$(\mathbb{C}P^n, \omega_{FS})$ 具有常全纯截面曲率 $K = 1$。

*证明*：在点 $[1:0:\cdots:0]$（即 $w = 0$）处，$\rho = 1$，度规矩阵为：
$$g_{j\bar{k}} = \frac{1}{2\pi}\delta_{jk}$$

曲率张量在该点的全纯分量由标准公式给出。对 Kähler 流形，Riemann 曲率张量的 $(1,1)$-部分为：
$$R_{j\bar{k}l\bar{m}} = -\frac{\partial^2 g_{j\bar{k}}}{\partial w_l \partial \bar{w}_m} + g^{p\bar{q}} \frac{\partial g_{j\bar{q}}}{\partial w_l} \frac{\partial g_{p\bar{k}}}{\partial \bar{w}_m}$$

对 $g_{j\bar{k}} = \frac{1}{2\pi}\left(\frac{\delta_{jk}}{\rho} - \frac{\bar{w}_j w_k}{\rho^2}\right)$，在 $w = 0$ 处直接计算得：
$$R_{j\bar{k}l\bar{m}}(0) = \frac{1}{2\pi}(\delta_{jl}\delta_{km} + \delta_{jm}\delta_{kl})$$

全纯截面曲率（对单位向量 $v$）：
$$K(v) = \frac{R(v, \bar{v}, v, \bar{v})}{g(v, \bar{v})^2} = \frac{2\cdot (2\pi)^{-1} |v|^4}{((2\pi)^{-1}|v|^2)^2} = 1$$

由 $U(n+1)$ 的传递性，$K = 1$ 处处成立。∎

**推论**：$\mathbb{C}P^n$ 的 Ricci 曲率满足 $\text{Ric}(\omega_{FS}) = (n+1)\omega_{FS}$，即 Fubini-Study 度规是 Kähler-Einstein 度规。

### (c) Kähler 流形的 Hodge 分解

**定理（Hodge 分解定理）**：设 $(M, \omega)$ 是紧 Kähler 流形。则对每个 $k$，复 de Rham 上同调有直和分解：
$$H^k(M, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(M)$$

其中 $H^{p,q}(M) = H^q(M, \Omega^p)$ 是 Dolbeault 上同调，且满足 Hodge 对称性：
$$H^{p,q}(M) = \overline{H^{q,p}(M)}$$

**证明**：

**步骤 1：Laplace 算子的比较**

对 Kähler 流形，de Rham Laplacian $\Delta_d = dd^* + d^*d$ 与 Dolbeault Laplacians 满足关键恒等式（Kähler identities）：
$$\Delta_d = 2\Delta_\partial = 2\Delta_{\bar{\partial}}$$

这意味着 harmonic $k$-形式恰好是 $(p,q)$-型 harmonic 形式的直和。

**步骤 2：$(p,q)$-分解**

由 Hodge 理论，$H^k_{dR}(M, \mathbb{C}) \cong \mathcal{H}^k(M)$（harmonic 形式空间）。若 $\alpha \in \mathcal{H}^k$，写 $\alpha = \sum_{p+q=k} \alpha^{p,q}$。由 Kähler 恒等式，$\Delta_d \alpha = 0 \iff \Delta_{\bar{\partial}}\alpha^{p,q} = 0$ 对所有 $(p,q)$ 成立。故：
$$\mathcal{H}^k = \bigoplus_{p+q=k} \mathcal{H}^{p,q}$$
其中 $\mathcal{H}^{p,q}$ 是 $(p,q)$-型 harmonic 形式。

**步骤 3：Dolbeault 同构**

由 Dolbeault 定理，$\mathcal{H}^{p,q} \cong H^{p,q}_{\bar{\partial}}(M) \cong H^q(M, \Omega^p)$。

**步骤 4：Hodge 对称性**

复共轭给出映射 $\overline{\cdot}: \mathcal{H}^{p,q} \to \mathcal{H}^{q,p}$，因 $\overline{\Delta_{\bar{\partial}}\alpha} = \Delta_\partial\bar{\alpha} = \Delta_{\bar{\partial}}\bar{\alpha}$（在 Kähler 情形）。这是同构，故 $\dim H^{p,q} = \dim H^{q,p}$。

**推论**：
- Hodge 数 $h^{p,q} = \dim H^{p,q}$ 满足 $h^{p,q} = h^{q,p} = h^{n-p,n-q}$（Serre 对偶）。
- Betti 数 $b_k = \sum_{p+q=k} h^{p,q}$。
- 奇数维 Betti 数 $b_{2k+1}$ 是偶数。

**常见错误**：
- 将 Hodge 定理应用于非 Kähler 复流形：如 Hopf 曲面 $S^1 \times S^3$ 是复流形但非 Kähler（$b_1 = 1$ 是奇数），Hodge 分解不成立。
- 混淆 $H^{p,q}$ 与 $H^q(M, \Omega^p)$：在非紧或非 Kähler 情形两者不等价。

**参考文献**：
- W. V. D. Hodge, *The Theory and Applications of Harmonic Integrals*, 1941
- P. Griffiths, J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978
- A. Moroianu, *Lectures on Kähler Geometry*, Cambridge, 2007
- D. Huybrechts, *Complex Geometry*, Springer, 2005
