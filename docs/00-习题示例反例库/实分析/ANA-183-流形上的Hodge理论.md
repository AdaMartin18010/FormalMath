---
msc_primary: 58
习题编号: ANA-183
学科: 微分几何
知识点: Hodge理论、Poincaré对偶、调和形式
难度: ⭐⭐⭐⭐⭐
预计时间: 90分钟
processed_at: '2026-04-20'
---

# 流形上的 Hodge 理论

## 题目

**(a)** 设 $(M, g)$ 为 $n$ 维紧定向 Riemann 流形。证明 Hodge 分解定理：
$$\Omega^k(M) = \mathcal{H}^k(M) \oplus d\Omega^{k-1}(M) \oplus d^*\Omega^{k+1}(M),$$
其中 $\mathcal{H}^k(M) = \ker \Delta \cap \Omega^k(M)$ 为 $k$-次调和形式空间，$\Delta = dd^* + d^*d$ 为 Hodge-Laplace 算子，$d^*$ 为外微分 $d$ 的形式伴随。

**(b)** 证明 Hodge 星算子 $*: \Omega^k(M) \to \Omega^{n-k}(M)$ 诱导 Poincaré 对偶同构
$$H^k_{\mathrm{dR}}(M) \cong H^{n-k}_{\mathrm{dR}}(M),$$
并在调和形式层面验证 $*: \mathcal{H}^k(M) \to \mathcal{H}^{n-k}(M)$ 为同构。

**(c)** 计算 $n$ 维平坦环面 $T^n = \mathbb{R}^n / \mathbb{Z}^n$ 的调和形式空间 $\mathcal{H}^k(T^n)$，并验证其维数等于二项式系数 $\binom{n}{k}$。

---

## 解答

### (a) Hodge 分解定理

**设定**：$(M, g)$ 为 $n$ 维紧定向 Riemann 流形。$k$-形式空间 $\Omega^k(M)$ 装备 $L^2$ 内积
$$(\alpha, \beta) = \int_M \alpha \wedge *\beta = \int_M \langle \alpha, \beta \rangle_g \, dV_g.$$

外微分 $d: \Omega^k \to \Omega^{k+1}$ 的形式伴随 $d^*: \Omega^{k+1} \to \Omega^k$ 由
$$(d\alpha, \beta) = (\alpha, d^*\beta), \quad \forall \alpha \in \Omega^k, \beta \in \Omega^{k+1}$$
唯一确定。由 Stokes 定理，$d^* = (-1)^{n(k+1)+1} * d *$ 在 $k+1$-形式上。

**Hodge-Laplace 算子**：
$$\Delta = dd^* + d^*d: \Omega^k(M) \longrightarrow \Omega^k(M).$$

**定理（Hodge 分解）**：
$$\Omega^k(M) = \mathcal{H}^k(M) \oplus d\Omega^{k-1}(M) \oplus d^*\Omega^{k+1}(M),$$
且三个子空间在内积 $(\cdot, \cdot)$ 下两两正交。

**证明**：

**步骤 1**：正交性。设 $\omega \in \mathcal{H}^k$，$d\alpha \in d\Omega^{k-1}$，$d^*\beta \in d^*\Omega^{k+1}$。

- $(\omega, d\alpha) = (d^*\omega, \alpha) = 0$，因 $\Delta\omega = 0 \implies d^*\omega = d\omega = 0$。
- $(\omega, d^*\beta) = (d\omega, \beta) = 0$。
- $(d\alpha, d^*\beta) = (d^2\alpha, \beta) = 0$。

**步骤 2**：证明 $\mathcal{H}^k = (d\Omega^{k-1} \oplus d^*\Omega^{k+1})^\perp$。

$\omega \perp d\Omega^{k-1}$ 且 $\omega \perp d^*\Omega^{k+1}$ 当且仅当 $d^*\omega = 0$ 且 $d\omega = 0$，当且仅当 $\Delta\omega = dd^*\omega + d^*d\omega = 0$，即 $\omega \in \mathcal{H}^k$。

**步骤 3**：椭圆正则性与紧性。$\Delta$ 是二阶椭圆微分算子。对紧流形，椭圆算子的基本定理（Gårding 不等式 + Rellich 紧性引理）保证：

- $\mathcal{H}^k(M)$ 是有限维的；
- $\Delta: \Omega^k(M) \to \Omega^k(M)$ 的像为闭子空间。

**步骤 4**：由 Hilbert 空间的正交分解，
$$\Omega^k = \overline{\mathrm{im}\,\Delta} \oplus \ker \Delta = \mathrm{im}\,\Delta \oplus \mathcal{H}^k,$$
因 $\mathrm{im}\,\Delta$ 闭。对任意 $\eta \in \Omega^k$，写 $\eta = \Delta\xi + h$，$h \in \mathcal{H}^k$。则
$$\eta = dd^*\xi + d^*d\xi + h = d\alpha + d^*\beta + h,$$
其中 $\alpha = d^*\xi$，$\beta = d\xi$。这给出所需的分解。 ∎

---

### (b) Poincaré 对偶与 Hodge 星

**Hodge 星算子**。由内积 $\langle \cdot, \cdot \rangle_g$ 和定向诱导的 Hodge 星 $*: \Omega^k \to \Omega^{n-k}$ 满足
$$\alpha \wedge *\beta = \langle \alpha, \beta \rangle_g \, dV_g, \quad \forall \alpha, \beta \in \Omega^k.$$

**性质**：$*^2 = (-1)^{k(n-k)}$ 于 $k$-形式上，$*$ 在内积意义下是等距（至多符号）。

**命题**：$d^* = (-1)^{n(k+1)+1} * d *$ 于 $\Omega^{k+1}$ 上，且 $*$ 与 $\Delta$ 交换：$*\Delta = \Delta *$。

**证明**：由 $d^*$ 的定义和 $*$ 的局部计算可得。具体地，对 $\alpha \in \Omega^k$，$\beta \in \Omega^{k+1}$：
$$(d\alpha, \beta) = \int d\alpha \wedge *\beta = (-1)^{k+1} \int \alpha \wedge d(*\beta) = (-1)^{k+1} (-1)^{k(n-k)} \int \alpha \wedge *(*d*\beta).$$

比较得 $d^*\beta = (-1)^{n(k+1)+1} * d * \beta$。进而
$$\Delta * = (dd^* + d^*d)* = d(*d* *) * + (*d* *)d * = \pm * d^* d \pm * d d^* = *\Delta.$$

符号细节由维数计算验证。 ∎

**定理（Poincaré 对偶）**。$*: \mathcal{H}^k(M) \to \mathcal{H}^{n-k}(M)$ 是同构，且诱导 de Rham 上同调的同构 $H^k_{\mathrm{dR}}(M) \cong H^{n-k}_{\mathrm{dR}}(M)$。

**证明**：

若 $\omega \in \mathcal{H}^k$，则 $\Delta(*\omega) = *\Delta\omega = 0$，故 $*\omega \in \mathcal{H}^{n-k}$。因 $*^2 = \pm \mathrm{id}$，$*$ 是双射。

对 de Rham 上同调，$H^k_{\mathrm{dR}}(M) \cong \mathcal{H}^k(M)$（Hodge 定理：每上同调类有唯一的调和代表）。Hodge 星将调和代表映到调和代表，且与恰当形式相容：
$$*(d\alpha) = \pm d^*(*\alpha) \in \mathrm{im}\,d^*$$
不是恰当形式，但在上同调层面 $*: H^k \to H^{n-k}$ 良定且为同构。实际上，利用 $H^k \cong \mathcal{H}^k$ 的典范同构，$*$ 直接给出所需对偶。

配对 $H^k \times H^{n-k} \to \mathbb{R}$，$([\alpha], [\beta]) \mapsto \int_M \alpha \wedge \beta$ 非退化：对 $[\alpha] \neq 0$，取调和代表 $\alpha \in \mathcal{H}^k$，则 $*\alpha \in \mathcal{H}^{n-k}$ 且
$$\int_M \alpha \wedge *\alpha = (\alpha, \alpha) > 0.$$
故 $([\alpha], [*\alpha]) \neq 0$，配对非退化。 ∎

---

### (c) 环面 $T^n$ 的调和形式

**设定**：$T^n = \mathbb{R}^n / \mathbb{Z}^n$ 具有平坦度量 $g = \sum_{i=1}^n dx_i \otimes dx_i$。

**命题**：$\mathcal{H}^k(T^n)$ 由常系数 $k$-形式张成：
$$\mathcal{H}^k(T^n) = \left\{ \sum_{1 \leq i_1 < \dots < i_k \leq n} c_{i_1 \dots i_k} \, dx_{i_1} \wedge \dots \wedge dx_{i_k} : c_{i_1 \dots i_k} \in \mathbb{R} \right\} \cong \Lambda^k(\mathbb{R}^n)^*.$$

**证明**：

在平坦度规下，Hodge-Laplace 算子在标准坐标下作用为分量形式的普通 Laplacian：
$$\Delta\left(\sum_I f_I \, dx_I\right) = \sum_I (\Delta_0 f_I) \, dx_I,$$
其中 $\Delta_0 = -\sum_{j=1}^n \frac{\partial^2}{\partial x_j^2}$（符号约定使 $-\partial^2$ 为正算子），$dx_I = dx_{i_1} \wedge \dots \wedge dx_{i_k}$。

设 $\omega = \sum_I f_I \, dx_I$ 为调和形式，则 $\Delta_0 f_I = 0$ 对所有 $I$。

将 $f_I$ 作 Fourier 展开：
$$f_I(x) = \sum_{m \in \mathbb{Z}^n} c_m e^{2\pi i m \cdot x}.$$

$\Delta_0 f_I = 0$ 意味着
$$\sum_m |2\pi m|^2 c_m e^{2\pi i m \cdot x} = 0 \implies c_m = 0 \text{ 对 } m \neq 0.$$

故 $f_I$ 为常数。因此调和形式恰为常系数 $k$-形式。

**维数**：常系数 $k$-形式空间的维数等于从 $n$ 个指标中选取 $k$ 个的组合数：
$$\dim \mathcal{H}^k(T^n) = \binom{n}{k}.$$

这与 Betti 数一致：$b_k(T^n) = \binom{n}{k}$，且由 Künneth 公式
$$H^*(T^n) = H^*(S^1)^{\otimes n} = \Lambda^*(\mathbb{R}^n)^*.$$

**验证 Hodge 星**：对标准基 $dx_I = dx_{i_1} \wedge \dots \wedge dx_{i_k}$，$*(dx_I) = \pm dx_{J}$，其中 $J$ 为 $I$ 在 $\{1, \dots, n\}$ 中的补集。这直接给出 $\mathcal{H}^k \cong \mathcal{H}^{n-k}$。 ∎

---

## 关键公式与定理速查

| 对象 | 公式/结果 | 说明 |
|------|----------|------|
| Hodge-Laplace | $\Delta = dd^* + d^*d$ | 椭圆算子 |
| Gårding 不等式 | $\|\omega\|_{H^1}^2 \leq C[(\Delta\omega, \omega) + \|\omega\|_{L^2}^2]$ | 椭圆正则性基础 |
| Betti 数 $b_k(T^n)$ | $\binom{n}{k}$ |  Künneth 公式 |
| Hodge 星平方 | $*^2 = (-1)^{k(n-k)}$ | 于 $k$-形式上 |

---

## 相关文档

- [de Rham 上同调](../几何与拓扑/de-Rham-上同调.md)
- [Riemann 几何基础](../几何与拓扑/Riemann几何-基础.md)
- [Kähler 流形](../几何与拓扑/Kähler流形-基础.md)
- [Poincaré 对偶](../几何与拓扑/Poincaré-对偶.md)
