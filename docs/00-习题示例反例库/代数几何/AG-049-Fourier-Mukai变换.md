---
msc_primary: 00A99
习题编号: AG-049
学科: 代数几何
知识点: 代数几何-Fourier-Mukai
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Fourier-Mukai 变换

## 题目

**(a)** 定义 Fourier-Mukai 变换并证明其是等价的条件。

**(b)** 证明椭圆曲线的 FM 对偶。

**(c)** 讨论 K3 曲面的 FM 伙伴。

## 解答

### (a) Fourier-Mukai 变换的定义与等价条件

**定义**：设 $X, Y$ 是光滑射影簇，$p_X: X \times Y \to X$ 和 $p_Y: X \times Y \to Y$ 是投影。对对象 $E \in D^b(\text{Coh}(X \times Y))$（有界导出范畴），**Fourier-Mukai 变换** 定义为函子：
$$\Phi_E: D^b(X) \to D^b(Y), \quad F \mapsto Rp_{Y*}(E \otimes^L Lp_X^* F)$$

其中 $\otimes^L$ 是导出张量积，$Lp_X^*$ 是导出拉回，$Rp_{Y*}$ 是导出推进。

**例子**：
- **恒等函子**：$E = \mathcal{O}_{\Delta_X}$，$\Delta_X \subset X \times X$ 是对角线。此时 $\Phi_{\mathcal{O}_{\Delta_X}} \cong \text{id}_{D^b(X)}$。
- **推进与拉回**：若 $f: X \to Y$，则 $Rf_* = \Phi_{\mathcal{O}_{\Gamma_f}}$，$Lf^* = \Phi_{\mathcal{O}_{\Gamma_f}[\dim X - \dim Y]}$（需适当调整），其中 $\Gamma_f$ 是图像。
- **张量与平移**：$E = L \boxtimes M$（外张量积）给出特定类型的变换。

**定理（Orlov, 1997）**：设 $X, Y$ 是光滑射影簇，$F: D^b(X) \to D^b(Y)$ 是完全忠实且保持适当性质的三角函子。则存在 $E \in D^b(X \times Y)$（在同构意义下唯一）使得 $F \cong \Phi_E$。

**完全忠实性的判别**：设 $E \in D^b(X \times Y)$，则 $\Phi_E$ 完全忠实当且仅当对所有 $x, x' \in X$：
$$\text{Hom}_{D^b(Y)}(\Phi_E(\mathcal{O}_x), \Phi_E(\mathcal{O}_{x'}[i])) \cong \begin{cases} \mathbb{C} & x = x', i = 0 \\ 0 & \text{otherwise} \end{cases}$$

其中 $\mathcal{O}_x$ 是点 $x$ 的结构层（skyscraper sheaf）。

**等价性判别（Bondal-Orlov）**：若 $X$ 是光滑射影簇且 $K_X$ 或 $-K_X$ 是 ample（即 $X$ 是 Fano 或 anti-Fano），则任何等价 $D^b(X) \cong D^b(Y)$ 推出 $X \cong Y$。

对于一般情形，$\Phi_E$ 是等价当且仅当：
1. 完全忠实（如上判别）
2. $E$ 的右正交补 $E^\perp = \{F \in D^b(Y) : \text{Hom}(\Phi_E(G), F) = 0, \forall G\}$ 为零

### (b) 椭圆曲线的 Fourier-Mukai 对偶

**设定**：设 $E$ 是椭圆曲线（亏格 1 的复射影曲线，带群结构）。其对偶椭圆曲线定义为 $\hat{E} = \text{Pic}^0(E)$，即度数为 0 的可逆层（线丛）的模空间。

**Poincaré 丛**：存在万有线丛 $\mathcal{P}$ 在 $E \times \hat{E}$ 上，满足：
- 对 $p \in \hat{E}$（对应 $L_p \in \text{Pic}^0(E)$），$\mathcal{P}|_{E \times \{p\}} \cong L_p$
- 对 $x \in E$，$\mathcal{P}|_{\{x\} \times \hat{E}} \cong$ 与 $x$ 相关的特定线丛（在 $\hat{E}$ 上）

**定理（Mukai, 1981）**：Fourier-Mukai 变换
$$\Phi_{\mathcal{P}}: D^b(E) \to D^b(\hat{E})$$
是范畴等价。且 $\Phi_{\hat{\mathcal{P}}} \circ \Phi_{\mathcal{P}} \cong [-1] \circ i^*$，其中 $i: E \to \hat{\hat{E}} \cong E$ 是自然同构（否定映射）。

**证明要点**：

**步骤 1**：计算 $\Phi_{\mathcal{P}}(\mathcal{O}_x)$。由定义：
$$\Phi_{\mathcal{P}}(\mathcal{O}_x) = Rp_{\hat{E}*}(\mathcal{P} \otimes p_E^* \mathcal{O}_x)$$
由于 $p_E^* \mathcal{O}_x = \mathcal{O}_{\{x\} \times \hat{E}}$，且 $\mathcal{P}|_{\{x\} \times \hat{E}}$ 是 $\hat{E}$ 上的线丛 $L_x$，故：
$$\Phi_{\mathcal{P}}(\mathcal{O}_x) = L_x$$
（作为 $\hat{E}$ 上的线丛，即点层被送到线丛）

**步骤 2**：验证完全忠实条件。对 $x, y \in E$：
$$\text{Hom}(L_x, L_y[i]) = H^i(\hat{E}, L_y \otimes L_x^{-1}) = H^i(\hat{E}, L_{y-x})$$
由椭圆曲线的上同调计算，这是 $\mathbb{C}$ 当 $x = y, i = 0$；否则当 $y \neq x$ 时 $L_{y-x}$ 是非平凡线丛，故 $H^0 = H^1 = 0$。

**步骤 3**：证明本质满性。由于 $E$ 和 $\hat{E}$ 都是曲线，$D^b$ 由 sheaf 复形生成。利用 $\Phi_{\mathcal{P}}$ 保持 hearts 的性质和 Atiyah 关于椭圆曲线上的向量丛分类，可证明每个不可分解层都在像中。

**经典 Fourier 变换的类比**：若将 $E \cong \mathbb{C}/\Lambda$ 参数化，$\hat{E} \cong \mathbb{C}/\Lambda^*$，则 $\Phi_{\mathcal{P}}$ 在 $L^2$ 层面退化为经典 Fourier 级数变换，解释了"Fourier-Mukai"名称的由来。

### (c) K3 曲面的 Fourier-Mukai 伙伴

**定义**：两个 K3 曲面 $X, Y$ 称为 **Fourier-Mukai 伙伴**（FM-partners），若存在等价 $D^b(X) \cong D^b(Y)$。

**定理（Orlov, 1997）**：对 K3 曲面 $X, Y$，以下条件等价：
1. $D^b(X) \cong D^b(Y)$（导出等价）
2. 存在 Hodge 等距（Hodge isometry）$H^2(X, \mathbb{Z}) \cong H^2(Y, \mathbb{Z})$ 保持相交形式和 Hodge 结构
3. $Y$ 是 $X$ 的某个 moduli space 的紧致化（对适当选取的 Mukai 向量）

**证明概要**：

**$(1) \Rightarrow (2)$**：导出等价诱导在 Mukai 格（Mukai lattice）上的等距：
$$\tilde{H}(X, \mathbb{Z}) = H^0(X, \mathbb{Z}) \oplus H^2(X, \mathbb{Z}) \oplus H^4(X, \mathbb{Z})$$
带 Mukai 配对 $(r, l, s) \cdot (r', l', s') = l \cdot l' - rs' - r's$。

若 $\Phi: D^b(X) \to D^b(Y)$ 是等价，则诱导的映射 $\Phi^H: \tilde{H}(X) \to \tilde{H}(Y)$ 是 Hodge 等距。限制到 $H^2$ 上（经适当调整）给出所需等距。

**$(2) \Rightarrow (3)$**：由 Torelli 定理的扩展，Hodge 等距可通过 moduli space 的构造实现。具体地，取原始 Mukai 向量 $v = (r, l, s)$ 满足 $v^2 = 0$，考虑 $X$ 上稳定层的模空间 $M_X(v)$，它是另一个 K3 曲面 $Y$，且 $D^b(X) \cong D^b(Y)$。

**$(3) \Rightarrow (1)$**：Mukai 证明了 universal sheaf 在 $X \times M_X(v)$ 上诱导 Fourier-Mukai 等价。

**计数结果**：对一般 K3 曲面 $X$，FM 伙伴的个数有限。具体公式（Hloybrechts-Stellari）：
$$|\{Y : D^b(Y) \cong D^b(X)\}| = 2^{\tau(N) - 1}$$
其中 $N$ 与判别式群有关，$\tau(N)$ 是 $N$ 的不同素因子个数。

**常见错误**：
- 误认为导出等价推出簇同构：反例是上面 K3 曲面的 FM 伙伴。
- 忽视 heart 的变换：导出等价一般不保持 standard heart $Coh(X)$，而是给出不同的 t-结构。

**参考文献**：
- S. Mukai, "Duality between $D(X)$ and $D(\hat{X})$ with its application to Picard sheaves", *Nagoya Math. J.* 1981
- D. Orlov, "Equivalences of derived categories and K3 surfaces", *J. Math. Sci.* 1997
- A. Caldararu, "Derived categories of twisted sheaves on Calabi-Yau manifolds", PhD thesis, 2000
- D. Huybrechts, *Fourier-Mukai Transforms in Algebraic Geometry*, Oxford, 2006
