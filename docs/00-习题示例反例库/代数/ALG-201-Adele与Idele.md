---
msc_primary: 00A99
习题编号: ALG-201
学科: 代数
知识点: 代数数论-Adele
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Adele 与 Idele

## 题目

**(a)** 定义 Adele 环 $A_K$ 和 Idele 群 $I_K$，证明其拓扑性质。

**(b)** 证明强逼近定理。

**(c)** 讨论 Tate 关于 $\zeta$ 函数的论文及adelic方法。

---

## 解答

### (a) Adele环与Idele群

#### 局部域

设 $K$ 是数域（$[K:\mathbb{Q}] < \infty$）。

**位**（place）：$K$ 的完备化：
- **无穷位**：$K_v = \mathbb{R}$ 或 $\mathbb{C}$（由 $K \to \mathbb{C}$ 的实/复嵌入诱导）
- **有限位**：$K_v$ 是 $p$-adic域（由素理想 $\mathfrak{p} \subseteq \mathcal{O}_K$ 诱导）

#### Adele环

**定义**：$A_K = \prod'_v K_v$（**限制积**）。

元 $(x_v)_v$ 属于 $A_K$ 当且仅当：对几乎所有有限位 $v$，$x_v \in \mathcal{O}_v$（$\mathcal{O}_v$ 是 $K_v$ 的整数环）。

**拓扑**：限制积拓扑。基开集：
$$\prod_{v \in S} U_v \times \prod_{v \notin S} \mathcal{O}_v$$

其中 $S$ 是有限位集，$U_v \subseteq K_v$ 开。

#### Idele群

**定义**：$I_K = A_K^\times = \prod'_v K_v^\times$。

元 $(x_v)_v$ 属于 $I_K$ 当且仅当：对几乎所有 $v$，$x_v \in \mathcal{O}_v^\times$。

**范数**：$|x| = \prod_v |x_v|_v$（idele范数）。

#### 对角嵌入

$K$ 对角嵌入 $A_K$：
$$x \mapsto (x, x, x, \ldots)$$

**定理**：$K$ 在 $A_K$ 中离散，$A_K/K$ 紧。

**证明**：
- 离散性：$K \cap \prod_v \mathcal{O}_v = \mathcal{O}_K$（有限集），而 $\prod_v \mathcal{O}_v$ 是 $A_K$ 中0的邻域。
- 紧性：用Minkowski定理。$A_K/K$ 的fundamental domain 有有限测度。

#### $K^\times$ 在 $I_K$ 中

**定理**：$K^\times$ 在 $I_K$ 中离散，$I_K^1/K^\times$ 紧。

其中 $I_K^1 = \{x \in I_K : |x| = 1\}$。

---

### (b) 强逼近定理

#### 陈述

**定理**：设 $G$ 是 $K$ 上单连通半单代数群。则 $G(K)$ 在 $G(A_K^S)$ 中稠密。

其中 $S$ 是包含所有无穷位的有限位集，$A_K^S = \prod'_{v \notin S} K_v$。

#### 对 $SL_n$ 的证明

**定理**：$SL_n(K)$ 在 $SL_n(A_K)$ 中稠密。

**证明概要**：

**步骤1**：对 $n = 2$。

需证：对任意有限位集 $S$ 和 $g_v \in SL_2(K_v)$（$v \in S$），存在 $g \in SL_2(K)$ 使得 $g \approx g_v$（$v \in S$）且 $g \in SL_2(\mathcal{O}_v)$（$v \notin S$）。

**步骤2**：用 Chinese Remainder Theorem。

对 $v \in S$，$g_v = \begin{pmatrix} a_v & b_v \\ c_v & d_v \end{pmatrix}$，$a_v d_v - b_v c_v = 1$。

找 $a, b, c, d \in K$ 使得 $a \equiv a_v, b \equiv b_v, c \equiv c_v, d \equiv d_v \pmod{\mathfrak{p}_v^{n_v}}$（$v \in S$）。

且 $a, b, c, d \in \mathcal{O}_v$（$v \notin S$）。

由CRT，这有解。

**步骤3**：调整使 $ad - bc = 1$。

若 $ad - bc = u \neq 1$，用 $S$ 外的位调整。

由Dirichlet单位定理或Hilbert符号理论，可以找到适当的调整。

$\square$

#### 应用

- **类域论**：idele类群 $I_K/K^\times$ 是Galois群
- **算术群**：$SL_n(\mathcal{O}_K)$ 是 $SL_n(K)$ 的离散子群
- **自守形式**：adelic自守形式 = 所有局部自守表示的张量积

---

### (c) Tate的论文

#### Tate的博士论文（1950）

Tate在论文中重新证明了Hecke的**函数方程**，用adelic方法统一了所有局部理论。

#### Dedekind $\zeta$ 函数的adelic表达

$$\zeta_K(s) = \sum_{\mathfrak{a}} \frac{1}{N(\mathfrak{a})^s} = \prod_{\mathfrak{p}} \frac{1}{1 - N(\mathfrak{p})^{-s}}$$

**Tate的方法**：

对 idele $x = (x_v)$，定义**adelic theta函数**：
$$\Theta(x) = \sum_{\alpha \in K} e^{2\pi i \Lambda(\alpha x)}$$

其中 $\Lambda$ 是adele上的canonical additive character。

#### Poisson求和公式

**定理**：对 Schwartz-Bruhat 函数 $f \in \mathcal{S}(A_K)$：
$$\sum_{\alpha \in K} f(\alpha) = \sum_{\alpha \in K} \hat{f}(\alpha)$$

其中 $\hat{f}$ 是adelic Fourier变换。

#### 函数方程

设 $Z(f, s) = \int_{I_K} f(x) |x|^s d^\times x$。

由Poisson求和：
$$Z(f, s) = Z(\hat{f}, 1-s) + \text{(解析项)}$$

这给出 $\zeta_K(s)$ 的解析延拓和函数方程：
$$\xi_K(s) = |d_K|^{s/2} \pi^{-r_1 s/2} (2\pi)^{-r_2 s} \Gamma(s/2)^{r_1} \Gamma(s)^{r_2} \zeta_K(s)$$

$$\xi_K(s) = \xi_K(1-s)$$

#### 现代发展

- **Langlands纲领**：自守L-函数的adelic定义
- **Drinfeld**：函数域上的Langlands对应
- **Wiles**：Fermat大定理的证明中用Hecke代数和adelic方法