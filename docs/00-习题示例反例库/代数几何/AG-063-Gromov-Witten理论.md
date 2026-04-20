---
msc_primary: 00A99
习题编号: AG-063
学科: 代数几何
知识点: 代数几何-GW理论
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Gromov-Witten 理论

## 题目

**(a)** 证明 WDVV 方程（Witten-Dijkgraaf-Verlinde-Verlinde）的几何来源。

**(b)** 讨论 Frobenius 流形结构与量子上同调。

**(c)** 证明 Virasoro 约束及其在枚举几何中的应用。

## 解答

### (a) WDVV 方程的几何来源

**GW 不变量的定义**：设 $(X, \omega)$ 是紧辛流形（或光滑射影簇），$\beta \in H_2(X, \mathbb{Z})$。对 $g \geq 0$，$n \geq 0$，考虑稳定映射模空间 $\overline{M}_{g,n}(X, \beta)$，参数化从 $n$-标记 genus $g$ 稳定曲线到 $X$ 的度 $\beta$ 映射。

**评估映射**：
$$ev_i: \overline{M}_{g,n}(X, \beta) \to X, \quad [f: C \to X; p_1, \ldots, p_n] \mapsto f(p_i)$$

**GW 不变量**：对 $\gamma_1, \ldots, \gamma_n \in H^*(X)$，定义：
$$\langle \gamma_1, \ldots, \gamma_n \rangle_{g,\beta} = \int_{[\overline{M}_{g,n}(X, \beta)]^{vir}} \bigcup_{i=1}^n ev_i^*\gamma_i$$

其中 $[\overline{M}_{g,n}(X, \beta)]^{vir}$ 是虚拟基本类（virtual fundamental class），维数为：
$$\dim^{vir} = (\dim X - 3)(1-g) + c_1(X) \cdot \beta + n$$

**Genus 0 GW 势**：设 $\{T_0 = 1, T_1, \ldots, T_m\}$ 是 $H^*(X)$ 的齐次基，$g_{ab} = \int_X T_a \smile T_b$ 是相交矩阵。令 $\gamma = \sum_{i=0}^m x_i T_i$。

$$\Phi(x) = \sum_{n \geq 3} \sum_{\beta \in H_2(X)} \frac{1}{n!}\langle \gamma^{\otimes n} \rangle_{0,\beta} \cdot q^\beta$$

其中 $q^\beta = \exp(2\pi i \int_\beta \omega)$（在 Novikov 环中）。

**量子上同调（Quantum Cohomology）**：在 $H^*(X)$ 上定义 **量子积** $*$：
$$T_a * T_b = \sum_{c,d} \Phi_{abc} g^{cd} T_d$$

其中 $\Phi_{abc} = \frac{\partial^3 \Phi}{\partial x_a \partial x_b \partial x_c}$，$(g^{cd})$ 是 $(g_{ab})$ 的逆矩阵。

**WDVV 方程**：量子积的结合性 $(T_a * T_b) * T_c = T_a * (T_b * T_c)$ 等价于 $\Phi$ 满足：
$$\sum_{e,f} \Phi_{abe} g^{ef} \Phi_{fcd} = \sum_{e,f} \Phi_{ace} g^{ef} \Phi_{fbd}$$

对所有指标 $a, b, c, d$。

**几何证明**：

考虑 forgetful 映射 $ft: \overline{M}_{0,n}(X, \beta) \to \overline{M}_{0,4} \cong \mathbb{P}^1$。当 $n \geq 4$，固定前 4 个标记点，剩余 $n-4$ 个由 $ft$ 遗忘。

在 $\overline{M}_{0,4} \cong \mathbb{P}^1$ 上，边界除子有两种类型：
- $D(12|34)$：曲线分裂为两分量，$\{1,2\}$ 在一支，$\{3,4\}$ 在另一支
- $D(13|24)$：$\{1,3\}$ 在一支，$\{2,4\}$ 在另一支
- $D(14|23)$：$\{1,4\}$ 在一支，$\{2,3\}$ 在另一支

**关键事实**：$D(12|34) \sim D(13|24) \sim D(14|23)$ 在 $\overline{M}_{0,4}$ 上线性等价（均为点）。

将 $ev_1^*T_a \smile ev_2^*T_b \smile ev_3^*T_c \smile ev_4^*T_d$ 在 $ft^*D(12|34)$ 和 $ft^*D(13|24)$ 上积分，由拉回保持线性等价，两者相等。

左边给出 $\sum_{e,f} \Phi_{abe}g^{ef}\Phi_{fcd}$（中间插入态 $T_e, T_f$ 作完备和），右边给出 $\sum_{e,f} \Phi_{ace}g^{ef}\Phi_{fbd}$。此即 WDVV。

### (b) Frobenius 流形与量子上同调

**定义（Frobenius 流形，Dubrovin）**：流形 $M$ 上装备：

1. **平坦度规**（metric）$g$: $TM$ 上的非退化对称双线性形式，存在平坦坐标 $\{t^i\}$ 使 $g(\partial_i, \partial_j) = g_{ij}$ 为常数。

2. **Frobenius 积** $*$: $TM$ 上交换结合积，满足：
   $$g(X * Y, Z) = g(Y, X * Z)$$（对称性/Frobenius 条件）
   
3. **单位向量场** $e$: $e * X = X$，且 $e = \partial_{t^0}$ 在平坦坐标下。

4. **Euler 向量场** $E$: 给出标度变换，使 $g$ 和 $*$ 有特定齐次性。

**定理（Dubrovin）**：Frobenius 流形等价于满足 WDVV 方程的函数 $\Phi$（前势，prepotential），模去坐标的仿射变换。

*证明*：给定 $\Phi$，定义 $g_{ab}$（常数矩阵）和 $c_{abc} = \partial_a\partial_b\partial_c \Phi$。令 $c^a_{bc} = \sum_d g^{ad}c_{dbc}$。则 $(c^a_{bc})$ 定义结合积 $*$。WDVV 正是 $*$ 的结合性。Frobenius 条件由 $c_{abc}$ 对指标的对称性自动满足。

**量子上同调作为 Frobenius 流形**：$M = H^*(X, \mathbb{C})$，坐标 $\{x_i\}$。经典上同调的杯积是 $*$ 在 $q = 0$ 的极限。量子积 $*$ 由 GW 不变量给出，使 $(H^*(X), g, *)$ 成为 Frobenius 流形。

**例子：$X = \mathbb{P}^n$**

$H^*(\mathbb{P}^n) = \mathbb{C}[h]/(h^{n+1})$，$h = c_1(\mathcal{O}(1))$。经典积：$h^i \cup h^j = h^{i+j}$（$i+j \leq n$），$h^{n+1} = 0$。

量子上同调：引入 Novikov 参数 $q$。GW 不变量计算给出：
$$h * h^i = \begin{cases} h^{i+1} & 0 \leq i < n \\ q & i = n \end{cases}$$

即 $h^{*(n+1)} = q$。这是量子上同调环的表示：
$$QH^*(\mathbb{P}^n) \cong \mathbb{C}[h, q]/(h^{n+1} - q)$$

经典极限 $q \to 0$ 恢复 $h^{n+1} = 0$。

### (c) Virasoro 约束

**Virasoro 代数**：Lie 代数，生成元 $\{L_n\}_{n \in \mathbb{Z}}$，满足：
$$[L_m, L_n] = (m-n)L_{m+n} + \frac{c}{12}(m^3-m)\delta_{m+n,0}$$
其中 $c$ 是中心荷（central charge）。

**GW 的生成函数**：定义总生成函数：
$$Z_X(t_0, t_1, \ldots) = \exp\left(\sum_{g \geq 0} \sum_{n \geq 0} \sum_{\beta} \frac{1}{n!}\langle \tau_{d_1}\gamma_1, \ldots, \tau_{d_n}\gamma_n \rangle_{g,\beta} \prod_{i=1}^n t_{d_i}^{\gamma_i}\right)$$

其中 $\tau_d\gamma$ 表示在标记点处插入 $\psi$ 类的 $d$-次幂和 $ev^*\gamma$。

**Virasoro 约束（Witten 猜想，Givental 证明）**：

**定理**：$Z_X$ 满足 Virasoro 约束：$L_n Z_X = 0$ 对 $n \geq -1$。

其中 $L_n$ 是用 $t_k$ 和 $\partial/\partial t_k$ 表示的微分算子。

**物理起源**：2D 拓扑引力中，$L_n$ 是模空间 $\overline{M}_{g,n}$ 上的 Beltrami 微分算子。约束 $L_n Z = 0$（$n \geq -1$）对应弦方程（$L_{-1}$）、dilaton 方程（$L_0$）和高亏格的推广。

**弦方程（$L_{-1}$）**：
$$\langle \tau_0 \prod_{i=1}^n \tau_{d_i} \rangle_g = \sum_{j=1}^n \langle \tau_{d_j-1} \prod_{i \neq j} \tau_{d_i} \rangle_g$$

其中 $\tau_0 = 1$ 对应插入 $1 \in H^*(X)$。

**Dilaton 方程（$L_0$）**：
$$\langle \tau_1 \prod_{i=1}^n \tau_{d_i} \rangle_g = (2g-2+n) \langle \prod_{i=1}^n \tau_{d_i} \rangle_g$$

**Kontsevich 的证明（$X = pt$）**：Kontsevich（1992）将 $Z_{pt}$ 与矩阵模型联系，利用 Feynman 图展开证明 Virasoro 约束。他的方法将 $\overline{M}_{g,n}$ 的组合结构与ribbon graph 的枚举联系起来。

**Givental 的形式化**：对任意 $X$，Givental 用 Lagrangian 锥的量化证明 Virasoro 约束。核心观察是 GW 理论的 ancestor potential 满足无穷小辛变换下的等变性，这等价于 Virasoro 约束。

**常见错误**：
- **WDVV 的指标对称性**：方程对 $(b, c)$ 对称，但对 $(a, d)$ 不对称（在等式两边位置不同）。需特别注意指标位置。
- **量子积的交换性**：$T_a * T_b = T_b * T_a$ 由 genus 0 三点函数的交换性（$\overline{M}_{0,3}$ 是点）自动成立。但结合性是非平凡的，由 WDVV 编码。
- **Virasoro 的 $n < -1$**：$L_n$ 对 $n < -1$ 一般不作用于 $Z_X$ 为零。仅 $n \geq -1$ 的约束成立。

**参考文献**：
- M. Kontsevich, Yu. Manin, "Gromov-Witten classes, quantum cohomology, and enumerative geometry", *Comm. Math. Phys.* 1994
- B. Dubrovin, "Geometry of 2D topological field theories", *Springer LNM* 1996
- A. Givental, "Gromov-Witten invariants and quantization of quadratic Hamiltonians", *Mosc. Math. J.* 2001
- E. Witten, "Two-dimensional gravity and intersection theory on moduli space", *Surv. Diff. Geom.* 1991
