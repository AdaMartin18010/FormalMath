---
msc_primary: 00A99
习题编号: GEO-048
学科: 几何
知识点: 指标定理-Dirac算子
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Dirac算子与指标

## 题目

**(a)** 定义Clifford代数和旋量表示。

**(b)** 证明Lichnerowicz公式：$D^2 = \nabla^*\nabla + \frac{1}{4}R$。

**(c)** 用Bochner技巧证明正标量曲率障碍。

---

## 解答

### (a) Clifford代数与旋量

#### Clifford代数的定义

设 $V$ 是实向量空间，$Q: V \to \mathbb{R}$ 是非退化二次型。

**Clifford代数**：
$$Cl(V, Q) = T(V) / \langle v \otimes v - Q(v) \cdot 1 \rangle$$

即：对所有 $v \in V$，$v^2 = Q(v)$。

等价关系：$v \cdot w + w \cdot v = 2\langle v, w \rangle$，其中 $\langle v, w \rangle = \frac{1}{2}(Q(v+w) - Q(v) - Q(w))$。

#### 例子

- $Cl(\mathbb{R}, -x^2) \cong \mathbb{C}$（$i^2 = -1$）
- $Cl(\mathbb{R}^2, -x^2-y^2) \cong \mathbb{H}$（四元数）
- $Cl(\mathbb{R}^{2n}, Q_{std}) \cong M_{2^n}(\mathbb{C})$（复矩阵代数）

#### 旋量群

**Pin群**：$Pin(V) = \{v_1 \cdots v_k \in Cl(V) : Q(v_i) = \pm 1\}$

**Spin群**：$Spin(V) = Pin(V) \cap Cl^{even}(V)$（偶次部分）

**覆盖映射**：$\rho: Spin(n) \to SO(n)$，$\rho(v)(x) = v x v^{-1}$，是2对1覆盖。

#### 旋量表示

对 $n = 2m$，$Cl(\mathbb{R}^{2m}) \otimes \mathbb{C} \cong M_{2^m}(\mathbb{C})$。

**旋量空间** $S = \mathbb{C}^{2^m}$ 是Clifford代数的不可约表示。

**手征分解**（$n$ 偶）：$S = S^+ \oplus S^-$，其中：
$$S^\pm = \{s \in S : \omega \cdot s = \pm s\}$$

$\omega = i^m e_1 \cdots e_{2m}$ 是**体积元**。

#### 旋量丛

对自旋流形 $M$（结构群可提升为 $Spin(n)$），定义**旋量丛**：
$$S(M) = P_{Spin} \times_\rho S$$

其中 $P_{Spin} \to M$ 是Spin主丛，$\rho: Spin(n) \to GL(S)$ 是旋量表示。

**手征旋量丛**：$S^\pm(M)$，截面称为**手征旋量场**（Weyl旋量）。

---

### (b) Lichnerowicz公式

#### Dirac算子

设 $M$ 是自旋流形，$S$ 是旋量丛。

**Dirac算子**：
$$D: \Gamma(S) \to \Gamma(S), \quad Ds = \sum_{i=1}^n e_i \cdot \nabla_{e_i}s$$

其中 $\{e_i\}$ 是局部正交标架，$\cdot$ 是Clifford乘法，$\nabla$ 是旋联络。

#### Lichnerowicz公式

**定理**（Lichnerowicz, 1963）：
$$D^2 = \nabla^*\nabla + \frac{1}{4}R$$

其中：
- $\nabla^*\nabla = -\sum_i \nabla_{e_i}\nabla_{e_i} + \nabla_{\nabla_{e_i}e_i}$（Bochner Laplacian，连接 Laplacian）
- $R$ 是标量曲率

#### 证明概要

**步骤1：局部计算**

$$D^2s = \sum_{i,j} e_i \cdot \nabla_{e_i}(e_j \cdot \nabla_{e_j}s)$$

$$= \sum_{i,j} e_i \cdot e_j \cdot \nabla_{e_i}\nabla_{e_j}s$$

（因为Clifford乘法与联络相容）

**步骤2：对称与反对称分解**

分 $i = j$ 和 $i \neq j$：
$$D^2s = \sum_i e_i^2 \cdot \nabla_{e_i}^2 s + \sum_{i \neq j} e_i e_j \nabla_{e_i}\nabla_{e_j}s$$

$e_i^2 = -1$（Riemann度量），故第一项 = $-\sum_i \nabla_{e_i}^2 s$。

对 $i \neq j$，分 $(i,j)$ 和 $(j,i)$：
$$\sum_{i < j} (e_i e_j \nabla_{e_i}\nabla_{e_j} + e_j e_i \nabla_{e_j}\nabla_{e_i})s$$

由 $e_j e_i = -e_i e_j$（$i \neq j$）：
$$= \sum_{i < j} e_i e_j (\nabla_{e_i}\nabla_{e_j} - \nabla_{e_j}\nabla_{e_i})s$$

$$= \sum_{i < j} e_i e_j R(e_i, e_j)s$$

其中 $R(X,Y) = [\nabla_X, \nabla_Y] - \nabla_{[X,Y]}$ 是曲率张量。

**步骤3：曲率化简**

在Clifford代数中：
$$\sum_{i < j} e_i e_j R(e_i, e_j) = \frac{1}{2} \sum_{i,j} e_i e_j R(e_i, e_j)$$

旋量表示下的曲率：
$$R^{S}(e_i, e_j) = \frac{1}{4} \sum_{k,l} R_{ijkl} e_k e_l$$

代入：
$$\sum_{i < j} e_i e_j R^{S}(e_i, e_j) = \frac{1}{4} \sum_{i,j,k,l} R_{ijkl} e_i e_j e_k e_l$$

由Bianchi恒等式 $R_{ijkl} + R_{iklj} + R_{iljk} = 0$ 和Clifford代数关系：

$$= \frac{1}{4} \sum_{i,j} R_{ijji} = \frac{1}{4} R$$

（标量曲率 $R = \sum_{i,j} R_{ijji}$）

**步骤4：整理**

$$D^2s = -\sum_i \nabla_{e_i}^2 s + \text{(lower order terms from } \nabla^*\nabla) + \frac{1}{4}Rs$$

更精确地：
$$\nabla^*\nabla s = -\sum_i \nabla_{e_i}\nabla_{e_i}s + \sum_i \nabla_{\nabla_{e_i}e_i}s$$

故：
$$D^2 = \nabla^*\nabla + \frac{1}{4}R$$

$\square$

#### 推广

对 twisted Dirac 算子 $D_A$（带向量丛 $E$ 上的联络 $A$）：
$$D_A^2 = \nabla_A^*\nabla_A + \frac{1}{4}R + F_A$$

其中 $F_A$ 是 $E$ 的曲率贡献。

---

### (c) 正标量曲率障碍

#### Bochner技巧

**定理**：若紧自旋流形 $M$ 有正标量曲率 $R > 0$，则 $M$ 没有非零调和旋量：
$$\ker D = 0$$

**证明**：设 $Ds = 0$，则 $D^2s = 0$。

由Lichnerowicz公式：
$$0 = \langle D^2 s, s \rangle = \langle \nabla^*\nabla s, s \rangle + \frac{1}{4}\langle Rs, s \rangle$$

$$= \|\nabla s\|_{L^2}^2 + \frac{1}{4} \int_M R |s|^2 d\mu$$

若 $R > 0$ 处处成立：
$$0 \geq \|\nabla s\|_{L^2}^2 + \frac{\min R}{4} \|s\|_{L^2}^2$$

故 $s = 0$。

$\square$

#### Â-亏格障碍

**Atiyah-Singer指标定理**对Dirac算子：
$$\text{ind}(D^+) = \dim \ker D^+ - \dim \ker D^- = \hat{A}(M)$$

其中 $\hat{A}(M) = \langle \hat{A}(TM), [M] \rangle$ 是Â-亏格。

**推论**：若 $M$ 有正标量曲率，则 $\hat{A}(M) = 0$。

**证明**：$R > 0 \Rightarrow \ker D = 0 \Rightarrow \ker D^+ = \ker D^- = 0 \Rightarrow \text{ind}(D^+) = 0$。

$\square$

#### Lichnerowicz定理

**定理**（Lichnerowicz, 1963）：若 $M^{4k}$ 是紧自旋流形且 $\hat{A}(M) \neq 0$，则 $M$ 不允许任何正标量曲率度量。

**例子**：
- $K3$ 曲面：$\hat{A}(K3) = 2 \neq 0$，故无PSC度量
- 某些4维流形：由Rokhlin定理，spin 4-manifold 的 signature 被16整除，且 $\hat{A} = -\frac{1}{24}\sigma$

#### 高维障碍

**Gromov-Lawson定理**：存在高维的拓扑障碍（与 $KO$-理论联系）。

对单连通 $M$（$\dim \geq 5$）：
$$M \text{ 有PSC} \Leftrightarrow \text{某个 } KO\text{-理论不变量为0}$$

具体地，用 **Dirac指标与 $KO$-理论的联系**：
$$\alpha(M) \in KO_n(pt) = KO^{-n}(pt)$$

$\alpha(M) = 0 \Leftrightarrow M$ 有PSC（Stolz定理，单连通情形）。

#### 现代发展

- **Schoen-Yau、Witten**：正质量定理的证明也用到类似Bochner技巧
- **Seiberg-Witten方程**：4维辛流形上的类似障碍
- **Ricci flow**：PSC度量在Ricci流下可能保持或改善