---
msc_primary: "19Lxx"
msc_secondary: ["55N15", "55R50"]
---

# K理论初步 / Introduction to K-Theory

**主题编号**: B.05.15
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**国际对齐**: Atiyah *K-Theory* (1967), Karoubi *K-Theory: An Introduction* (1978), Hatcher *Vector Bundles and K-Theory* (2003)

---

## 目录 / Table of Contents

- [K理论初步 / Introduction to K-Theory](#k理论初步--introduction-to-k-theory)
  - [1. 基础概念 / Basic Concepts](#1-基础概念--basic-concepts)
  - [2. Bott周期性 / Bott Periodicity](#2-bott周期性--bott-periodicity)
  - [3. 高阶K群与谱序列 / Higher K-Groups and Spectral Sequences](#3-高阶k群与谱序列--higher-k-groups-and-spectral-sequences)
  - [4. 核心定理 / Core Theorems](#4-核心定理--core-theorems)
  - [5. 实战问题 / Practical Problems](#5-实战问题--practical-problems)
  - [6. 参考文献 / References](#6-参考文献--references)

---

## 1. 基础概念 / Basic Concepts

### 1.1 向量丛的半群 / The Semigroup of Vector Bundles

**定义 1.1.1**（向量丛的等价类）
设 $X$ 是紧致 Hausdorff 空间。记 $\text{Vect}_\mathbb{F}(X)$ 为 $X$ 上有限秩 $\mathbb{F}$-向量丛（$\mathbb{F} = \mathbb{R}$ 或 $\mathbb{C}$）的同构类集合。

**定义 1.1.2**（Whitney 和）
在 $\text{Vect}_\mathbb{F}(X)$ 上定义加法：
$$[E] + [F] = [E \oplus F]$$
这使得 $\text{Vect}_\mathbb{F}(X)$ 成为**交换半群**。

**问题**：半群缺乏逆元（一般地，$E \oplus F$ 不是平凡丛）。

### 1.2 Grothendieck 构造 / Grothendieck Construction

**定义 1.2.1**（K群 / K-Group）
$X$ 的**K群** $K_\mathbb{F}(X)$ 是半群 $(\text{Vect}_\mathbb{F}(X), \oplus)$ 的**Grothendieck 完备化**：
$$K_\mathbb{F}(X) = \text{Grothendieck}(\text{Vect}_\mathbb{F}(X))$$

**构造方法**：形式地添加逆元
$$K_\mathbb{F}(X) = \{[E] - [F] : [E], [F] \in \text{Vect}_\mathbb{F}(X)\} / \sim$$
其中 $[E] - [F] \sim [E'] - [F']$ 当且仅当存在 $[G]$ 使得 $[E \oplus F' \oplus G] = [E' \oplus F \oplus G]$。

**定理 1.2.2**（K群的结构）
1. $K_\mathbb{F}(X)$ 是交换群
2. 有自然的半群同态 $\text{Vect}_\mathbb{F}(X) \to K_\mathbb{F}(X)$，$[E] \mapsto [E] - [0]$
3. 任何从 $\text{Vect}_\mathbb{F}(X)$ 到群的同态唯一地通过 $K_\mathbb{F}(X)$ 分解

### 1.3 约化K群 / Reduced K-Theory

**定义 1.3.1**（约化K群）
设 $X$ 是带基点空间。定义**约化K群**：
$$\tilde{K}_\mathbb{F}(X) = \ker(K_\mathbb{F}(X) \xrightarrow{i^*} K_\mathbb{F}(x_0) \cong \mathbb{Z})$$
其中 $i: x_0 \hookrightarrow X$ 是基点的包含。

**定理 1.3.2**
$$K_\mathbb{F}(X) \cong \tilde{K}_\mathbb{F}(X) \oplus \mathbb{Z}$$

**例 1.3.3**
- $\tilde{K}_\mathbb{C}(S^2) \cong \mathbb{Z}$，生成元是 tautological 线丛的类减去平凡线丛
- $\tilde{K}_\mathbb{R}(S^1) \cong \mathbb{Z}/2\mathbb{Z}$（Möbius 丛）

---

## 2. Bott周期性 / Bott Periodicity

### 2.1 复Bott周期性 / Complex Bott Periodicity

**定理 2.1.1**（复Bott周期性 / Complex Bott Periodicity）
存在自然的群同构：
$$\tilde{K}_\mathbb{C}(X) \cong \tilde{K}_\mathbb{C}(\Sigma^2 X) = \tilde{K}_\mathbb{C}(S^2 \wedge X)$$
或等价地：
$$K_\mathbb{C}(X) \cong K_\mathbb{C}(S^2 \times X, X \vee S^2)$$

**推论 2.1.2**（球面的K群）
$$\tilde{K}_\mathbb{C}(S^n) = \begin{cases} \mathbb{Z} & n \text{ 偶数} \\ 0 & n \text{ 奇数} \end{cases}$$

### 2.2 实Bott周期性 / Real Bott Periodicity

**定理 2.2.1**（实Bott周期性 / Real Bott Periodicity）
存在自然的群同构：
$$\tilde{K}_\mathbb{R}(X) \cong \tilde{K}_\mathbb{R}(\Sigma^8 X)$$

**推论 2.2.2**（球面的实K群）
$\tilde{K}_\mathbb{R}(S^n)$ 以 8 为周期：
$$\tilde{K}_\mathbb{R}(S^n) = \begin{cases} \mathbb{Z} & n \equiv 0 \pmod 8 \\ \mathbb{Z}/2\mathbb{Z} & n \equiv 1 \pmod 8 \\ \mathbb{Z}/2\mathbb{Z} & n \equiv 2 \pmod 8 \\ 0 & n \equiv 3 \pmod 8 \\ \mathbb{Z} & n \equiv 4 \pmod 8 \\ 0 & n \equiv 5,6,7 \pmod 8 \end{cases}$$

### 2.3 Bott映射的显式构造 / Explicit Bott Map

**定理 2.3.1**
Bott 同构由**外部张量积**给出：
$$\tilde{K}_\mathbb{C}(X) \otimes \tilde{K}_\mathbb{C}(S^2) \xrightarrow{\cong} \tilde{K}_\mathbb{C}(X \times S^2)$$

**生成元的显式描述**：
- $\tilde{K}_\mathbb{C}(S^2)$ 的生成元是 $[H] - [1]$，其中 $H$ 是 $S^2 = \mathbb{C}P^1$ 上的 tautological 线丛
- Bott 映射将 $[E] - [F]$ 送到 $([E] - [F]) \otimes ([H] - [1])$

---

## 3. 高阶K群与谱序列 / Higher K-Groups and Spectral Sequences

### 3.1 负K群 / Negative K-Groups

**定义 3.1.1**
对 $n \geq 0$，定义：
$$K^{-n}(X) = \tilde{K}(\Sigma^n X_+) = \tilde{K}(S^n \wedge (X \sqcup \{pt\}))$$

**定理 3.1.2**
由 Bott 周期性，$K^{-n}(X)$ 只依赖于 $n \pmod 2$（复K理论）或 $n \pmod 8$（实K理论）。

### 3.2 Atiyah-Hirzebruch谱序列 / Atiyah-Hirzebruch Spectral Sequence

**定理 3.2.1**（AHSS for K-Theory）
对有限 CW 复形 $X$，存在谱序列：
$$E_2^{p,q} = H^p(X; K^q(\text{pt})) \Rightarrow K^{p+q}(X)$$

**推论 3.2.2**
$E_2$ 页只有 $q$ 为偶数时非零（复K理论），且 $K^q(\text{pt}) = \mathbb{Z}$ 对 $q$ 偶，$0$ 对 $q$ 奇。

### 3.3 Adams运算 / Adams Operations

**定义 3.3.1**
对 $k \geq 1$，**Adams 运算** $\psi^k: K(X) \to K(X)$ 是环同态，满足：
1. $\psi^k([L]) = [L^{\otimes k}]$ 对线丛 $L$
2. $\psi^k \circ \psi^l = \psi^{kl}$
3. $\psi^k(x) \equiv x^k \pmod{\text{挠元}}$（对 $x \in \tilde{K}(X)$）

**应用**：Adams 运算用于证明球面上的线性无关向量场个数的上界（Adams 定理）。

---

## 4. 核心定理 / Core Theorems

### 4.1 环结构与lambda-运算 / Ring Structure and lambda-Operations

**定理 4.1.1**（K群的环结构）
$K(X)$ 具有交换环结构，乘法由张量积给出：
$$[E] \cdot [F] = [E \otimes F]$$

**定义 4.1.2**（lambda-运算）
定义 $\lambda^k: K(X) \to K(X)$：
$$\lambda^k([E] - [F]) = \sum_{i=0}^k (-1)^i [\Lambda^i F^*] [\Lambda^{k-i} E]$$

**定理 4.1.3**（分裂原理与 Adams 运算的关系）
$$\psi^k(x) = Q_k(\lambda^1(x), \ldots, \lambda^k(x))$$
其中 $Q_k$ 是 Newton 多项式。

### 4.2 Thom同构 / Thom Isomorphism

**定理 4.2.1**（K理论中的Thom同构）
设 $E$ 是复向量丛，$\pi: E \to X$ 是投影。存在**Thom 类** $\lambda_E \in \tilde{K}(E^+)$ 使得：
$$\Phi: K(X) \xrightarrow{\cong} \tilde{K}(E^+), \quad \Phi(x) = \pi^*(x) \cdot \lambda_E$$
是同构，其中 $E^+$ 是 $E$ 的一点紧化。

### 4.3 指标定理的联系 / Relation to Index Theory

**定理 4.3.1**（符号差与K理论）
紧流形 $M$ 的符号差可表示为：
$$\sigma(M) = \langle \text{ch}([T^*M]) \smile \text{Td}(TM), [M] \rangle$$
其中 $\text{ch}$ 是 Chern 特征，$\text{Td}$ 是 Todd 类。

**定理 4.3.2**（Atiyah-Singer 指标定理）
椭圆算子 $D$ 的解析指标等于拓扑指标：
$$\text{ind}(D) = \langle \text{ch}([\sigma(D)]) \smile \text{Td}(T^*M), [M] \rangle$$

---

## 5. 实战问题 / Practical Problems

### 问题 1：计算 K(S^2)

**问题**：计算 $K_\mathbb{C}(S^2)$ 并确定其环结构。

**解答**：

1. 由定义，$K(S^2) = \tilde{K}(S^2) \oplus \mathbb{Z}$

2. **计算 $\tilde{K}(S^2)$**：
   - $S^2$ 上的复向量丛由第一陈类分类
   - 线丛 $L$ 对应 $c_1(L) \in H^2(S^2; \mathbb{Z}) \cong \mathbb{Z}$
   - 对任意秩 $n$ 丛 $E$，由分裂原理 $E \cong L_1 \oplus \cdots \oplus L_n$
   - 在 $K$ 群中，$[E] = [L_1] + \cdots + [L_n]$
   - 设 $[L] - [1]$ 为 $c_1(L) = 1$ 的线丛的类，则任意 $[L_k] - [1] = k([L] - [1])$

3. **结论**：
   $$K(S^2) \cong \mathbb{Z}[x]/(x^2), \quad x = [H] - [1]$$
   其中 $H$ 是 tautological 线丛。

4. **验证**：$x^2 = ([H] - [1])^2 = [H \otimes H] - 2[H] + [1]$。实际上 $K(S^2) \cong \mathbb{Z}[h]/((h-1)^2)$，其中 $h = [H]$。

### 问题 2：利用Bott周期性计算 K(S^4)

**问题**：计算 $\tilde{K}_\mathbb{C}(S^4)$。

**解答**：

1. 由 Bott 周期性：$\tilde{K}(X) \cong \tilde{K}(\Sigma^2 X)$
2. 故 $\tilde{K}(S^4) = \tilde{K}(\Sigma^4 S^0) \cong \tilde{K}(\Sigma^2 S^0) = \tilde{K}(S^2) \cong \mathbb{Z}$
3. 或者直接用分裂原理：$S^4$ 上的丛稳定地由第二陈类分类
4. $\tilde{K}(S^4) \cong \mathbb{Z}$，生成元对应 $c_2 = 1$

### 问题 3：实K理论中的Möbius丛

**问题**：计算 $K_\mathbb{R}(S^1)$ 并识别 Möbius 丛的类。

**解答**：

1. $S^1$ 上的实线丛由 $w_1 \in H^1(S^1; \mathbb{Z}/2) = \mathbb{Z}/2$ 分类
2. 两个线丛：平凡丛 $\varepsilon^1$ 和 Möbius 丛 $M$
3. 在 $K_\mathbb{R}(S^1)$ 中，$[M] - [\varepsilon^1]$ 是挠元
4. 事实上，$[M] + [M] = [M \oplus M] = [\varepsilon^1 \oplus \varepsilon^1] = 2[\varepsilon^1]$（因为 $M \oplus M \cong \varepsilon^1 \oplus \varepsilon^1$）
5. 故 $2([M] - [\varepsilon^1]) = 0$，$\tilde{K}_\mathbb{R}(S^1) \cong \mathbb{Z}/2\mathbb{Z}$

### 问题 4：Chern特征的性质

**问题**：证明 Chern 特征 $\text{ch}: K(X) \otimes \mathbb{Q} \to H^{\text{even}}(X; \mathbb{Q})$ 是环同构（对有限 CW 复形）。

**解答**：

1. **Chern 特征的定义**：
   - 对线丛 $L$，$\text{ch}(L) = e^{c_1(L)} = \sum_{k=0}^\infty \frac{c_1(L)^k}{k!}$
   - 一般地，$\text{ch}(E \ominus F) = \text{ch}(E) - \text{ch}(F)$

2. **验证环同态**：
   - $\text{ch}(E \oplus F) = \text{ch}(E) + \text{ch}(F)$（由 Whitney 和公式）
   - $\text{ch}(E \otimes F) = \text{ch}(E) \smile \text{ch}(F)$（由分裂原理和线丛情况验证）

3. **同构的证明**：
   - 对 $X = \text{pt}$，$\text{ch}: \mathbb{Z} \to \mathbb{Q}$ 是单射
   - 由 AHSS 和 5-引理，对一般 $X$ 也是同构

### 问题 5：Adams运算的应用

**问题**：证明 $S^2$ 上不存在秩 2 复向量丛 $E$ 使得 $c_1(E) = 0$ 但 $E$ 非平凡。

**解答**：

1. 对秩 2 丛，$c_1(E) = 0$ 意味着 $E$ 的行列式丛平凡
2. 由分裂原理，$E \cong L \oplus L^*$（因为 $L_1 \otimes L_2 = \det E = 1$）
3. 在 $K$ 群中，$[E] = [L] + [L^*]$
4. 若 $c_1(L) = k$，则 $[L] = 1 + kx$，$[L^*] = 1 - kx$（其中 $x = [H] - 1$）
5. 故 $[E] = 2$，即 $E$ 稳定平凡
6. 但 $S^2$ 上秩 2 丛由其陈类完全分类，故 $E$ 本身平凡

---

## 6. 参考文献 / References

### 经典教材 / Classic Textbooks

- Atiyah, M. F. (1967). *K-Theory*. 2nd Edition. Benjamin.
- Karoubi, M. (1978). *K-Theory: An Introduction*. Springer.
- Hatcher, A. (2003). *Vector Bundles and K-Theory* (Notes).

### 高级专题 / Advanced Topics

- Atiyah, M. F., & Singer, I. M. (1968). The Index of Elliptic Operators I. *Annals of Mathematics*, 87(3), 484-530.
- Adams, J. F. (1962). Vector Fields on Spheres. *Annals of Mathematics*, 75(3), 603-632.

### 代数K理论 / Algebraic K-Theory

- Rosenberg, J. (1994). *Algebraic K-Theory and Its Applications*. Springer.
- Weibel, C. A. (2013). *The K-book: An Introduction to Algebraic K-theory*.

### 在线资源 / Online Resources

- Hatcher's VBKT: <https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf>
- nLab: Topological K-Theory
- Wikipedia: K-theory

---

**文档状态**: K理论初步文档创建完成
**内容范围**: 基础概念、核心定理、实战问题
**难度级别**: 研究生高级
