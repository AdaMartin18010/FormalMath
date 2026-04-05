---
title: 同伦论基础
msc_primary: 55Q05
msc_secondary:
- 55A99
- 00A99
processed_at: '2026-04-05'
---
# 同伦论基础 / Foundations of Homotopy Theory

**主题编号**: B.05.12
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**国际对齐**: Hatcher *Algebraic Topology* (2002), May *A Concise Course in Algebraic Topology* (1999)

---

## 目录 / Table of Contents

- [同伦论基础 / Foundations of Homotopy Theory](#同伦论基础-foundations-of-homotopy-theory)
  - [1. 基础概念 / Basic Concepts](#1-基础概念-basic-concepts)
  - [2. 同伦群 / Homotopy Groups](#2-同伦群-homotopy-groups)
  - [3. 纤维化与余纤维化 / Fibrations and Cofibrations](#3-纤维化与余纤维化-fibrations-and-cofibrations)
  - [4. 核心定理 / Core Theorems](#4-核心定理-core-theorems)
  - [5. 实战问题 / Practical Problems](#5-实战问题-practical-problems)
  - [6. 参考文献 / References](#6-参考文献-references)

---

## 1. 基础概念 / Basic Concepts

### 1.1 同伦 / Homotopy

**定义 1.1.1**（同伦 / Homotopy）
设 $X, Y$ 为拓扑空间，$f, g: X \to Y$ 为连续映射。若存在连续映射 $H: X \times [0,1] \to Y$ 使得：
$$H(x, 0) = f(x), \quad H(x, 1) = g(x), \quad \forall x \in X$$
则称 $f$ 与 $g$ **同伦**（homotopic），记作 $f \simeq g$，$H$ 称为从 $f$ 到 $g$ 的**同伦**。

**定义 1.1.2**（相对同伦 / Relative Homotopy）
设 $A \subseteq X$，若同伦 $H$ 满足 $H(a, t) = f(a) = g(a)$ 对所有 $a \in A$ 和 $t \in [0,1]$ 成立，则称 $f$ 与 $g$ **相对于 $A$ 同伦**，记作 $f \simeq g \text{ rel } A$。

**定理 1.1.1**（同伦是等价关系）
同伦关系 $\simeq$ 是 $C(X, Y)$（从 $X$ 到 $Y$ 的连续映射集合）上的等价关系。

*证明*：
- **自反性**：$f \simeq f$ 通过常同伦 $H(x, t) = f(x)$
- **对称性**：若 $H: f \simeq g$，则 $\bar{H}(x, t) = H(x, 1-t)$ 给出 $g \simeq f$
- **传递性**：若 $H: f \simeq g$ 且 $K: g \simeq h$，则
$$(H * K)(x, t) = \begin{cases} H(x, 2t) & 0 \leq t \leq 1/2 \\ K(x, 2t-1) & 1/2 \leq t \leq 1 \end{cases}$$
给出 $f \simeq h$ $\square$

### 1.2 同伦等价 / Homotopy Equivalence

**定义 1.2.1**（同伦等价 / Homotopy Equivalence）
空间 $X$ 与 $Y$ 称为**同伦等价**（homotopy equivalent），若存在映射 $f: X \to Y$ 和 $g: Y \to X$ 使得：
$$g \circ f \simeq \text{id}_X, \quad f \circ g \simeq \text{id}_Y$$
记作 $X \simeq Y$。此时 $f$ 和 $g$ 称为**同伦等价**。

**定义 1.2.2**（形变收缩 / Deformation Retraction）
设 $A \subseteq X$，若存在收缩 $r: X \to A$（即 $r|_A = \text{id}_A$）使得 $i \circ r \simeq \text{id}_X \text{ rel } A$，其中 $i: A \hookrightarrow X$ 为包含映射，则称 $A$ 是 $X$ 的**形变收缩核**（deformation retract）。

**定理 1.2.1**
若 $A$ 是 $X$ 的形变收缩核，则 $A \simeq X$。

**例 1.2.2**
- 圆周 $S^1$ 是 $\mathbb{C} \setminus \{0\}$ 的形变收缩核
- 单点 $\{x_0\}$ 是凸集的形变收缩核
- Möbius 带的中心圆周是其形变收缩核

---

## 2. 同伦群 / Homotopy Groups

### 2.1 基本群 / Fundamental Group

**定义 2.1.1**（回路 / Loop）
设 $X$ 为拓扑空间，$x_0 \in X$。连续映射 $\gamma: [0,1] \to X$ 满足 $\gamma(0) = \gamma(1) = x_0$ 称为以 $x_0$ 为基点的**回路**（loop）。

**定义 2.1.2**（基本群 / Fundamental Group）
在基点 $x_0$ 处所有回路的同伦类集合记为 $\pi_1(X, x_0)$，配备运算：
$$[\gamma] \cdot [\delta] = [\gamma * \delta]$$
其中 $(\gamma * \delta)(t) = \begin{cases} \gamma(2t) & 0 \leq t \leq 1/2 \\ \delta(2t-1) & 1/2 \leq t \leq 1 \end{cases}$

则 $\pi_1(X, x_0)$ 构成群，称为 $X$ 在 $x_0$ 处的**基本群**。

**定理 2.1.1**（基本群的性质）
1. $\pi_1(X, x_0)$ 是群，单位元为常回路 $[e_{x_0}]$
2. 若 $X$ 道路连通，则不同基点的基本群同构
3. $\pi_1(X \times Y, (x_0, y_0)) \cong \pi_1(X, x_0) \times \pi_1(Y, y_0)$

### 2.2 高阶同伦群 / Higher Homotopy Groups

**定义 2.2.1**（$n$ 阶同伦群）
设 $n \geq 1$，$I^n = [0,1]^n$，$\partial I^n$ 为其边界。定义：
$$\pi_n(X, x_0) = [ (I^n, \partial I^n), (X, x_0) ]$$
即映射 $f: (I^n, \partial I^n) \to (X, x_0)$ 的同伦类集合。

**定理 2.2.1**（高阶同伦群的群结构）
- 当 $n \geq 2$ 时，$\pi_n(X, x_0)$ 是**阿贝尔群**
- 群运算通过将 $I^n$ 沿某一坐标轴拼接定义
- 对 $n \geq 2$，拼接顺序不影响结果（与 $n=1$ 不同）

**定理 2.2.2**（球面的同伦群）
$$\pi_k(S^n) = \begin{cases} 0 & k < n \\ \mathbb{Z} & k = n \\ \text{复杂} & k > n \end{cases}$$

### 2.3 相对同伦群 / Relative Homotopy Groups

**定义 2.3.1**（相对同伦群）
设 $A \subseteq X$，$x_0 \in A$。定义：
$$\pi_n(X, A, x_0) = [(I^n, \partial I^n, J^{n-1}), (X, A, x_0)]$$
其中 $J^{n-1} = \partial I^n \setminus (I^{n-1} \times \{0\})$。

**定理 2.3.1**（同伦群的长正合序列）
对空间对 $(X, A)$，存在长正合序列：
$$\cdots \to \pi_n(A) \to \pi_n(X) \to \pi_n(X, A) \to \pi_{n-1}(A) \to \cdots \to \pi_0(X)$$

---

## 3. 纤维化与余纤维化 / Fibrations and Cofibrations

### 3.1 纤维化 / Fibrations

**定义 3.1.1**（纤维化 / Fibration）
映射 $p: E \to B$ 称为**纤维化**，若对任意空间 $X$，任意同伦 $H: X \times I \to B$ 和映射 $\tilde{f}: X \to E$ 满足 $p \circ \tilde{f} = H(-, 0)$，存在提升 $\tilde{H}: X \times I \to E$ 使得 $p \circ \tilde{H} = H$ 且 $\tilde{H}(-, 0) = \tilde{f}$。

$$\begin{array}{ccc}
X & \xrightarrow{\tilde{f}} & E \\
\downarrow & \swarrow_{\tilde{H}} & \downarrow{p} \\
X \times I & \xrightarrow{H} & B
\end{array}$$

**定义 3.1.2**（塞尔纤维化 / Serre Fibration）
若上述提升性质对所有 CW 复形 $X$ 成立，则称 $p$ 为**塞尔纤维化**。

**定理 3.1.1**（纤维化的同伦群长正合序列）
对纤维化 $p: E \to B$，纤维 $F = p^{-1}(b_0)$，存在长正合序列：
$$\cdots \to \pi_n(F) \to \pi_n(E) \to \pi_n(B) \to \pi_{n-1}(F) \to \cdots$$

**例 3.1.2**（霍普夫纤维化）
$$S^1 \hookrightarrow S^3 \xrightarrow{\eta} S^2$$
这是历史上第一个非平凡纤维化的例子，诱导同伦群的长正合序列可以计算球面的部分同伦群。

### 3.2 余纤维化 / Cofibrations

**定义 3.2.1**（余纤维化 / Cofibration）
映射 $i: A \to X$ 称为**余纤维化**，若对任意空间 $Y$，任意同伦 $H: A \times I \to Y$ 和映射 $f: X \to Y$ 满足 $H(-, 0) = f \circ i$，存在延拓 $\tilde{H}: X \times I \to Y$ 使得 $\tilde{H} \circ (i \times \text{id}) = H$ 且 $\tilde{H}(-, 0) = f$。

**定理 3.2.1**
相对 CW 复形的包含映射 $(X, A) \hookrightarrow (Y, B)$ 是余纤维化。

---

## 4. 核心定理 / Core Theorems

### 4.1 怀特黑德定理 / Whitehead's Theorem

**定理 4.1.1**（怀特黑德定理）
设 $f: X \to Y$ 是 CW 复形之间的映射，若 $f$ 诱导所有同伦群的同构：
$$f_*: \pi_n(X, x_0) \xrightarrow{\cong} \pi_n(Y, f(x_0)), \quad \forall n \geq 0$$
则 $f$ 是**同伦等价**。

*注*：此定理对一般拓扑空间不成立，需要附加条件（如 X, Y 具有 CW 复形的同伦类型）。

### 4.2 Hurewicz 定理 / Hurewicz Theorem

**定理 4.2.1**（Hurewicz 同态）
存在自然同态 $h: \pi_n(X, x_0) \to H_n(X; \mathbb{Z})$，称为**Hurewicz 同态**。

**定理 4.2.2**（Hurewicz 定理）
设 $X$ 是 $(n-1)$-连通空间（$n \geq 2$），则：
1. $\tilde{H}_k(X) = 0$ 对 $k < n$
2. $h: \pi_n(X) \to H_n(X)$ 是同构

### 4.3 Blakers-Massey 定理

**定理 4.3.1**（Blakers-Massey 定理）
设 $X = A \cup B$，$C = A \cap B$。若 $(A, C)$ 是 $m$-连通的，$(B, C)$ 是 $n$-连通的，则 inclusion 诱导的映射：
$$\pi_k(A, C) \to \pi_k(X, B)$$
在 $k < m + n$ 时是同构，在 $k = m + n$ 时是满射。

### 4.4 Freudenthal 悬挂定理

**定理 4.4.1**（Freudenthal 悬挂定理）
设 $X$ 是 $(n-1)$-连通空间，则悬挂同态：
$$\Sigma: \pi_k(X) \to \pi_{k+1}(\Sigma X)$$
在 $k \leq 2n - 1$ 时是满射，在 $k < 2n - 1$ 时是同构。

**推论 4.4.2**（稳定同伦群）
对 $n \geq k + 2$，$\pi_{n+k}(S^n)$ 与 $n$ 无关，称为**稳定同伦群** $\pi_k^S$。

---

## 5. 实战问题 / Practical Problems

### 问题 1：计算 $S^1$ 的基本群

**问题**：证明 $\pi_1(S^1, 1) \cong \mathbb{Z}$。

**解答思路**：

1. 使用覆叠空间理论：万有覆叠 $\exp: \mathbb{R} \to S^1$，$t \mapsto e^{2\pi i t}$
2. 回路提升：回路 $\gamma: [0,1] \to S^1$ 提升为 $\tilde{\gamma}: [0,1] \to \mathbb{R}$
3. 映射 $[\gamma] \mapsto \tilde{\gamma}(1) - \tilde{\gamma}(0) \in \mathbb{Z}$ 给出同构

**关键步骤**：
- 证明提升的存在唯一性
- 证明同伦的回路有相同的提升终点差
- 证明任意整数对应某回路的类

### 问题 2：计算 $\pi_4(S^3)$

**问题**：利用霍普夫纤维化计算 $\pi_4(S^3)$。

**解答**：

考虑霍普夫纤维化 $S^1 \hookrightarrow S^3 \xrightarrow{\eta} S^2$，其同伦群长正合序列为：
$$\cdots \to \pi_4(S^1) \to \pi_4(S^3) \to \pi_4(S^2) \to \pi_3(S^1) \to \cdots$$

由于 $\pi_4(S^1) = \pi_3(S^1) = 0$（$S^1$ 的万有覆叠是 $\mathbb{R}$，高阶同伦群平凡），得到：
$$\pi_4(S^3) \cong \pi_4(S^2)$$

再利用 $\pi_4(S^2) \cong \mathbb{Z}/2\mathbb{Z}$（可通过进一步的纤维化和谱序列计算），最终：
$$\pi_4(S^3) \cong \mathbb{Z}/2\mathbb{Z}$$

### 问题 3：证明 $S^n$ 是 $(n-1)$-连通的

**问题**：证明对 $k < n$，$\pi_k(S^n) = 0$。

**解答**：

**方法 1**（胞腔逼近）：
- $S^n$ 的 CW 结构有一个 0-胞腔和一个 $n$-胞腔
- 任意映射 $f: S^k \to S^n$（$k < n$）可胞腔逼近到 $(n-1)$-骨架
- $(n-1)$-骨架是单点，故 $f$ 零伦

**方法 2**（光滑逼近 + Sard 定理）：
- 任意连续映射可用光滑映射逼近
- 若 $k < n$，由 Sard 定理，光滑映射的像在 $S^n$ 中测度为零
- 像不包含某点，故可形变收缩到该点的补集（同胚于 $\mathbb{R}^n$）
- $\mathbb{R}^n$ 可缩，故映射零伦

### 问题 4：同伦等价与同调

**问题**：设 $f: X \to Y$ 是同伦等价，证明 $f$ 诱导同调群的同构 $f_*: H_n(X) \xrightarrow{\cong} H_n(Y)$。

**解答**：

1. 设 $g: Y \to X$ 是同伦逆，即 $g \circ f \simeq \text{id}_X$，$f \circ g \simeq \text{id}_Y$

2. 由同伦不变性，同伦的映射诱导相同的同调同态：
   $$(g \circ f)_* = (\text{id}_X)_* = \text{id}_{H_n(X)}$$
   $$(f \circ g)_* = (\text{id}_Y)_* = \text{id}_{H_n(Y)}$$

3. 因此 $(g \circ f)_* = g_* \circ f_* = \text{id}$，$(f \circ g)_* = f_* \circ g_* = \text{id}$

4. 故 $f_*$ 是同构，$g_*$ 是其逆 $\square$

### 问题 5：计算实射影空间的基本群

**问题**：计算 $\pi_1(\mathbb{R}P^n)$ 对 $n \geq 2$。

**解答**：

1. 覆叠映射 $p: S^n \to \mathbb{R}P^n$ 是 2 层覆叠
2. 由覆叠空间理论，$p_*: \pi_1(S^n) \to \pi_1(\mathbb{R}P^n)$ 是单射（当 $n \geq 2$）
3. 由于 $n \geq 2$ 时 $\pi_1(S^n) = 0$，$p_*$ 的像是平凡子群
4. 覆叠的层数等于 $p_*\pi_1(S^n)$ 在 $\pi_1(\mathbb{R}P^n)$ 中的指数
5. 故 $|\pi_1(\mathbb{R}P^n)| = 2$，即 $\pi_1(\mathbb{R}P^n) \cong \mathbb{Z}/2\mathbb{Z}$

---

## 6. 参考文献 / References

### 经典教材 / Classic Textbooks

- Hatcher, A. (2002). *Algebraic Topology*. Cambridge University Press.
- May, J. P. (1999). *A Concise Course in Algebraic Topology*. University of Chicago Press.
- Whitehead, G. W. (1978). *Elements of Homotopy Theory*. Springer-Verlag.

### 专题著作 / Monographs

- Fomenko, A. T., & Fuchs, D. B. (2016). *Homotopical Topology*. 2nd Edition. Springer.
- Davis, J. F., & Kirk, P. (2001). *Lecture Notes in Algebraic Topology*. AMS.

### 中文教材 / Chinese Textbooks

- 姜伯驹. (2006). *同调论*. 北京大学出版社.
- 尤承业. (1997). *基础拓扑学讲义*. 北京大学出版社.

### 在线资源 / Online Resources

- Hatcher's Algebraic Topology (免费下载): <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>
- MIT OpenCourseWare: 18.905 Algebraic Topology I
- nLab: Homotopy Theory

---

**文档状态**: 同伦论基础文档创建完成
**内容范围**: 基础概念、核心定理、实战问题
**难度级别**: 研究生初级至中级
