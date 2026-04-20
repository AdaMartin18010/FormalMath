---
msc_primary: 00A99
习题编号: TOP-093
学科: 拓扑
知识点: 拓扑-Thom空间
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Thom 空间

## 题目

**(a)** 定义向量丛的 Thom 空间 Th(E) 并证明其基本性质。

**(b)** 证明 Thom 同构定理：$H^i(X) \cong H^{i+k}(\text{Th}(E))$。

**(c)** 计算 MSO 和 MO 的上同调环。

## 解答

### (a) Thom 空间的定义与性质

**定义**：设 $E \to X$ 是秩 $k$ 实向量丛。令 $D(E) = \{v \in E : |v| \leq 1\}$ 为圆盘丛，$S(E) = \{v \in E : |v| = 1\}$ 为球丛（关于某个 Riemann 度规）。**Thom 空间**定义为商空间：
$$\text{Th}(E) = D(E) / S(E)$$

等价描述：$\text{Th}(E)$ 是 $E$ 的一点紧化（当 $X$ 紧时），或作为 $E$ 的 Alexandroff 紧化，其中无穷远点由 $S(E)$ 的所有点等同而成。

**基本性质**：

1. **基点**：$\text{Th}(E)$ 有典范基点（$S(E)$ 的像，记为 $\infty$ 或 $*$）。

2. **自然性**：对丛映射（覆盖 $f: X \to Y$ 的向量丛映射）$\hat{f}: E \to F$，诱导映射：
   $$\text{Th}(\hat{f}): \text{Th}(E) \to \text{Th}(F)$$

3. **Whitney 和**：对丛的直和 $E \oplus F$：
   $$\text{Th}(E \oplus F) \cong \text{Th}(E) \wedge \text{Th}(F)$$
   （smash 积）

4. **平凡丛**：若 $E = X \times \mathbb{R}^k$ 是平凡丛，则：
   $$\text{Th}(E) = X_+ \wedge S^k = \Sigma^k X_+$$
   其中 $X_+ = X \sqcup \{pt\}$，$\Sigma^k$ 是 $k$ 次悬挂。

5. **约化上同调**：对连通 $X$，
   $$\widetilde{H}^*(\text{Th}(E)) \cong H^*(D(E), S(E)) = H^*_{cs}(E)$$
   （紧支上同调）

**Thom 空间的同伦型**：Thom 空间仅依赖于向量丛的稳定等价类。若 $E \oplus \mathbb{R}^m \cong F \oplus \mathbb{R}^n$，则 $\Sigma^m \text{Th}(E) \simeq \Sigma^n \text{Th}(F)$。

### (b) Thom 同构定理

**定理（Thom Isomorphism）**：设 $E \to X$ 是秩 $k$ 可定向实向量丛（或复向量丛，视为实丛）。则存在 **Thom 类** $u \in H^k(\text{Th}(E); R)$（$R = \mathbb{Z}$ 对可定向实丛或复丛，$R = \mathbb{Z}/2$ 对任意实丛），使得 cup 积给出同构：
$$\Phi: H^i(X; R) \xrightarrow{\cong} \widetilde{H}^{i+k}(\text{Th}(E); R), \quad \Phi(\alpha) = \pi^*\alpha \smile u$$

其中 $\pi: E \to X$ 是投影，$\pi^*: H^i(X) \to H^i(D(E)) \cong H^i(E)$ 是同构（因 $D(E)$ 形变收缩到 $X$）。

**证明**：

**步骤 1：Thom 类的存在性**

利用 Leray-Hirsch 定理。考虑纤维 $F \cong \mathbb{R}^k$，$\text{Th}(F) \cong S^k$。可定向性意味着 $H^k(S^k; \mathbb{Z}) \cong \mathbb{Z}$ 有典范生成元（由定向确定）。

对每点 $x \in X$，纤维的 Thom 空间是 $S^k$，$H^k(S^k) \cong \mathbb{Z}$。可定向性保证这些生成元可连续（局部地）选择。由纤维丛的上同调理论（Leray-Hirsch），整体 Thom 类 $u \in H^k(\text{Th}(E))$ 存在且限制到每纤维是生成元。

**步骤 2：同构的证明**

考虑相对上同调长正合列：
$$\cdots \to H^*(D(E)) \to H^*(S(E)) \to H^{*+1}(\text{Th}(E)) \to \cdots$$

利用 Gysin 序列：对可定向球丛 $S^{k-1} \to S(E) \to X$：
$$\cdots \to H^{i-k}(X) \xrightarrow{\cup e} H^i(X) \to H^i(S(E)) \to H^{i-k+1}(X) \to \cdots$$

其中 $e \in H^k(X)$ 是 Euler 类。结合 Thom 类的定义 $u$ 与 Euler 类的关系 $i^*u = e$（$i: X \hookrightarrow \text{Th}(E)$ 是零截面），可得 Thom 同构。

更直接地：对 $X$ 的 CW 结构归纳。若 $X = pt$，$\text{Th}(E) = S^k$，$\Phi: H^0(pt) \to \widetilde{H}^k(S^k)$ 将 $1 \mapsto u$（生成元），是同构。对一般 $X$，利用 Mayer-Vietoris 和局部平凡性。

**步骤 3：与 Euler 类的关系**

零截面 $s_0: X \to E$，$x \mapsto 0_x$，给出 $X \hookrightarrow \text{Th}(E)$（避开无穷远点）。则：
$$s_0^*(u) = e(E) \in H^k(X)$$
是 $E$ 的 Euler 类。这是因为 $u$ 限制到每纤维是生成元，而零截面是纤维的"中心"。

### (c) MSO 和 MO 的上同调环

**Thom 谱**：对 $k = 1, 2, \ldots$，令 $\gamma^k \to BSO(k)$（或 $BO(k)$）是万有定向（或任意）$k$-平面丛。定义：
$$MSO(k) = \text{Th}(\gamma^k), \quad MO(k) = \text{Th}(\gamma_{universal}^k \to BO(k))$$

bonding maps 由 $BSO(k) \to BSO(k+1)$ 的万有丛映射诱导：
$$S^1 \wedge MSO(k) \to MSO(k+1)$$

（因 $\gamma^{k+1}|_{BSO(k)} \cong \gamma^k \oplus \mathbb{R}$，其 Thom 空间满足 $\text{Th}(\gamma^k \oplus \mathbb{R}) = \Sigma \text{Th}(\gamma^k)$。）

**定理（Thom, 1954）**：

**(1) MO 的上同调**：
$$H^*(MO; \mathbb{Z}/2) \cong \mathbb{Z}/2[w_1, w_2, w_3, \ldots]$$

其中 $w_i$ 是万有 Stiefel-Whitney 类，$|w_i| = i$。

*证明*：由 Thom 同构，$H^*(MO(k); \mathbb{Z}/2) \cong \widetilde{H}^{*+k}(\text{Th}(\gamma^k))$。而 $H^*(BO(k); \mathbb{Z}/2) \cong \mathbb{Z}/2[w_1, \ldots, w_k]$。Thom 同构将 $H^*(BO(k))$ 提升到 $H^{*+k}(\text{Th}(\gamma^k))$。取极限 $k \to \infty$ 得上述多项式环。

**(2) MSO 的有理上同调**：
$$H^*(MSO; \mathbb{Q}) \cong \mathbb{Q}[p_1, p_2, p_3, \ldots]$$

其中 $p_i$ 是万有 Pontryagin 类，$|p_i| = 4i$。

*证明*：类似地，$H^*(BSO(k); \mathbb{Q}) \cong \mathbb{Q}[p_1, \ldots, p_{\lfloor k/2 \rfloor}]$。Thom 同构（可定向情形，系数 $\mathbb{Q}$）提升到 Thom 谱。

**(3) MSO 的 $\mathbb{Z}/2$ 上同调**：更复杂，包含挠元。Thom 证明了：
$$H^*(MSO; \mathbb{Z}/2) \cong H^*(BSO; \mathbb{Z}/2) \cdot u \cong \mathbb{Z}/2[w_2, w_3, \ldots] \cdot u$$

但注意 $w_1 = 0$ 在 $BSO$ 上（可定向性）。完整的环结构涉及 $Sq^i(u)$ 的关系，由 Wu 公式给出。

**配边环的计算**：

Thom 的关键定理：$\Omega_*^{SO} \cong \pi_*^{SO} \cong \pi_{*+k}(MSO(k))$（稳定极限）。结合 $H^*(MSO)$ 的计算和 Adams 谱序列，Thom 证明了：

- $\Omega_*^{SO} \otimes \mathbb{Q} \cong \mathbb{Q}[\mathbb{C}P^2, \mathbb{C}P^4, \ldots]$（由 Pontryagin 数生成）
- $\Omega_*^{SO}$ 无奇挠（即无 $p$-挠，$p > 2$）
- $2$-挠部分由 Milnor 和 Wall 后来完全确定

对非定向配边：
$$\Omega_*^O \cong \pi_*^O \cong \pi_{*+k}(MO(k))$$
Thom 证明了 $\Omega_*^O \cong \mathbb{Z}/2[x_2, x_4, x_5, x_6, x_8, \ldots]$（某些维数的生成元），由 Stiefel-Whitney 数完全分类。

**常见错误**：
- 将 Thom 空间与球丛混淆：Thom 空间 $D(E)/S(E)$ 不是 $S(E)$，而是将 $S(E)$ 捏合成一点。
- 忽视可定向性条件：Thom 同构对非定向丛需 $\mathbb{Z}/2$ 系数。对整数系数，可定向性是必要的。
- 混淆 MSO 和 MO 的生成元：MSO 涉及 Pontryagin 类（偶数次），MO 涉及所有 Stiefel-Whitney 类。

**参考文献**：
- R. Thom, "Quelques proprietes globales des varietes differentiables", *Ann. Math.* 1954
- J. Milnor, J. Stasheff, *Characteristic Classes*, Princeton, 1974
- J. F. Adams, *Stable Homotopy and Generalised Homology*, Chicago, 1974
- R. E. Stong, *Notes on Cobordism Theory*, Princeton, 1968
