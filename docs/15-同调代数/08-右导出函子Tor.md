---
title: 右导出函子Tor
description: 系统介绍Tor_n函子的定义、基本性质、长正合列，以及与平坦模和张量积正合性的深刻联系。
msc_primary:
  - 18G15
msc_secondary:
  - 13D07
  - 16E30
processed_at: '2026-04-20'
references:
  textbooks:
    - id: weibel_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Charles A. Weibel
      publisher: Cambridge University Press
      year: 1994
      msc: 18-01
    - id: rotman_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Joseph J. Rotman
      publisher: Springer
      year: 2009
      msc: 18-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Tor函子

## 引言

Tor函子是张量积函子的左导出函子，是测量张量积偏离正合性的精确工具。张量积函子 $-\otimes_R N$ 是右正合的：对短正合列 $0 \to M' \to M \to M'' \to 0$，序列
$$M' \otimes N \to M \otimes N \to M'' \otimes N \to 0$$
仍正合，但左端 $M' \otimes N \to M \otimes N$ 未必是单射。Tor函子 $\operatorname{Tor}_n^R(M,N)$ 精确量化了这一"失败"，其中 $\operatorname{Tor}_1$ 直接测量单射的破坏，而高阶Tor则提供系统的高阶障碍。

本教程从Tor的定义出发，证明其对称性、建立长正合列，给出平坦模的Tor判据，并通过具体例子展示计算技巧。

---

## 1. Tor的定义

### 1.1 通过投射分解

设 $R$ 为环，$M, N$ 为右/左 $R$-模（为简化记号，以下假设 $R$ 交换，不区分左右模）。

**定义 1.1**。取 $M$ 的一个 **投射分解**（projective resolution）
$$\cdots \to P_2 \xrightarrow{d_2} P_1 \xrightarrow{d_1} P_0 \xrightarrow{\varepsilon} M \to 0,$$
其中每个 $P_n$ 为投射 $R$-模。对复形 $P_\bullet$ 应用张量积 $-\otimes_R N$，得
$$\cdots \to P_2 \otimes N \xrightarrow{d_2 \otimes \mathrm{id}} P_1 \otimes N \xrightarrow{d_1 \otimes \mathrm{id}} P_0 \otimes N \to 0.$$

**定义 1.2（Tor函子）**。第 $n$ 个Tor群定义为
$$\operatorname{Tor}_n^R(M, N) := H_n(P_\bullet \otimes_R N) = \frac{\ker(d_n \otimes \mathrm{id})}{\operatorname{im}(d_{n+1} \otimes \mathrm{id})}.$$

### 1.2 通过 $N$ 的分解

**定理 1.1（对称性）**。若取 $N$ 的投射分解 $Q_\bullet \to N$，则
$$H_n(M \otimes_R Q_\bullet) \cong \operatorname{Tor}_n^R(M, N).$$
更精确地，存在自然的同构
$$\operatorname{Tor}_n^R(M, N) \cong \operatorname{Tor}_n^R(N, M)$$
（当 $R$ 交换时；非交换情形需对左右模作适当调整）。

**证明概要**：取 $M$ 和 $N$ 的投射分解 $P_\bullet, Q_\bullet$。构造双复形 $P_\bullet \otimes Q_\bullet$，其全复形的同调既可通过先计算 $P_\bullet \otimes N$（得 $\operatorname{Tor}_*(M,N)$）也可通过先计算 $M \otimes Q_\bullet$（得 $\operatorname{Tor}_*(N,M)$）得到。由谱序列的收敛唯一性，两者同构。∎

---

## 2. 基本性质

### 2.1 低维解释

**命题 2.1**。$\operatorname{Tor}_0^R(M, N) \cong M \otimes_R N$。

**证明**：$\operatorname{Tor}_0 = H_0(P_\bullet \otimes N) = \operatorname{coker}(d_1 \otimes \mathrm{id}) = P_0 \otimes N / \operatorname{im}(d_1 \otimes \mathrm{id}) \cong (P_0/\operatorname{im}d_1) \otimes N \cong M \otimes N$（因 $-\otimes N$ 右正合）。∎

**命题 2.2**。若 $M$ 或 $N$ 为平坦模，则 $\operatorname{Tor}_n^R(M, N) = 0$ 对所有 $n \geq 1$。

**证明**：若 $M$ 平坦，取 $N$ 的投射分解 $Q_\bullet \to N$。因 $M \otimes -$ 正合，$M \otimes Q_\bullet$ 是正合列（除 $M \otimes Q_0 \to M \otimes N \to 0$ 外处处正合），故 $H_n = 0$ 对 $n \geq 1$。∎

### 2.2 长正合列

**定理 2.1**。给定短正合列 $0 \to M' \to M \to M'' \to 0$，对每个 $N$ 有自然的长正合列
$$\cdots \to \operatorname{Tor}_n(M', N) \to \operatorname{Tor}_n(M, N) \to \operatorname{Tor}_n(M'', N) \xrightarrow{\partial} \operatorname{Tor}_{n-1}(M', N) \to \cdots$$
$$\cdots \to \operatorname{Tor}_1(M'', N) \to M' \otimes N \to M \otimes N \to M'' \otimes N \to 0.$$

**证明**：取 $M''$ 的投射分解的提升，由马蹄引理（horseshoe lemma）得到 $M$ 的投射分解，使得 $0 \to P'_\bullet \to P_\bullet \to P''_\bullet \to 0$ 为复形的短正合列。因每个 $P''_n$ 投射，该序列分裂。对 $-\otimes N$ 仍保持短正合，由蛇形引理得长正合列。∎

---

## 3. 平坦模的Tor判据

### 3.1 平坦模的定义回顾

**定义 3.1**。$R$-模 $N$ 称为 **平坦** 的，若 $-\otimes_R N$ 是正合函子，即对任意单射 $M' \hookrightarrow M$，$M' \otimes N \to M \otimes N$ 仍为单射。

### 3.2 Tor判据

**定理 3.1（平坦性的Tor判据）**。以下条件等价：
1. $N$ 为平坦模；
2. $\operatorname{Tor}_1^R(M, N) = 0$ 对所有 $R$-模 $M$；
3. $\operatorname{Tor}_n^R(M, N) = 0$ 对所有 $R$-模 $M$ 和 $n \geq 1$。

**证明**：$(1) \Rightarrow (3)$：由命题2.2。$(3) \Rightarrow (2)$：显然。$(2) \Rightarrow (1)$：对单射 $M' \hookrightarrow M$，长正合列给出
$$\operatorname{Tor}_1(M'', N) \to M' \otimes N \to M \otimes N \to M'' \otimes N \to 0.$$
若 $\operatorname{Tor}_1(M'', N) = 0$，则 $M' \otimes N \to M \otimes N$ 为单射。∎

**定理 3.2（局部判据）**。设 $R$ 为交换环，$N$ 为有限表现 $R$-模。则 $N$ 平坦当且仅当 $N_{\mathfrak{p}}$ 为自由 $R_{\mathfrak{p}}$-模对所有素理想 $\mathfrak{p}$（即 $N$ 为局部自由模）。

---

## 4. 具体计算例子

### 例子 4.1：$\operatorname{Tor}_1^\mathbb{Z}(\mathbb{Z}/m, \mathbb{Z}/n)$

这是Tor计算中最经典的例子。

取 $\mathbb{Z}/m$ 的自由分解：
$$0 \to \mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \to \mathbb{Z}/m \to 0.$$

对 $-\otimes_\mathbb{Z} \mathbb{Z}/n$：
$$0 \to \operatorname{Tor}_1(\mathbb{Z}/m, \mathbb{Z}/n) \to \mathbb{Z} \otimes \mathbb{Z}/n \xrightarrow{\times m} \mathbb{Z} \otimes \mathbb{Z}/n \to \mathbb{Z}/m \otimes \mathbb{Z}/n \to 0.$$

即
$$0 \to \operatorname{Tor}_1 \to \mathbb{Z}/n \xrightarrow{\times m} \mathbb{Z}/n \to \mathbb{Z}/\gcd(m,n) \to 0.$$

映射 $\times m: \mathbb{Z}/n \to \mathbb{Z}/n$ 的核为
$$\ker(\times m) = \{[k] \in \mathbb{Z}/n : mk \equiv 0 \pmod n\} = \frac{n}{\gcd(m,n)}\mathbb{Z}/n \cong \mathbb{Z}/\gcd(m,n).$$

**结论**：
$$\operatorname{Tor}_1^\mathbb{Z}(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}.$$

**实例**：$\operatorname{Tor}_1(\mathbb{Z}/4, \mathbb{Z}/6) \cong \mathbb{Z}/2$；$\operatorname{Tor}_1(\mathbb{Z}/5, \mathbb{Z}/7) = 0$（因 $\gcd(5,7)=1$，反映 $\mathbb{Z}/5$ 和 $\mathbb{Z}/7$ 互素的挠性不相互作用）。

### 例子 4.2：$\operatorname{Tor}_1^{k[x]}(k, k)$

设 $R = k[x]$，$M = N = k$（$x$ 作用为0）。取 $k$ 的投射分解：
$$0 \to k[x] \xrightarrow{\times x} k[x] \to k \to 0.$$

对 $-\otimes_{k[x]} k$：
$$0 \to \operatorname{Tor}_1(k,k) \to k[x] \otimes k \xrightarrow{\times x} k[x] \otimes k \to k \otimes k \to 0.$$

$k[x] \otimes_{k[x]} k \cong k$，$x$ 在 $k$ 上作用为0，故 $\times x: k \to k$ 为零映射。因此
$$\operatorname{Tor}_1^{k[x]}(k,k) \cong \ker(0: k \to k) = k.$$

几何意义：在概形 $\mathbb{A}^1_k = \operatorname{Spec} k[x]$ 的原点 $x=0$ 处，$k$ 对应于结构层的剩余类域。非零的 $\operatorname{Tor}_1$ 反映了在原点处两个结构层"相交"的高阶信息，是相交理论中Tor代数的初等实例。

### 例子 4.3：$\operatorname{Tor}$ 与挠子模

设 $R$ 为整环，$K$ 为其分式域。对 $R$-模 $M$，定义 **挠子模**
$$T(M) := \{m \in M : \exists r \neq 0 \in R, \, rm = 0\}.$$

**定理 4.1**。$\operatorname{Tor}_1^R(M, K/R) \cong T(M)$。

**证明**：由短正合列 $0 \to R \to K \to K/R \to 0$ 及 $K$ 平坦（作为域上的向量空间），长正合列给出
$$0 = \operatorname{Tor}_1(M, K) \to \operatorname{Tor}_1(M, K/R) \to M \otimes R \to M \otimes K.$$
故 $\operatorname{Tor}_1(M, K/R) \cong \ker(M \to M \otimes K) = T(M)$。∎

---

## 5. 与已有文档的关联

- [11-平坦模](11-平坦模.md)：平坦模的系统理论与Tor判据。
- [05-投射分解](05-投射分解.md)：Tor由投射分解计算。
- [04-投射模与内射模](04-投射模与内射模.md)：投射模的性质与分解存在性。
- [同调代数-具体计算例子](同调代数-具体计算例子.md)：更多同调代数计算实例。
- [12-曲面相交理论](../../13-代数几何/12-曲面相交理论.md)：Tor在代数几何相交理论中的应用。

---

## 参考文献

1. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
2. H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton Univ. Press, 1956. (Ch. VI)
3. D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Springer, 1995. (Ch. 6)
4. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)

---

**适用**：docs/15-同调代数/
