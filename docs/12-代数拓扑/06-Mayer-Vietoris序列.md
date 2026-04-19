---
msc_primary: 55N10
msc_secondary:
  - 55U30
  - 55Q05
processed_at: '2026-04-20'
title: Mayer-Vietoris序列
---

# Mayer-Vietoris序列

## 1. 引言

Mayer-Vietoris序列是计算同调群的核心工具之一，由奥地利数学家Walther Mayer和Leopold Vietoris在1929-1930年间独立提出。它将空间 $X$ 的同调与其两个开子集 $U$ 和 $V$ 的同调（以及它们交集 $U \cap V$ 的同调）联系起来，形成一个长正合序列。这与Van Kampen定理在基本群理论中的作用类似：Van Kampen将空间的基本群表为其开覆盖基本群的合积，而Mayer-Vietoris将空间的同调表为其开覆盖同调的"拼接"。本文建立Mayer-Vietoris序列的代数基础（蛇引理与长正合序列），给出序列的详细构造，并通过球面同调等经典计算展示其威力。

## 2. 正合序列与蛇引理

### 2.1 短正合序列

**定义 2.1**。交换群（或更一般的Abel范畴中的对象）的序列
$$\cdots \to A_{n+1} \xrightarrow{f_{n+1}} A_n \xrightarrow{f_n} A_{n-1} \to \cdots$$
称为**正合的**（exact），若对每个 $n$，$\operatorname{im} f_{n+1} = \ker f_n$。

**定义 2.2**。**短正合序列**形如
$$0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0,$$
即 $f$ 单射，$g$ 满射，$\operatorname{im} f = \ker g$。

### 2.2 蛇引理

**定理 2.3**（蛇引理）。设有交换图
$$\begin{array}{ccccccccc}
& & A & \xrightarrow{f} & B & \xrightarrow{g} & C & \to & 0 \\
& & \downarrow{\alpha} & & \downarrow{\beta} & & \downarrow{\gamma} & & \\
0 & \to & A' & \xrightarrow{f'} & B' & \xrightarrow{g'} & C' & &
\end{array}$$
两行皆正合。则存在**连接同态**（connecting homomorphism）$\delta: \ker \gamma \to \operatorname{coker} \alpha$ 使以下序列正合：
$$\ker \alpha \to \ker \beta \to \ker \gamma \xrightarrow{\delta} \operatorname{coker} \alpha \to \operatorname{coker} \beta \to \operatorname{coker} \gamma.$$

*证明概要*。对 $c \in \ker \gamma$，取 $b \in B$ 使 $g(b) = c$（$g$ 满）。则 $g'(\beta(b)) = \gamma(g(b)) = \gamma(c) = 0$，故 $\beta(b) \in \ker g' = \operatorname{im} f'$。取 $a' \in A'$ 使 $f'(a') = \beta(b)$。定义 $\delta(c) = a' + \operatorname{im} \alpha \in \operatorname{coker} \alpha$。验证良定义性和正合性。$\square$

### 2.3 链复形的长正合序列

**定理 2.4**。设 $0 \to A_\bullet \xrightarrow{f} B_\bullet \xrightarrow{g} C_\bullet \to 0$ 为链复形的短正合序列（即每层的 $0 \to A_n \to B_n \to C_n \to 0$ 皆短正合，且 $f, g$ 与边缘算子交换）。则存在自然的长正合序列
$$\cdots \to H_n(A) \xrightarrow{f_*} H_n(B) \xrightarrow{g_*} H_n(C) \xrightarrow{\delta} H_{n-1}(A) \to \cdots.$$

*证明*。对每层应用蛇引理，连接同态拼合为 $\delta: H_n(C) \to H_{n-1}(A)$。$\square$

## 3. Mayer-Vietoris序列的构造

### 3.1 序列的陈述

**定理 3.1**（Mayer-Vietoris）。设 $X = U \cup V$，其中 $U, V$ 为开集（或更一般地，$\{\mathring{U}, \mathring{V}\}$ 覆盖 $X$）。则存在长正合序列
$$\cdots \to H_n(U \cap V) \xrightarrow{(i_*, j_*)} H_n(U) \oplus H_n(V) \xrightarrow{k_* - l_*} H_n(X) \xrightarrow{\partial} H_{n-1}(U \cap V) \to \cdots$$
其中 $i: U \cap V \hookrightarrow U$，$j: U \cap V \hookrightarrow V$，$k: U \hookrightarrow X$，$l: V \hookrightarrow X$ 为包含映射。

### 3.2 证明概要

考虑链复形的短正合序列
$$0 \to S_n(U \cap V) \xrightarrow{(i_\sharp, j_\sharp)} S_n(U) \oplus S_n(V) \xrightarrow{k_\sharp - l_\sharp} S_n(U) + S_n(V) \to 0.$$

其中 $S_n(U) + S_n(V)$ 为 $S_n(X)$ 中由 $U$ 和 $V$ 中的奇异单形生成的子群。**关键事实**（小单形引理/barycentric subdivision）：包含 $S_n(U) + S_n(V) \hookrightarrow S_n(X)$ 诱导同调同构。这是因为任何奇异链经重心细分足够多次后，每个单形将完全落在 $U$ 或 $V$ 中。

由链复形长正合序列即得Mayer-Vietoris序列。$\square$

## 4. 简化版与约化同调

### 4.1 约化同调

**定义 4.1**。在链复形末端追加 $S_{-1}(X) = \mathbb{Z}$，$\partial_0(\sigma) = 1$（对每个0-单形），得到**增广链复形**。其同调称为**约化同调** $\tilde{H}_n(X)$。显然 $\tilde{H}_n(X) = H_n(X)$（$n > 0$），$\tilde{H}_0(X) \oplus \mathbb{Z} \cong H_0(X)$。

### 4.2 约化Mayer-Vietoris

对 $X = U \cup V$ 且 $U \cap V \neq \emptyset$，有
$$\cdots \to \tilde{H}_n(U \cap V) \to \tilde{H}_n(U) \oplus \tilde{H}_n(V) \to \tilde{H}_n(X) \to \tilde{H}_{n-1}(U \cap V) \to \cdots.$$

## 5. 应用：球面的同调

**定理 5.1**。$H_k(S^n) = \begin{cases} \mathbb{Z}, & k = 0, n, \\ 0, & \text{其他}. \end{cases}$

*证明*（归纳法，用Mayer-Vietoris）。对 $n = 0$，$S^0 = \{+1, -1\}$，$H_0(S^0) = \mathbb{Z}^2$，$H_k = 0$（$k > 0$）。

设结论对 $S^{n-1}$ 成立。将 $S^n$ 写为 $U \cup V$，其中 $U = S^n \setminus \{N\}$（北极），$V = S^n \setminus \{S\}$（南极）。则 $U, V \cong \mathbb{R}^n$ 可缩，$U \cap V \cong \mathbb{R}^n \setminus \{0\} \simeq S^{n-1}$。

约化Mayer-Vietoris：
$$\cdots \to \tilde{H}_k(S^{n-1}) \to \tilde{H}_k(U) \oplus \tilde{H}_k(V) \to \tilde{H}_k(S^n) \to \tilde{H}_{k-1}(S^{n-1}) \to \cdots$$

因 $U, V$ 可缩，$\tilde{H}_k(U) = \tilde{H}_k(V) = 0$。故
$$\tilde{H}_k(S^n) \cong \tilde{H}_{k-1}(S^{n-1}).$$

归纳：$\tilde{H}_n(S^n) \cong \tilde{H}_{n-1}(S^{n-1}) \cong \cdots \cong \tilde{H}_0(S^0) \cong \mathbb{Z}$。对 $k \neq n$，$
\tilde{H}_k(S^n) = 0$（因 $\tilde{H}_k(S^{n-1}) = 0$ 当 $k \neq n-1$）。$\square$

## 6. 应用：其他计算

### 6.1 轮胎面 $T^2$

将 $T^2$ 分为圆柱 $U$ 和 $V$（重叠为两个圆环）。用约化Mayer-Vietoris：$U \simeq S^1$，$V \simeq S^1$，$U \cap V \simeq S^1 \sqcup S^1$。

$$\cdots \to \tilde{H}_2(S^1 \sqcup S^1) \to \tilde{H}_2(S^1) \oplus \tilde{H}_2(S^1) \to \tilde{H}_2(T^2) \to \tilde{H}_1(S^1 \sqcup S^1) \to \cdots$$

$\tilde{H}_2(S^1) = 0$，$\tilde{H}_2(S^1 \sqcup S^1) = 0$。$\tilde{H}_1(S^1 \sqcup S^1) = \mathbb{Z}^2$。

继续计算得 $\tilde{H}_2(T^2) \cong \mathbb{Z}$，$\tilde{H}_1(T^2) \cong \mathbb{Z}^2$，与胞腔计算一致。

### 6.2 Klein瓶

类似分解（两Möbius带沿边界粘合），Mayer-Vietoris给出
$$H_1(K) = \mathbb{Z} \oplus \mathbb{Z}/2\mathbb{Z}, \quad H_2(K) = 0.$$

## 7. 与项目其他部分的关联

Mayer-Vietoris序列是同调计算的主力工具，与切除定理（见[05-奇异同调群](05-奇异同调群.md)）和胞腔分解方法互补。上同调版本同样存在，且与杯积结构相容（见[07-上同调环](07-上同调环.md)）。在层上同调中，Mayer-Vietoris型序列被Čech上同调和谱序列所推广。 snake lemma是Abel范畴中的基本工具，在同调代数（见`docs/02-代数结构/范畴论/05-Abel范畴.md`）中居于核心地位。

## 8. 参考文献

1. W. Mayer, "Über abstrakte Topologie", *Monatsh. Math. Phys.* 36 (1929), 1–42.
2. L. Vietoris, "Über die Homologiegruppen der Vereinigung zweier Komplexe", *Monatsh. Math. Phys.* 37 (1930), 159–162.
3. A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002.
4. J.R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984.
5. 尤承业，《基础拓扑学讲义》，北京大学出版社，1997。
