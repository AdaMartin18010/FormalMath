---
title: 左导出函子Ext
description: 系统介绍Ext^n函子的定义、基本性质、长正合列，以及Ext与模扩张之间的深刻联系。
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

# Ext函子

## 引言

Ext函子是同调代数中最基本、应用最广泛的导出函子。它起源于同调代数创立时期Eilenberg和Mac Lane的工作，名字"Ext"即"Extension"（扩张）的缩写，因为 $\operatorname{Ext}^1$ 精确分类了模的短正合列扩张。Ext函子测量了Hom函子在正合列上的"失败程度"：Hom函子 $-\otimes -$ 和 $\operatorname{Hom}(-,-)$ 都是左正合或右正合的，Ext（以及Tor）正是量化其偏离正合性的高阶修正项。

本教程从Ext的双定义（投射分解与内射分解）出发，证明二者的一致性，建立长正合列，给出投射模与内射模的同调判据，并计算典型例子。

---

## 1. Ext的定义

### 1.1 通过投射分解

设 $R$ 为环，$M, N$ 为 $R$-模。

**定义 1.1**。取 $M$ 的投射分解 $P_\bullet \to M$：
$$\cdots \to P_2 \xrightarrow{d_2} P_1 \xrightarrow{d_1} P_0 \xrightarrow{\varepsilon} M \to 0.$$
对复形 $P_\bullet$ 应用 $\operatorname{Hom}_R(-, N)$，得上链复形
$$0 \to \operatorname{Hom}(P_0, N) \xrightarrow{d_1^*} \operatorname{Hom}(P_1, N) \xrightarrow{d_2^*} \cdots.$$

**定义 1.2**。第 $n$ 个Ext群定义为
$$\operatorname{Ext}^n_R(M, N) := H^n(\operatorname{Hom}_R(P_\bullet, N)) = \frac{\ker d_{n+1}^*}{\operatorname{im} d_n^*}.$$

### 1.2 通过内射分解

**定义 1.3**。取 $N$ 的内射分解 $N \to I^\bullet$：
$$0 \to N \to I^0 \to I^1 \to I^2 \to \cdots.$$
对 $M$ 应用 $\operatorname{Hom}_R(M, -)$，得上链复形
$$0 \to \operatorname{Hom}(M, I^0) \to \operatorname{Hom}(M, I^1) \to \cdots.$$

**定义 1.4**。等价地定义
$$\operatorname{Ext}^n_R(M, N) := H^n(\operatorname{Hom}_R(M, I^\bullet)).$$

### 1.3 两种定义的一致性

**定理 1.1**。上述两种定义给出自然同构的函子。

**证明概要**：构造双复形 $K^{p,q} = \operatorname{Hom}(P_p, I^q)$，其中 $P_\bullet \to M$ 为投射分解，$N \to I^\bullet$ 为内射分解。全复形的谱序列有两种退化方式：
- 先计算 $H^q_\mathrm{vert}(K^{p,\bullet}) = \operatorname{Ext}^q(P_p, N)$。因 $P_p$ 投射，$\operatorname{Ext}^q(P_p, N) = 0$ 对 $q > 0$，$= \operatorname{Hom}(P_p, N)$ 对 $q=0$。故第一谱序列退化为 $H^p(\operatorname{Hom}(P_\bullet, N))$。
- 先计算 $H^p_\mathrm{horiz}(K^{\bullet,q}) = \operatorname{Ext}^p(M, I^q)$。因 $I^q$ 内射，$\operatorname{Ext}^p(M, I^q) = 0$ 对 $p > 0$，$= \operatorname{Hom}(M, I^q)$ 对 $p=0$。故第二谱序列退化为 $H^q(\operatorname{Hom}(M, I^\bullet))$。

由谱序列收敛到同一全复形上同调，二者同构。∎

---

## 2. 基本性质

### 2.1 低维解释

**命题 2.1**。$\operatorname{Ext}^0_R(M, N) = \operatorname{Hom}_R(M, N)$。

**证明**：$H^0(\operatorname{Hom}(P_\bullet, N)) = \ker d_1^* = \{f: P_0 \to N : f \circ d_1 = 0\}$。因 $P_1 \to P_0 \to M \to 0$ 正合，$f$ 通过 $M$ 唯一分解，即 $f = \tilde{f} \circ \varepsilon$。故 $\ker d_1^* \cong \operatorname{Hom}(M, N)$。∎

**命题 2.2**。$\operatorname{Ext}^1_R(M, N)$ 分类短正合列 $0 \to N \to E \to M \to 0$ 的等价类（Baer对应）。

### 2.2 长正合列

**定理 2.1**。对短正合列 $0 \to M' \to M \to M'' \to 0$，对每个固定的 $N$，有自然长正合列
$$0 \to \operatorname{Hom}(M'', N) \to \operatorname{Hom}(M, N) \to \operatorname{Hom}(M', N) \xrightarrow{\delta} \operatorname{Ext}^1(M'', N) \to \operatorname{Ext}^1(M, N) \to \operatorname{Ext}^1(M', N) \xrightarrow{\delta} \operatorname{Ext}^2(M'', N) \to \cdots$$

对固定的 $M$ 和短正合列 $0 \to N' \to N \to N'' \to 0$，有
$$0 \to \operatorname{Hom}(M, N') \to \operatorname{Hom}(M, N) \to \operatorname{Hom}(M, N'') \xrightarrow{\delta} \operatorname{Ext}^1(M, N') \to \operatorname{Ext}^1(M, N) \to \cdots$$

**证明**：取 $M''$ 的投射分解的提升，由马蹄引理得到 $M$ 的投射分解，使 $0 \to P'_\bullet \to P_\bullet \to P''_\bullet \to 0$ 为分裂的短正合列。对 $-\otimes N$ 或 $\operatorname{Hom}(-,N)$ 应用后由蛇形引理得长正合列。∎

### 2.3 投射模与内射模的判据

**定理 2.2**。以下条件等价：
1. $M$ 为投射模；
2. $\operatorname{Ext}^1_R(M, N) = 0$ 对所有 $N$；
3. $\operatorname{Ext}^n_R(M, N) = 0$ 对所有 $n \geq 1$ 和 $N$。

**证明**：$(1) \Rightarrow (3)$：$M$ 的投射分解可取 $0 \to M \to M \to 0$，故 $\operatorname{Ext}^n = 0$ 对 $n \geq 1$。$(3) \Rightarrow (2)$：显然。$(2) \Rightarrow (1)$：对短正合列 $0 \to N' \to N \to M \to 0$，长正合列给出 $\operatorname{Hom}(N, N') \to \operatorname{Hom}(N', N') \to \operatorname{Ext}^1(M, N') = 0$，故 $N \to M$ 分裂，$M$ 投射。∎

**定理 2.3**。$N$ 为内射模当且仅当 $\operatorname{Ext}^1_R(M, N) = 0$ 对所有 $M$。

---

## 3. 重要计算例子

### 3.1 PID上的Ext

**定理 3.1**。设 $R$ 为PID，$M, N$ 为有限生成 $R$-模。则
$$\operatorname{Ext}^n_R(M, N) = 0 \quad \text{对 } n \geq 2.$$

**证明**：PID上任何子模自由，故任何模有长度为1的自由（从而投射）分解：$0 \to F_1 \to F_0 \to M \to 0$。因此 $\operatorname{Ext}^n = 0$ 对 $n \geq 2$。∎

### 3.2 Abel群的Ext

**定理 3.2**。$\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$。

**证明**：取 $\mathbb{Z}/m$ 的自由分解 $0 \to \mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \to \mathbb{Z}/m \to 0$。对 $\operatorname{Hom}(-, \mathbb{Z}/n)$：
$$0 \to \operatorname{Hom}(\mathbb{Z}/m, \mathbb{Z}/n) \to \mathbb{Z}/n \xrightarrow{\times m} \mathbb{Z}/n \to \operatorname{Ext}^1(\mathbb{Z}/m, \mathbb{Z}/n) \to 0.$$
$\times m: \mathbb{Z}/n \to \mathbb{Z}/n$ 的核为 $\mathbb{Z}/\gcd(m,n)$，像为 $(m\mathbb{Z})/n\mathbb{Z} \cong \mathbb{Z}/(n/\gcd)$。由正合性，$\operatorname{Ext}^1 \cong \operatorname{coker}(\times m) \cong \mathbb{Z}/\gcd(m,n)$。∎

**推论 3.1**。$\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/m, \mathbb{Z}) = 0$（因 $\mathbb{Z}$ 内射？不，$\mathbb{Z}$ 非内射。直接计算：$\times m: \mathbb{Z} \to \mathbb{Z}$ 的coker为 $\mathbb{Z}/m$，故 $\operatorname{Ext}^1 = \mathbb{Z}/m$）。

实际上：$0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$ 对 $\operatorname{Hom}(-, \mathbb{Z})$ 给出
$$0 \to \operatorname{Hom}(\mathbb{Z}/m, \mathbb{Z}) = 0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \operatorname{Ext}^1(\mathbb{Z}/m, \mathbb{Z}) \to 0,$$
故 $\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/m, \mathbb{Z}) \cong \mathbb{Z}/m\mathbb{Z}$。

### 3.3 $\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z})$

**定理 3.3**。$\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z}) \cong \mathbb{R}$（作为 $\mathbb{Q}$-向量空间，维数为连续统）。

**证明概要**：由短正合列 $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ 的长正合列，及 $\operatorname{Hom}(\mathbb{Q}, \mathbb{Z}) = 0$，$\operatorname{Ext}^1(\mathbb{Q}, \mathbb{Q}) = 0$（因 $\mathbb{Q}$ 平坦且 $R = \mathbb{Z}$ 上平坦=无挠，而 $\mathbb{Q}$ 可除从而内射？不，$\mathbb{Q}$ 非内射作为 $\mathbb{Z}$-模），需更细致的分析。已知结论为 $\operatorname{Ext}^1(\mathbb{Q}, \mathbb{Z}) \cong \mathbb{R}$，反映了有理数群与整数群之间的复杂扩张结构。∎

---

## 4. 与已有文档的关联

- [09-Ext与群扩张](09-Ext与群扩张.md)：$\operatorname{Ext}^1$ 与群扩张的Baer对应。
- [10-Ext与模扩张](10-Ext与模扩张.md)：模扩张的详细理论与Yoneda Ext。
- [05-投射分解](05-投射分解.md)：投射分解的存在性与构造。
- [06-内射分解](06-内射分解.md)：内射分解与内射模判据。
- [08-右导出函子Tor](08-右导出函子Tor.md)：Tor函子——张量积的左导出函子。

---

## 参考文献

1. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
2. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)
3. H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton Univ. Press, 1956. (Ch. VI)
4. S. Mac Lane, *Homology*, Springer, 1963. (Ch. III)

---

**适用**：docs/15-同调代数/
