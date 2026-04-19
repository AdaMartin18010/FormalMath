---
title: Ext与模扩张
description: 详细介绍Ext^1(A,B)与模的短正合列扩张之间的Baer和理论，以及Yoneda Ext的构造。
msc_primary:
  - 18G15
msc_secondary:
  - 16E30
  - 13D07
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

# Ext与模扩张

## 引言

在同调代数中，Ext函子不仅是一个抽象的导出函子，它还具有深刻的几何与代数意义：$\operatorname{Ext}^1_R(A, B)$ 精确分类了 $R$-模 $A$ 由 $B$ 的短正合列扩张。这一对应由Baer在1934年系统建立，它将同调类的加法运算转化为扩张的Baer和，使得Ext成为研究模结构的直观工具。更高阶的Yoneda Ext则将这一对应推广到 $n$-步扩张，构成了同调代数中理论与计算交汇的典范。

本教程从模扩张的等价类出发，严格构造Baer和，证明Baer群与 $\operatorname{Ext}^1$ 的自然同构，并引入Yoneda Ext的高阶框架。

---

## 1. 模扩张的等价类

### 1.1 定义

设 $R$ 为环，$A, B$ 为 $R$-模。

**定义 1.1（模扩张）**。一个 $A$ 由 $B$ 的 **扩张**（extension）是指一个短正合列
$$0 \longrightarrow B \xrightarrow{\iota} E \xrightarrow{\pi} A \longrightarrow 0. \tag{E}$$

**定义 1.2（扩张的等价）**。两个扩张 $0 \to B \to E \to A \to 0$ 和 $0 \to B \to E' \to A \to 0$ 称为 **等价**，如果存在 $R$-模同态 $\phi: E \to E'$ 使得下图交换：
$$\begin{array}{ccccccccc}
0 & \to & B & \to & E & \to & A & \to & 0 \\
  &     & \downarrow^{\mathrm{id}} & & \downarrow^{\phi} & & \downarrow^{\mathrm{id}} & & \\
0 & \to & B & \to & E' & \to & A & \to & 0
\end{array}$$
由五引理，$\phi$ 必为同构。等价类的集合记为 $\mathcal{E}(A, B)$。

---

## 2. Baer和的构造

### 2.1 纤维积

给定两个扩张 $\mathcal{E}_1: 0 \to B \to E_1 \to A \to 0$ 和 $\mathcal{E}_2: 0 \to B \to E_2 \to A \to 0$，首先构造 **纤维积**（fiber product / pullback）：
$$E_1 \times_A E_2 := \{(e_1, e_2) \in E_1 \oplus E_2 : \pi_1(e_1) = \pi_2(e_2)\}.$$

映射 $\tilde{\pi}: E_1 \times_A E_2 \to A$，$(e_1, e_2) \mapsto \pi_1(e_1) = \pi_2(e_2)$ 为满射。其核为
$$\ker\tilde{\pi} = \{(b_1, b_2) \in B \oplus B\} = B \oplus B.$$

### 2.2 Baer和的商构造

**定义 2.1（Baer和）**。定义对角同态与反同态
$$\nabla: B \to B \oplus B, \quad b \mapsto (b, -b),$$
$$\Delta: B \oplus B \to B, \quad (b_1, b_2) \mapsto b_1 + b_2.$$

Baer和扩张定义为
$$\mathcal{E}_1 + \mathcal{E}_2: \quad 0 \longrightarrow B \xrightarrow{\iota} \frac{E_1 \times_A E_2}{\nabla(B)} \xrightarrow{\bar{\pi}} A \longrightarrow 0,$$
其中 $\iota(b) = [(\iota_1(b), 0)] = [(0, \iota_2(b))]$（因 $[(\iota_1(b),0)] - [(0,\iota_2(b))] = [(\iota_1(b), -\iota_2(b))] \in \nabla(B)$），$\bar{\pi}([e_1,e_2]) = \pi_1(e_1)$。

**定理 2.1**。Baer和给出 $\mathcal{E}(A,B)$ 上的Abel群结构：
- 零元为分裂扩张 $0 \to B \to B \oplus A \to A \to 0$；
- 逆元：$-[0 \to B \to E \to A \to 0] = [0 \to B \to E \to A \to 0]$，其中第二个扩张通过 $B$ 的自同构 $b \mapsto -b$ 得到。

---

## 3. Ext与扩张的精确对应

### 3.1 从扩张到Ext类

给定扩张 $0 \to B \to E \to A \to 0$，取 $A$ 的投射分解 $P_\bullet \to A$。由比较定理，存在链映射提升 $\tilde{f}: P_\bullet \to E_\bullet$（$E_\bullet$ 为扩张的投射分解）：
$$\begin{array}{ccccccccc}
\cdots & \to & P_1 & \to & P_0 & \to & A & \to & 0 \\
       &     & \downarrow &     & \downarrow &     & \downarrow &     & \\
0 & \to & B & \to & E & \to & A & \to & 0
\end{array}$$

映射 $f: P_1 \to B$ 满足 $f \circ d_2 = 0$（因下链只有两项），故 $f \in \ker(d^*: \operatorname{Hom}(P_1,B) \to \operatorname{Hom}(P_2,B))$。不同提升选择相差 $\operatorname{im}(d^*: \operatorname{Hom}(P_0,B) \to \operatorname{Hom}(P_1,B))$。因此 $[f] \in \operatorname{Ext}^1_R(A,B)$ 良定。

### 3.2 从Ext类到扩张

反之，给定 $[f] \in \operatorname{Ext}^1_R(A,B)$，可构造扩张如下。取 $P_1 \xrightarrow{d_1} P_0 \to A \to 0$（$P_0, P_1$ 投射）。因 $f \circ d_2 = 0$，$f$ 诱导 $f': P_1/\operatorname{im}d_2 \to B$。令 $E = (B \oplus P_0)/\{(f'(x), -d_1(x)) : x \in P_1/\operatorname{im}d_2\}$，则 $0 \to B \to E \to A \to 0$ 为所求扩张。

### 3.3 主定理

**定理 3.1（Baer, 1934）**。上述对应给出自然Abel群同构
$$\operatorname{Ext}^1_R(A, B) \cong \mathcal{E}(A, B).$$

**证明概要**：
1. **良定性**：从扩张到Ext类的构造不依赖于投射分解和提升的选择（由比较定理的同伦唯一性）。
2. **同态性**：两个扩张的Baer和对应于Ext类中的加法。这可通过纤维积的泛性质和投射分解的函子性验证。
3. **双射**：给定 $[f] \in \operatorname{Ext}^1$，构造的扩张在 $\mathcal{E}(A,B)$ 中映射回 $[f]$；反之，从扩张出发构造的Ext类再构造回等价的扩张。

详细验证参见 Weibel, *An Introduction to Homological Algebra*, Ch. 3.4。∎

---

## 4. Yoneda Ext

### 4.1 $n$-步扩张

**定义 4.1（$n$-步扩张）**。对 $n \geq 1$，一个 $n$-步扩张是长正合列
$$\mathcal{E}: \quad 0 \to B \to E_n \to E_{n-1} \to \cdots \to E_1 \to A \to 0.$$
两个 $n$-步扩张等价，如果存在链映射连接它们，且在两端为恒等映射。

**定义 4.2（Yoneda积）**。给定 $m$-步扩张 $0 \to C \to F_m \to \cdots \to B \to 0$ 和 $n$-步扩张 $0 \to B \to E_n \to \cdots \to A \to 0$，其 **Yoneda积** / **拼接**（splicing）为 $(m+n)$-步扩张：
$$0 \to C \to F_m \to \cdots \to E_n \to \cdots \to A \to 0.$$

### 4.2 Yoneda Ext群

**定理 4.1（Yoneda, 1954）**。$n$-步扩张的等价类集合在适当的等价关系下构成Abel群，记为 $\operatorname{YExt}^n_R(A,B)$。存在自然同构
$$\operatorname{YExt}^n_R(A,B) \cong \operatorname{Ext}^n_R(A,B).$$

对 $n=1$，此即Baer定理。对 $n \geq 2$，Yoneda Ext提供了Ext函子的具体"几何"实现。

---

## 5. 具体计算例子

### 例子 5.1：PID上的扩张分类

设 $R = \mathbb{Z}$，$A = \mathbb{Z}/p\mathbb{Z}$，$B = \mathbb{Z}/p\mathbb{Z}$（$p$ 为素数）。

由定理3.1和已知公式，$\operatorname{Ext}^1_\mathbb{Z}(\mathbb{Z}/p, \mathbb{Z}/p) \cong \mathbb{Z}/p\mathbb{Z}$。故恰有 $p$ 个不等价的扩张。

**具体构造**：对 $[k] \in \mathbb{Z}/p$，扩张为
$$0 \to \mathbb{Z}/p \xrightarrow{\iota_k} \mathbb{Z}/p^2 \xrightarrow{\pi_k} \mathbb{Z}/p \to 0,$$
其中 $\iota_k([1]) = [kp]$（$kp \in \mathbb{Z}/p^2$），$\pi_k([1]) = [1]$。注意当 $k \not\equiv 0 \pmod p$ 时，$\iota_k$ 仍为单射（因 $p \cdot kp = kp^2 \equiv 0$），且像为 $p$ 的倍数子群。$k=0$ 对应分裂扩张 $\mathbb{Z}/p \oplus \mathbb{Z}/p$（实际上 $\pi_0$ 的核为 $p\mathbb{Z}/p^2 \cong \mathbb{Z}/p$，分裂）。

验证：对 $p=2$，$\operatorname{Ext}^1(\mathbb{Z}/2, \mathbb{Z}/2) = \mathbb{Z}/2$。两个扩张为：
- 分裂：$\mathbb{Z}/2 \oplus \mathbb{Z}/2$（Klein四元群作为 $\mathbb{Z}$-模）。
- 非分裂：$0 \to \mathbb{Z}/2 \to \mathbb{Z}/4 \to \mathbb{Z}/2 \to 0$。

### 例子 5.2：$k[x]$-模的扩张

设 $R = k[x]$（$k$ 为域），$A = B = k$（$x$ 作用为0，即平凡模）。取 $A$ 的投射分解：
$$0 \to k[x] \xrightarrow{\times x} k[x] \to k \to 0.$$

计算 $\operatorname{Ext}^1_{k[x]}(k,k)$：
$$\operatorname{Ext}^1(k,k) = \frac{\ker(\operatorname{Hom}(k[x],k) \xrightarrow{0} 0)}{\operatorname{im}(\operatorname{Hom}(k[x],k) \xrightarrow{x^*} \operatorname{Hom}(k[x],k))}.$$

$\operatorname{Hom}_{k[x]}(k[x], k) \cong k$（由 $f(1)$ 决定）。$x^*(f)(1) = f(x \cdot 1) = x \cdot f(1) = 0$（因 $x$ 在 $k$ 上作用为0）。故 $\operatorname{im}x^* = 0$，$\ker = k$。因此
$$\operatorname{Ext}^1_{k[x]}(k,k) \cong k.$$

扩张 $0 \to k \to E \to k \to 0$ 对应于 $k[x]$-模 $E = k^2$，$x$ 的作用由Jordan块 $\begin{pmatrix} 0 & a \\ 0 & 0 \end{pmatrix}$（$a \in k$）给出。$a=0$ 为分裂扩张；$a \neq 0$ 彼此同构（通过基变换），故恰有一个非平凡扩张类。

---

## 6. 与已有文档的关联

- [07-左导出函子Ext](07-左导出函子Ext.md)：Ext函子的定义、长正合序列与基本计算。
- [09-Ext与群扩张](09-Ext与群扩张.md)：群扩张是模扩张在 $R = \mathbb{Z}Q$ 时的特殊情形。
- [04-投射模与内射模](04-投射模与内射模.md)：投射分解的存在性是Ext计算的前提。
- [05-投射分解](05-投射分解.md)：投射分解的显式构造。

---

## 参考文献

1. R. Baer, "Erweiterung von Gruppen und ihren Isomorphismen", *Math. Z.*, 38:375–416, 1934.
2. N. Yoneda, "On Ext and exact sequences", *J. Fac. Sci. Univ. Tokyo*, Sect. I, 8:507–576, 1960.
3. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
4. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)

---

**适用**：docs/15-同调代数/
