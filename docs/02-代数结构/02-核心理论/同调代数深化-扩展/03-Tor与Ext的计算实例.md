---
msc_primary: 18G15
msc_secondary:
- 16E30
- 13D07
- 18G10
title: 15.3 Tor与Ext的计算实例 / Computational Examples of Tor and Ext
processed_at: '2026-04-05'
---
# 15.3 Tor与Ext的计算实例 / Computational Examples of Tor and Ext

**主题编号**: B.15.03
**创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日

---

## 目录 / Table of Contents

- [15.3 Tor与Ext的计算实例 / Computational Examples of Tor and Ext](#153-tor与ext的计算实例--computational-examples-of-tor-and-ext)
  - [目录 / Table of Contents](#目录)
  - [15.3.1 引言 / Introduction](#1531-引言--introduction)
  - [15.3.2 Tor函子的定义与基本性质 / Definition and Basic Properties of Tor](#1532-tor函子的定义与基本性质--definition-and-basic-properties-of-tor)
    - [作为导出张量积 / Tor as Derived Tensor Product](#作为导出张量积--tor-as-derived-tensor-product)
    - [Tor的对称性与平坦性判据 / Symmetry and Flatness Criterion](#tor的对称性与平坦性判据--symmetry-and-flatness-criterion)
  - [15.3.3 Ext函子的定义与基本性质 / Definition and Basic Properties of Ext](#1533-ext函子的定义与基本性质--definition-and-basic-properties-of-ext)
    - [作为导出Hom函子 / Ext as Derived Hom Functor](#作为导出hom函子--ext-as-derived-hom-functor)
    - [Ext与模扩张 / Ext and Module Extensions](#ext与模扩张--ext-and-module-extensions)
  - [15.3.4 Tor的具体计算 / Concrete Computations of Tor](#1534-tor的具体计算--concrete-computations-of-tor)
    - [主理想整环上的Tor / Tor over PID](#主理想整环上的tor--tor-over-pid)
    - [多项式环上的Tor / Tor over Polynomial Rings](#多项式环上的tor--tor-over-polynomial-rings)
  - [15.3.5 Ext的具体计算 / Concrete Computations of Ext](#1535-ext的具体计算--concrete-computations-of-ext)
    - [主理想整环上的Ext / Ext over PID](#主理想整环上的ext--ext-over-pid)
    - [Ext与群上同调的联系 / Connection with Group Cohomology](#ext与群上同调的联系--connection-with-group-cohomology)
  - [15.3.6 应用：群扩张与挠模 / Applications: Group Extensions and Torsion Modules](#1536-应用群扩张与挠模--applications-group-extensions-and-torsion-modules)
  - [15.3.7 参考文献 / References](#1537-参考文献--references)

---

## 15.3.1 引言 / Introduction

$\operatorname{Tor}$ 和 $\operatorname{Ext}$ 是同调代数中最基本、应用最广泛的导出函子。$\operatorname{Tor}_n^R(M, N)$ 度量了张量积函子 $M \otimes_R -$（或 $- \otimes_R N$）破坏正合性的程度，而 $\operatorname{Ext}_R^n(M, N)$ 度量了 Hom 函子 $\operatorname{Hom}_R(M, -)$（或 $\operatorname{Hom}_R(-, N)$）破坏正合性的程度。这两个函子不仅在纯代数中举足轻重，也是代数拓扑、代数几何和表示论的常用工具。

**Tor and Ext are the most fundamental and widely applied derived functors in homological algebra. $\operatorname{Tor}_n^R(M, N)$ measures the failure of exactness of the tensor product functor $M \otimes_R -$ (or $- \otimes_R N$), while $\operatorname{Ext}_R^n(M, N)$ measures the failure of exactness of the Hom functor $\operatorname{Hom}_R(M, -)$ (or $\operatorname{Hom}_R(-, N)$). These functors are not only pivotal in pure algebra but also essential tools in algebraic topology, algebraic geometry, and representation theory.**

本文档专注于 $\operatorname{Tor}$ 和 $\operatorname{Ext}$ 的计算实例，从基础定义出发，通过主理想整环、多项式环等具体环上的计算，展示这些抽象函子的实际操作方法。

---

## 15.3.2 Tor函子的定义与基本性质 / Definition and Basic Properties of Tor

### 作为导出张量积 / Tor as Derived Tensor Product

**定义 15.3.1** ($\operatorname{Tor}$ 函子)
设 $R$ 是环，$M$ 是右 $R$-模，$N$ 是左 $R$-模。$\operatorname{Tor}_n^R(M, N)$ 定义为左导出函子 $L_n(M \otimes_R -)(N)$，即：

取 $N$ 的投射消解 $P_\bullet \to N$，则

$$
\operatorname{Tor}_n^R(M, N) = H_n(M \otimes_R P_\bullet)
$$

等价地，可取 $M$ 的投射消解 $Q_\bullet \to M$，定义

$$
\operatorname{Tor}_n^R(M, N) = H_n(Q_\bullet \otimes_R N)
$$

**定理 15.3.1** ($\operatorname{Tor}$ 的对称性)
上述两种定义给出自然同构的 Abel 群（或 $R$-模，当 $R$ 交换时）。即 $\operatorname{Tor}_n^R(M, N) \cong \operatorname{Tor}_n^R(N, M)$（在 $R$ 交换时自然同构；非交换时需要适当的双模条件）。

**证明思路**：
考虑双复形 $Q_\bullet \otimes_R P_\bullet$。两种定义分别对应于先取横向同调或纵向同调。由于张量积与直和可交换，且 $Q_p$ 和 $P_q$ 都是投射模，双复形的全复形的两种谱序列均退化为 $E^2$ 页。由谱序列的比较定理（或直接利用平衡函子的经典结果），两种构造给出同构的结果。详见 Weibel [1, Theorem 2.7.2] 或 Mac Lane [2, Chapter V, §8]。

### Tor的对称性与平坦性判据 / Symmetry and Flatness Criterion

**命题 15.3.1**
1. $\operatorname{Tor}_0^R(M, N) \cong M \otimes_R N$
2. 若 $P$ 是投射模，则 $\operatorname{Tor}_n^R(P, N) = 0$ 对 $n > 0$ 成立
3. 若 $F$ 是平坦模，则 $\operatorname{Tor}_n^R(F, N) = 0$ 对 $n > 0$ 成立

**定理 15.3.2** (平坦性判据)
右 $R$-模 $M$ 是平坦的当且仅当对所有左 $R$-模 $N$ 和所有 $n > 0$ 有 $\operatorname{Tor}_n^R(M, N) = 0$。实际上，只需验证 $n = 1$ 即可：$M$ 平坦当且仅当 $\operatorname{Tor}_1^R(M, N) = 0$ 对所有 $N$ 成立。

**证明**：
($\Rightarrow$) 若 $M$ 平坦，则 $M \otimes_R -$ 是正合函子，因此其左导出函子全部为零。
($\Leftarrow$) 设 $\operatorname{Tor}_1^R(M, N) = 0$ 对所有 $N$ 成立。对任意短正合序列 $0 \to N' \to N \to N'' \to 0$，由左导出函子的长正合序列：

$$
\cdots \to \operatorname{Tor}_1^R(M, N'') \to M \otimes N' \to M \otimes N \to M \otimes N'' \to 0
$$

因 $\operatorname{Tor}_1^R(M, N'') = 0$，序列 $0 \to M \otimes N' \to M \otimes N \to M \otimes N'' \to 0$ 正合，故 $M$ 平坦。

---

## 15.3.3 Ext函子的定义与基本性质 / Definition and Basic Properties of Ext

### 作为导出Hom函子 / Ext as Derived Hom Functor

**定义 15.3.2** ($\operatorname{Ext}$ 函子)
设 $R$ 是环，$M, N$ 是左 $R$-模。$\operatorname{Ext}_R^n(M, N)$ 可定义为：

1. 取 $M$ 的投射消解 $P_\bullet \to M$，定义
   $$
   \operatorname{Ext}_R^n(M, N) = H^n(\operatorname{Hom}_R(P_\bullet, N))
   $$

2. 取 $N$ 的内射消解 $N \to I^\bullet$，定义
   $$
   \operatorname{Ext}_R^n(M, N) = H^n(\operatorname{Hom}_R(M, I^\bullet))
   $$

**定理 15.3.3** ($\operatorname{Ext}$ 的平衡性)
上述两种定义自然同构。

**证明思路**：
与 $\operatorname{Tor}$ 类似，考虑双复形 $\operatorname{Hom}_R(P_\bullet, I^\bullet)$。由于 $P_p$ 投射，$I^q$ 内射，双复形的两个谱序列均退化。这本质上是导出函子"平衡性"（balancing）的一个特例。详见 Weibel [1, Theorem 2.7.6]。

### Ext与模扩张 / Ext and Module Extensions

**定义 15.3.3** (模扩张 / Module Extension)
一个 $N$ 被 $M$ 的**扩张**（extension）是指一个短正合序列

$$
\mathcal{E}: \quad 0 \longrightarrow N \longrightarrow E \longrightarrow M \longrightarrow 0
$$

两个扩张 $\mathcal{E}$ 和 $\mathcal{E}'$ 称为**等价**，若存在交换图：

$$
\begin{array}{ccccccccc}
0 & \to & N & \to & E & \to & M & \to & 0 \\
 & & \downarrow^{=} & & \downarrow^{\cong} & & \downarrow^{=} & & \\
0 & \to & N & \to & E' & \to & M & \to & 0
\end{array}
$$

**定理 15.3.4** (Baer 和)
所有等价类的集合 $\operatorname{Ext}(M, N)$ 具有 Abel 群结构，称为**Baer 和**。零元对应于分裂扩张 $E = M \oplus N$。

**定理 15.3.5** ($\operatorname{Ext}^1$ 与扩张)
存在自然同构

$$
\operatorname{Ext}_R^1(M, N) \cong \operatorname{Ext}(M, N)
$$

将 $\operatorname{Ext}^1$ 中的元素与模扩张的等价类一一对应。

**证明思路**：
取 $M$ 的投射消解 $\cdots \to P_1 \xrightarrow{d_1} P_0 \to M \to 0$。一个 $\operatorname{Ext}^1$ 中的元素由 $\operatorname{Hom}(P_1, N)$ 中的上循环 $f: P_1 \to N$ 代表，满足 $f \circ d_2 = 0$。考虑推出（pushout）：

$$
\begin{array}{ccc}
P_1 & \xrightarrow{d_1} & P_0 \\
\downarrow{f} & & \downarrow \\
N & \longrightarrow & E
\end{array}
$$

这给出扩张 $0 \to N \to E \to M \to 0$。反之，给定一个扩张，利用 $P_0$ 的投射性提升 $P_0 \to M$ 到 $E$，再限制到核上得到 $P_1 \to N$。可以验证这是良定的双射，且保持群运算。

---

## 15.3.4 Tor的具体计算 / Concrete Computations of Tor

### 主理想整环上的Tor / Tor over PID

**定理 15.3.6** (PID 上的结构定理)
设 $R$ 是主理想整环，$M, N$ 是有限生成 $R$-模。则

$$
M \cong R^r \oplus \bigoplus_{i=1}^k R/(a_i), \quad N \cong R^s \oplus \bigoplus_{j=1}^l R/(b_j)
$$

由于 $\operatorname{Tor}$ 对直和可加且自由部分贡献为零，只需计算 $\operatorname{Tor}_1^R(R/(a), R/(b))$。

**计算**：取 $R/(a)$ 的投射消解：

$$
0 \longrightarrow R \xrightarrow{\times a} R \longrightarrow R/(a) \longrightarrow 0
$$

作用 $- \otimes_R R/(b)$：

$$
0 \longrightarrow R/(b) \xrightarrow{\times a} R/(b) \longrightarrow 0
$$

因此

$$
\operatorname{Tor}_1^R(R/(a), R/(b)) = \ker(\times a: R/(b) \to R/(b)) \cong R/\gcd(a,b)
$$

**例子 15.3.1** ($R = \mathbb{Z}$)

$$
\operatorname{Tor}_1^\mathbb{Z}(\mathbb{Z}/4\mathbb{Z}, \mathbb{Z}/6\mathbb{Z}) = \mathbb{Z}/2\mathbb{Z}
$$

因为 $\gcd(4, 6) = 2$。

**例子 15.3.2** ($R = k[x]$，$k$ 是域)
设 $M = k[x]/(x^2)$，$N = k[x]/(x^3)$，则

$$
\operatorname{Tor}_1^{k[x]}(M, N) \cong k[x]/(x^2)
$$

因为 $\gcd(x^2, x^3) = x^2$（在相伴意义下）。

### 多项式环上的Tor / Tor over Polynomial Rings

**例子 15.3.3** ($k[x, y]$ 上的 Tor)
设 $R = k[x, y]$，$M = R/(x)$，$N = R/(y)$。求 $\operatorname{Tor}_1^R(M, N)$ 和 $\operatorname{Tor}_2^R(M, N)$。

取 $M = R/(x)$ 的极小自由消解（Koszul 复形）：

$$
0 \longrightarrow R \xrightarrow{\cdot x} R \longrightarrow R/(x) \longrightarrow 0
$$

这不是完全的，因为 $R/(x)$ 作为 $R$-模有无限投射维数？不，$R = k[x,y]$ 中 $(x)$ 是由非零因子生成的理想，实际上 $R/(x)$ 的投射维数为 1。上面的消解是正确的。

作用 $- \otimes_R R/(y)$：

$$
0 \longrightarrow R/(y) \xrightarrow{\times x} R/(y) \longrightarrow R/(x, y) \longrightarrow 0
$$

因 $x$ 在 $R/(y) \cong k[x]$ 上不是零因子，故 $\operatorname{Tor}_1^R(R/(x), R/(y)) = 0$。

**例子 15.3.4** ($R/(x, y)$ 的 Tor)
设 $M = R/(x, y)$，$N = R/(x, y)$。取 Koszul 复形作为 $M$ 的自由消解：

$$
0 \longrightarrow R \xrightarrow{\begin{pmatrix} y \\ -x \end{pmatrix}} R^2 \xrightarrow{\begin{pmatrix} x & y \end{pmatrix}} R \longrightarrow R/(x, y) \longrightarrow 0
$$

作用 $- \otimes_R R/(x, y)$，所有映射变为零（因为在 $R/(x,y)$ 上 $x = y = 0$）。因此：

$$
\operatorname{Tor}_0^R(R/(x,y), R/(x,y)) \cong R/(x,y)
$$

$$
\operatorname{Tor}_1^R(R/(x,y), R/(x,y)) \cong (R/(x,y))^2 \cong k^2
$$

$$
\operatorname{Tor}_2^R(R/(x,y), R/(x,y)) \cong R/(x,y) \cong k
$$

这正是 Koszul 复形的 Betti 数。

---

## 15.3.5 Ext的具体计算 / Concrete Computations of Ext

### 主理想整环上的Ext / Ext over PID

**定理 15.3.7** (PID 上的 Ext)
设 $R$ 是 PID，$M, N$ 是有限生成 $R$-模。由结构定理，只需计算 $\operatorname{Ext}_R^n(R/(a), R)$ 和 $\operatorname{Ext}_R^n(R/(a), R/(b))$。

对 $R/(a)$，取投射消解 $0 \to R \xrightarrow{\times a} R \to R/(a) \to 0$。

**计算 $\operatorname{Ext}^1(R/(a), R)$**：
作用 $\operatorname{Hom}(-, R)$：

$$
0 \longrightarrow \operatorname{Hom}(R, R) \xrightarrow{\times a} \operatorname{Hom}(R, R) \longrightarrow 0
$$

即 $0 \to R \xrightarrow{\times a} R \to 0$。因此

$$
\operatorname{Ext}^1(R/(a), R) = R/(a)
$$

**计算 $\operatorname{Ext}^1(R/(a), R/(b))$**：
作用 $\operatorname{Hom}(-, R/(b))$：

$$
0 \longrightarrow R/(b) \xrightarrow{\times a} R/(b) \longrightarrow 0
$$

因此

$$
\operatorname{Ext}^1(R/(a), R/(b)) = R/\gcd(a, b)
$$

**例子 15.3.5**

$$
\operatorname{Ext}_\mathbb{Z}^1(\mathbb{Z}/4\mathbb{Z}, \mathbb{Z}/6\mathbb{Z}) = \mathbb{Z}/2\mathbb{Z}
$$

### Ext与群上同调的联系 / Connection with Group Cohomology

**定理 15.3.8**
设 $G$ 是群，$M$ 是 $\mathbb{Z}G$-模，则群上同调 $H^n(G, M)$ 同构于 $\operatorname{Ext}_{\mathbb{Z}G}^n(\mathbb{Z}, M)$，其中 $\mathbb{Z}$ 带有平凡的 $G$-作用。

**解释**：
这是因为 $H^0(G, M) = M^G = \operatorname{Hom}_{\mathbb{Z}G}(\mathbb{Z}, M)$。群上同调是固定点函子 $M \mapsto M^G$ 的右导出函子，因此 $H^n(G, M) = R^n(\operatorname{Hom}_{\mathbb{Z}G}(\mathbb{Z}, -))(M) = \operatorname{Ext}_{\mathbb{Z}G}^n(\mathbb{Z}, M)$。

**例子 15.3.6** ($G = \mathbb{Z}/2\mathbb{Z}$)
计算 $H^1(\mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/2\mathbb{Z})$，其中作用为平凡作用。

由上述定理，$H^1(G, \mathbb{Z}/2\mathbb{Z}) = \operatorname{Ext}_{\mathbb{Z}G}^1(\mathbb{Z}, \mathbb{Z}/2\mathbb{Z})$。

取 $\mathbb{Z}$ 的投射消解（标准 bar 消解的简化形式）：

$$
\cdots \longrightarrow \mathbb{Z}G \xrightarrow{N} \mathbb{Z}G \xrightarrow{T} \mathbb{Z}G \xrightarrow{N} \mathbb{Z}G \xrightarrow{\varepsilon} \mathbb{Z} \longrightarrow 0
$$

其中 $T = g - 1$，$N = 1 + g$（$g$ 是 $G$ 的生成元）。作用 $\operatorname{Hom}_{\mathbb{Z}G}(-, \mathbb{Z}/2\mathbb{Z})$ 后：

$$
0 \longrightarrow \mathbb{Z}/2\mathbb{Z} \xrightarrow{0} \mathbb{Z}/2\mathbb{Z} \xrightarrow{0} \mathbb{Z}/2\mathbb{Z} \xrightarrow{0} \cdots
$$

（因为 $G$ 作用是平凡的，$T$ 作用为零，$N$ 作用为 $2 = 0$）。因此

$$
\operatorname{Ext}_{\mathbb{Z}G}^n(\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}) = \mathbb{Z}/2\mathbb{Z}
$$

对所有 $n \geq 0$ 成立。特别地，$H^1(\mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}) = \mathbb{Z}/2\mathbb{Z}$。

---

## 15.3.6 应用：群扩张与挠模 / Applications: Group Extensions and Torsion Modules

**定理 15.3.9** ($\operatorname{Ext}^1$ 分类 Abel 群扩张)
设 $A, B$ 是 Abel 群（即 $\mathbb{Z}$-模）。则 Abel 群 $E$ 的短正合序列 $0 \to B \to E \to A \to 0$ 的等价类与 $\operatorname{Ext}_\mathbb{Z}^1(A, B)$ 一一对应。

**例子 15.3.7** ($\operatorname{Ext}_\mathbb{Z}^1(\mathbb{Z}/p\mathbb{Z}, \mathbb{Z}/p\mathbb{Z}) = \mathbb{Z}/p\mathbb{Z}$)
这对应 $p^2$ 阶 Abel 群的分类：对素数 $p$，$p^2$ 阶 Abel 群恰有两个：
1. $\mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/p\mathbb{Z}$（分裂扩张，对应 Ext 中的零元）
2. $\mathbb{Z}/p^2\mathbb{Z}$（非分裂扩张）

但 $\operatorname{Ext}_\mathbb{Z}^1(\mathbb{Z}/p\mathbb{Z}, \mathbb{Z}/p\mathbb{Z}) = \mathbb{Z}/p\mathbb{Z}$ 有 $p$ 个元素。这 $p$ 个元素分别对应怎样的扩张？

实际上，这里的 $p$ 个等价类对应的是短正合序列 $0 \to \mathbb{Z}/p\mathbb{Z} \to E \to \mathbb{Z}/p\mathbb{Z} \to 0$。由于 $E$ 作为 Abel 群，阶为 $p^2$ 的群只有两个（初等 Abel 群和循环群）。但这里的"扩张"是在 $\mathbb{Z}$-模意义下的，非分裂扩张都同构于 $\mathbb{Z}/p^2\mathbb{Z}$，但其嵌入方式有 $p-1$ 种不同的等价类（Aut 的作用）。

更准确地说，非零元给出 $E \cong \mathbb{Z}/p^2\mathbb{Z}$，但不同的非零元对应不同的嵌入 $B \hookrightarrow E$ 的等价类。这 $p-1$ 个非零元通过 $\operatorname{Aut}(B)$ 的作用形成单个轨道？实际上，$\operatorname{Aut}(\mathbb{Z}/p\mathbb{Z}) \cong (\mathbb{Z}/p\mathbb{Z})^\times$ 在 $\operatorname{Ext}^1$ 上的作用是乘法，将 $p-1$ 个非零元化为同一个等价类（若考虑群扩张的等价定义允许 $B$ 和 $A$ 的自同构）。在标准的模扩张等价定义中（只允许中间项的自同构），确实有 $p$ 个不同的等价类。

**定理 15.3.10** (挠模与 Tor)
设 $R$ 是交换诺特环，$M$ 是有限生成 $R$-模。则 $\operatorname{Tor}_1^R(M, K) = 0$（$K$ 为分式域）当且仅当 $M$ 是无挠模。

这在整环上给出了模的挠性的同调判据。

---

## 15.3.7 参考文献 / References

### 经典教材 / Classical Textbooks

1. **C. A. Weibel**, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced Mathematics 38, Cambridge University Press, 1994.
   - 第3章：Tor与Ext（第3.1-3.4节）
   - 第6章：群上同调中的 Ext 解释

2. **S. Mac Lane**, *Homology*, Classics in Mathematics, Springer, 1995.
   - 第III章 §§2-3：Tor 的对称性
   - 第III章 §§4-5：Ext 与模扩张

3. **D. Eisenbud**, *Commutative Algebra with a View Toward Algebraic Geometry*, Graduate Texts in Mathematics 150, Springer, 1995.
   - 附录A3：同调代数工具箱，包含 Tor 与 Ext 的计算实例

### 课程讲义 / Lecture Notes

4. **Oxford Mathematics**, *C2.2 Homological Algebra*, Michaelmas Term 2024/25.
   - Lecture 8-9: Tor 的计算与平坦性判据
   - Lecture 10-11: Ext 的 Baer 和与模扩张
   - Lecture 12: 具体计算实例（PID、多项式环）

### 在线资源 / Online Resources

5. **Stacks Project**, Tag 00LY — Tor groups, Chapter 15.
   - `https://stacks.math.columbia.edu/tag/00LY`

6. **Stacks Project**, Tag 00O0 — Ext groups, Chapter 15.
   - `https://stacks.math.columbia.edu/tag/00O0`

### 中文参考 / Chinese References

7. **李克正**，《同调代数基础》，科学出版社，1996.
   - 第4章：Tor 与 Ext

8. **陈志杰**，《同调代数》，北京大学出版社，2006.
   - 第5-6章：具体计算与应用

---

## 补充内容：局部环与Koszul复形上的计算 / Supplement: Local Rings and Koszul Complexes

### 正则局部环上的投射维数 / Projective Dimension over Regular Local Rings

**定理 15.3.11** (Hilbert 合冲定理)
设 $R = k[x_1, \ldots, x_n]$ 是域 $k$ 上的多项式环，$M$ 是有限生成分次 $R$-模。则 $M$ 有长度不超过 $n$ 的有限自由消解。等价地，$\operatorname{pd}_R(M) \leq n$。

**推论 15.3.2**
对任意两个有限生成 $R$-模 $M, N$，$\operatorname{Tor}_i^R(M, N) = 0$ 对 $i > n$。因此多项式环的整体维数为 $n$。

### Koszul复形作为Tor计算工具 / Koszul Complexes as Computational Tools

**定义 15.3.4** (Koszul 复形)
设 $R$ 是交换环，$\mathbf{x} = (x_1, \ldots, x_n) \in R^n$。Koszul 复形 $K_\bullet(\mathbf{x}; R)$ 定义为外代数 $\Lambda^*(R^n)$ 配以微分

$$
d(e_{i_1} \wedge \cdots \wedge e_{i_p}) = \sum_{k=1}^p (-1)^{k-1} x_{i_k} e_{i_1} \wedge \cdots \wedge \widehat{e}_{i_k} \wedge \cdots \wedge e_{i_p}
$$

**定理 15.3.12**
若 $x_1, \ldots, x_n$ 构成 $R$-正则序列，则 $K_\bullet(\mathbf{x}; R)$ 是 $R/(x_1, \ldots, x_n)$ 的自由消解。因此

$$
\operatorname{Tor}_p^R(R/(\mathbf{x}), M) = H_p(K_\bullet(\mathbf{x}) \otimes_R M)
$$

**例子 15.3.8** (完全交的 Tor)
设 $R = k[x, y, z]$，$I = (x, y)$，$M = R/(z)$。因 $x, y$ 是 $R$-正则序列，也是 $M$-正则序列（因为 $z$ 与 $x, y$ 无关），Koszul 复形给出：

$$
K_\bullet = [0 \to R \xrightarrow{(y, -x)} R^2 \xrightarrow{(x, y)} R \to 0]
$$

作用 $-\otimes_R M$：

$$
0 \to M \to M^2 \to M \to 0
$$

因 $x, y$ 在 $M = k[x,y,z]/(z)$ 上仍是正则的，故 $H_1 = H_2 = 0$，$H_0 = M/(x,y) \cong k$。这说明 $R/I$ 是 $M$-平坦的。

**例子 15.3.9** (非完全交的 Tor)
设 $R = k[x,y]/(x^2, xy)$，$M = R/(y) \cong k[x]/(x^2)$。计算 $\operatorname{Tor}_1^R(M, M)$。

取 $M$ 的投射消解：

$$
\cdots \to R \xrightarrow{\cdot y} R \xrightarrow{\cdot x} R \xrightarrow{\cdot y} R \to M \to 0
$$

作用 $-\otimes_R M$ 后 $y$ 变为零，因此复形变为

$$
\cdots \to M \xrightarrow{0} M \xrightarrow{\cdot x} M \xrightarrow{0} M \to 0
$$

因 $x$ 在 $M = k[x]/(x^2)$ 上的核和余核都是 $k$，可得

$$
\operatorname{Tor}_{2n+1}^R(M, M) = k, \quad \operatorname{Tor}_{2n+2}^R(M, M) = k \quad (n \geq 0)
$$

这说明非正则局部环可以具有无限的整体维数，Tor 不消失。

### Ext与深度 / Ext and Depth

**定义 15.3.5** (深度 / Depth)
设 $R$ 是诺特局部环，$\mathfrak{m}$ 是极大理想，$M$ 是有限生成 $R$-模。$M$ 的**深度**定义为

$$
\operatorname{depth}_R(M) = \min\{n : \operatorname{Ext}_R^n(R/\mathfrak{m}, M) \neq 0\}
$$

**定理 15.3.13** (Auslander-Buchsbaum 公式)
设 $R$ 是正则局部环，$M$ 是有限生成 $R$-模。若 $\operatorname{pd}_R(M) < \infty$，则

$$
\operatorname{pd}_R(M) + \operatorname{depth}(M) = \operatorname{depth}(R) = \dim(R)
$$

**例子 15.3.10**
设 $R = k[[x, y]]$，$M = R/(x)$。则 $\operatorname{pd}(M) = 1$（由 Koszul 复形 $0 \to R \xrightarrow{x} R \to M \to 0$），$\operatorname{depth}(M) = 1$（因为 $y$ 在 $M$ 上是正则的），而 $\dim(R) = 2$。Auslander-Buchsbaum 公式验证：$1 + 1 = 2$。

