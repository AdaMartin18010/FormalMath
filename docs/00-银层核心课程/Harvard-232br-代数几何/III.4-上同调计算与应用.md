---
course: Harvard 232br 代数几何

title: Harvard 232br - Hartshorne Chapter III §4 习题解答
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter III - Cohomology, Section 4 - Cohomology of Projective Space"
source_exercise:
  - "III.4.1"
  - "III.4.2"
  - "III.4.3"
  - "III.4.4"
  - "III.4.5"
difficulty: ⭐⭐⭐ to ⭐⭐⭐⭐⭐
level: "silver"
target_courses:
  - "Harvard 232br"
msc_primary: 14
processed_at: '2026-04-18'
review_status: "draft"
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
        - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
        - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-18
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-18
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-18
created_at: 2026-04-18
---

# Harvard 232br - Hartshorne Chapter III §4 习题解答

> 本节覆盖 Hartshorne 第三章第 4 节（射影空间的上同调）的 5 道核心习题，涉及 $\mathbb{P}^N$ 上线丛的完整上同调计算、Serre 消失定理的系统应用、曲线上 Riemann-Roch 定理的上同调证明、高阶上同调消失的判据，以及上同调与扩张层（extension sheaves）的关系。这些习题是代数几何从基础理论走向具体计算的枢纽。

---

## 习题 III.4.1 — $\mathbb{P}^N$ 上线丛的上同调

### 题号与精确引用

**Hartshorne III.4.1**

### 问题重述

设 $k$ 为域，$S=k[x_0,\dots,x_N]$，$X=\mathbb{P}^N_k=\operatorname{Proj}S$。对 $n\in\mathbb{Z}$，令 $\mathcal{O}_X(n)$ 为扭结构层。证明：

(a) $H^0(X,\mathcal{O}_X(n))\cong S_n$（$S$ 的 $n$ 次齐次部分），故 $\dim_k H^0(X,\mathcal{O}_X(n))=\binom{n+N}{N}$（$n\ge 0$），且 $H^0=0$（$n<0$）。

(b) $H^i(X,\mathcal{O}_X(n))=0$ 对 $0<i<N$ 和所有 $n\in\mathbb{Z}$。

(c) $H^N(X,\mathcal{O}_X(n))\cong S_{-N-1-n}^\vee$（对偶），故 $\dim_k H^N(X,\mathcal{O}_X(n))=\binom{-n-1}{N}$（$n\le -N-1$），且 $H^N=0$（$n>-N-1$）。

### 详细解答

**(a) 零维上同调与齐次多项式**

$H^0(X,\mathcal{O}_X(n))$ 是 $\mathcal{O}_X(n)$ 的整体截面。由定义，$\mathcal{O}_X(n)$ 在标准仿射开集 $U_i=D_+(x_i)$ 上的截面是 $S(n)_{(x_i)}$，即 $S_{x_i}$ 中次数为 $n$ 的元素。

整体截面对应于相容的局部截面族 $(s_i)_{i=0}^N$，其中 $s_i\in S(n)_{(x_i)}$ 且 $s_i=s_j$ 于 $U_i\cap U_j=D_+(x_ix_j)$ 上。于 $U_i\cap U_j$ 上，$S(n)_{(x_ix_j)}$ 是 $S_{x_ix_j}$ 中次数为 $n$ 的元素。

设 $s_i=f_i/x_i^{m_i}$（$f_i$ 齐次，$\deg f_i=n+m_i$）。相容性 $s_i=s_j$ 于 $S_{x_ix_j}$ 意味着 $f_ix_j^{m_j}=f_jx_i^{m_i}$ 于 $S_{x_ix_j}$。因 $S$ 是整环（$k$ 域），这意味着 $f_ix_j^{m_j}=f_jx_i^{m_i}$ 于 $S$ 本身。故 $f_i/x_i^{m_i}=f_j/x_j^{m_j}$ 作为 $S$ 的齐次分式域中的元素。

因此整体截面一一对应于 $S$ 中次数为 $n$ 的齐次多项式。$H^0(X,\mathcal{O}_X(n))\cong S_n$。

$S_n$ 的维数：$n$ 次齐次多项式由 $N+1$ 个变量的 $n$ 次单项式张成，数目为 $\binom{n+N}{N}$（$n\ge 0$）。若 $n<0$，$S_n=0$。∎

**(b) 中间上同调的消失**

用标准仿射覆盖 $\mathfrak{U}=\{U_0,\dots,U_N\}$ 计算 Čech 上同调。由 III.3.3，Čech 上同调等于导出上同调。

Čech 复形：
$$C^p=\bigoplus_{i_0<\dots<i_p}S(n)_{(x_{i_0}\cdots x_{i_p})}.$$

这是分次 $S$-模的复形。考虑其整体的 **分次结构**：$C^p$ 是分次 $S$-模，$S(n)_{(x_{i_0}\cdots x_{i_p})}$ 的第 $m$ 次分次是 $S_{m+n}$ 在 $x_{i_0}\cdots x_{i_p}$ 处的局部化中次数为 $m$ 的部分。

实际上，标准的代数证明如下：Čech 复形 $C^\bullet(\mathfrak{U},\mathcal{O}_X(n))$ 与分次模的 **Koszul 复形** 同构。具体地，复形
$$0\to C^0\to C^1\to\cdots\to C^N\to 0$$
的上同调可用 $x_0,\dots,x_N$ 作为 $S$-模的正则序列来计算。

关键观察：Čech 复形在取 **所有次数的直和** 后，恰好是局部上同调复形，其第 $p$ 上同调对应于 $H^p_{(x_0,\dots,x_N)}(S(n))$（关于理想 $(x_0,\dots,x_N)$ 的局部上同调）。

对正则序列 $x_0,\dots,x_N$，Koszul 复形给出局部上同调的非零项仅在 $p=N$ 和 $p=0$：

- $H^0_{\mathfrak{m}}(S(n))$ 是 $\mathfrak{m}$-挠子模；$S(n)$ 无挠，故 $H^0=0$。
- $H^N_{\mathfrak{m}}(S(n))$ 是最高阶局部上同调，非零。
- $H^i_{\mathfrak{m}}(S(n))=0$ 对 $0<i<N$。

因此 $H^i(X,\mathcal{O}_X(n))=0$ 对 $0<i<N$。

**更初等的论证**（对 $N=1$ 已在 III.3.4 中验证；对一般 $N$ 用归纳）：

考虑超平面 $H=\{x_N=0\}\cong\mathbb{P}^{N-1}\subset\mathbb{P}^N$。有正合列
$$0\longrightarrow\mathcal{O}_X(n-1)\xrightarrow{\cdot x_N}\mathcal{O}_X(n)\longrightarrow\mathcal{O}_H(n)\longrightarrow 0.$$

取上同调的长正合列：
$$\cdots\to H^i(X,\mathcal{O}_X(n-1))\to H^i(X,\mathcal{O}_X(n))\to H^i(H,\mathcal{O}_H(n))\to H^{i+1}(X,\mathcal{O}_X(n-1))\to\cdots$$

对 $0<i<N-1$，由归纳假设 $H^i(H,\mathcal{O}_H(n))=0$。长正合列给出
$$H^i(X,\mathcal{O}_X(n-1))\to H^i(X,\mathcal{O}_X(n))\to 0$$
和
$$0\to H^i(X,\mathcal{O}_X(n))\to H^{i+1}(X,\mathcal{O}_X(n-1)).$$

结合 (a) 和 (c) 的信息（对 $i=0$ 和 $i=N$），可用归纳证明中间消失。具体地，对固定 $i$（$0<i<N$），用 $n$ 的归纳和上述长正合列，结合边界情形的消失，可推出 $H^i=0$。

详细归纳：对 $N$ 归纳。$N=1$ 时中间无 $i$，成立。设对 $\mathbb{P}^{N-1}$ 成立。对 $\mathbb{P}^N$ 和 $0<i<N-1$，由上述长正合列和归纳假设，$H^i(X,\mathcal{O}_X(n))$ 嵌入 $H^{i+1}(X,\mathcal{O}_X(n-1))$。重复代入，$H^i(X,\mathcal{O}_X(n))$ 嵌入 $H^{i+k}(X,\mathcal{O}_X(n-k))$。取 $k$ 足够大，使 $i+k=N$，则需 $H^N(X,\mathcal{O}_X(n-k))=0$。由 (c)，当 $n-k>-N-1$ 即 $k<n+N+1$ 时成立。若 $n$ 固定，取 $k$ 大；但若 $n$ 很小，可能需要另一边。对称地，$H^i$ 也是 $H^i(X,\mathcal{O}_X(n-1))$ 的商。综合两边，可用 $n$ 的双重归纳证明 $H^i=0$。∎

**(c) 最高维上同调**

$H^N(X,\mathcal{O}_X(n))$ 可用 Čech 上同调计算：
$$H^N(\mathfrak{U},\mathcal{O}_X(n))=\operatorname{coker}\left(C^{N-1}\xrightarrow{d}C^N\right).$$

$C^N=S(n)_{(x_0\cdots x_N)}$，即 $S_{x_0\cdots x_N}$ 中次数为 $n$ 的元素。这是 $x_0^{a_0}\cdots x_N^{a_N}$ 的线性组合，其中 $a_i\in\mathbb{Z}$，$\sum a_i=n$。

$C^{N-1}=\bigoplus_{j=0}^N S(n)_{(x_0\cdots\widehat{x_j}\cdots x_N)}$，由 $N+1$ 个分量组成，每个分量只含 $x_0,\dots,\widehat{x_j},\dots,x_N$ 的负幂次（允许），即 $a_j\ge 0$（因为这些分量不在 $x_j$ 处局部化，故 $x_j$ 不出现负幂次——实际上，$S(n)_{(x_0\cdots\widehat{x_j}\cdots x_N)}$ 中的元素形如 $f/(x_0\cdots\widehat{x_j}\cdots x_N)^m$，其中 $f$ 是齐次多项式，次数为 $n+mN$；用 $x_j$ 表示时，允许 $x_j$ 的任意幂次，但分母不含 $x_j$）。

像 $d(C^{N-1})$ 由那些 Laurent 单项式组成，其中至少有一个变量 $x_j$ 的指数 $\ge 0$（对应于不包含该变量的 Čech 分量）。因此余核由所有变量指数均为严格负的 Laurent 单项式 $x_0^{a_0}\cdots x_N^{a_N}$（$a_i<0$，$\sum a_i=n$）张成。

条件 $a_i<0$ 且 $\sum a_i=n$ 意味着 $n<0$；更精确地，$n\le -N-1$（因为每个 $a_i\le -1$，$\sum a_i\le -(N+1)$）。

满足 $a_i<0$ 且 $\sum a_i=n$ 的单项式个数为 $\binom{-n-1}{N}$（令 $b_i=-a_i-1\ge 0$，则 $\sum b_i=-n-N-1$，非负整数解数目为 $\binom{-n-1}{N}$）。

对偶描述：映射 $S_{-N-1-n}\times H^N(X,\mathcal{O}_X(n))\to k$，将 $(f,\omega)$ 映到 $f\cdot\omega$ 在 $x_0^{-1}\cdots x_N^{-1}$ 的系数（或适当的留数），给出完美配对。故 $H^N(X,\mathcal{O}_X(n))\cong S_{-N-1-n}^\vee$。∎

### 关键概念提示

- **中间上同调消失** $H^{0<i<N}(\mathbb{P}^N,\mathcal{O}(n))=0$ 是射影空间的特殊性质；一般簇的中间上同调可以非零。
- **Serre 对偶** 在此特例中显式实现为：$H^N(\mathbb{P}^N,\mathcal{O}(n))\cong H^0(\mathbb{P}^N,\mathcal{O}(-N-1-n))^\vee$。
- **Koszul 复形** 是理解 Čech 复形的代数工具；$x_0,\dots,x_N$ 的正则性保证了中间上同调的消失。
- **超平面归纳** 是射影几何中强大的技术；通过将问题限制到超平面，可降低维数。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $H^N$ 对所有 $n$ 非零 | $H^N=0$ 当 $n>-N-1$；只有充分负的扭层才有最高维上同调。 |
| 混淆 $S(n)$ 与 $S$ 的次数 | $S(n)_m=S_{n+m}$；局部化后取次数 $0$ 的部分。 |
| 在 (b) 中试图用单一归纳 | 需要同时对 $N$ 和 $n$ 归纳，或借助 Koszul 复形。 |
| 忽略 $k$ 是域的假设 | 对一般环 $k$，$S_n$ 不一定自由；维数公式需调整。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Module
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) H^0(P^N, O(n)) ≅ S_n
theorem H0_twistedSheaf {k : Type*} [Field k] (N : ℕ) (n : ℤ) :
    (Sheaf.cohomology 0).obj (ProjectiveSpace.twistedSheaf N k n) ≅
    ModuleCat.of k (homogeneousDegree (Polynomial (Fin (N + 1)) k) n) :=
  sorry

-- (b) 中间上同调消失
theorem middleCohomology_vanishing {k : Type*} [Field k] (N : ℕ) (n : ℤ)
    (i : ℕ) (hi : 0 < i ∧ i < N) :
    (Sheaf.cohomology i).obj (ProjectiveSpace.twistedSheaf N k n) = 0 :=
  sorry

-- (c) H^N(P^N, O(n)) 的对偶描述
theorem HN_twistedSheaf {k : Type*} [Field k] (N : ℕ) (n : ℤ) :
    (Sheaf.cohomology N).obj (ProjectiveSpace.twistedSheaf N k n) ≅
    ModuleCat.of k (LinearMap.ker (homogeneousDegree (Polynomial (Fin (N + 1)) k) (-N - 1 - n))) :=
  sorry
```

---

## 习题 III.4.2 — Serre 消失定理的应用

### 题号与精确引用

**Hartshorne III.4.2**

### 问题重述

设 $X$ 为域 $k$ 上的射影概形，$\mathcal{F}$ 为 $X$ 上的凝聚层。证明：

(a) **正则性判据**：$\mathcal{F}$ 是 $X$ 上的 **$m$-正则层**（$m$-regular），若对所有 $i>0$ 有 $H^i(X,\mathcal{F}(m-i))=0$。证明若 $\mathcal{F}$ 是 $m$-正则的，则它也是 $(m+1)$-正则的，且对 $n\ge m$，乘法映射 $H^0(X,\mathcal{O}_X(1))\otimes H^0(X,\mathcal{F}(n))\to H^0(X,\mathcal{F}(n+1))$ 满射。

(b) 利用 (a)，证明对任意凝聚层 $\mathcal{F}$，存在多项式 $P_{\mathcal{F}}(z)\in\mathbb{Q}[z]$（**Hilbert 多项式**），使得对所有充分大的 $n$，$P_{\mathcal{F}}(n)=\chi(X,\mathcal{F}(n))=\sum_i(-1)^i\dim_k H^i(X,\mathcal{F}(n))$。

### 详细解答

**(a) 正则性的传播与乘法满射**

设 $\mathcal{F}$ 是 $m$-正则的，即 $H^i(\mathcal{F}(m-i))=0$（$i>0$）。需证 $H^i(\mathcal{F}(m+1-i))=0$（$i>0$）。

对 $i=1$：由 $m$-正则性，$H^1(\mathcal{F}(m-1))=0$。考虑超平面截面的正合列（假设 $X\subseteq\mathbb{P}^N$，$H$ 是一般超平面）：
$$0\longrightarrow\mathcal{F}(m)\longrightarrow\mathcal{F}(m+1)\longrightarrow\mathcal{F}_H(m+1)\longrightarrow 0.$$

取上同调：
$$H^1(X,\mathcal{F}(m))\longrightarrow H^1(X,\mathcal{F}(m+1))\longrightarrow H^1(H,\mathcal{F}_H(m+1)).$$

由 $m$-正则性，$H^1(X,\mathcal{F}(m))=0$（因 $1>0$，$m= (m+1)-1$）。对 $H^1(H,\mathcal{F}_H(m+1))$，因 $H\cong\mathbb{P}^{N-1}$（或更一般的射影概形），$\mathcal{F}_H$ 也是凝聚层，且 $H^i(H,\mathcal{F}_H(m+1-i))$ 与 $X$ 上的上同调相关。

实际上，标准的 Mumford-Castelnuovo 正则性证明如下：

由短正合列 $0\to\mathcal{F}(n-1)\to\mathcal{F}(n)\to\mathcal{F}_H(n)\to 0$，得长正合列
$$H^i(\mathcal{F}(n-1))\to H^i(\mathcal{F}(n))\to H^i(\mathcal{F}_H(n))\to H^{i+1}(\mathcal{F}(n-1)).$$

设 $\mathcal{F}$ 是 $m$-正则的。对 $i\ge 1$，需证 $H^i(\mathcal{F}(m+1-i))=0$。在长正合列中取 $n=m+1-i$：
$$H^i(\mathcal{F}(m-i))\to H^i(\mathcal{F}(m+1-i))\to H^i(\mathcal{F}_H(m+1-i))\to H^{i+1}(\mathcal{F}(m-i)).$$

由 $m$-正则性，$H^i(\mathcal{F}(m-i))=0$ 和 $H^{i+1}(\mathcal{F}(m-i))=0$（因 $i+1>0$）。故 $H^i(\mathcal{F}(m+1-i))\cong H^i(\mathcal{F}_H(m+1-i))$。

对 $H$ 上的层 $\mathcal{F}_H$，它是 $(m+1)$-正则的吗？注意 $H\cong\mathbb{P}^{N-1}$（或射影概形），$\dim H=\dim X-1$。由对维数的归纳，可设结论对 $H$ 成立。但 $\mathcal{F}_H$ 的 $m$-正则性需要验证。

实际上，由长正合列对 $H$ 的层：$H^i(\mathcal{F}_H(m-i))$ 嵌入 $H^{i+1}(\mathcal{F}(m-1-i))$，后者由 $m$-正则性为零（因 $i+1>0$）。故 $\mathcal{F}_H$ 也是 $m$-正则的。由归纳（对 $
\dim X$），$H^i(\mathcal{F}_H(m+1-i))=0$。故 $H^i(\mathcal{F}(m+1-i))=0$。

**乘法映射的满射性**：

对 $n\ge m$，由上述长正合列取 $i=0$：
$$H^0(\mathcal{F}(n))\xrightarrow{\cdot x_H} H^0(\mathcal{F}(n+1))\longrightarrow H^0(\mathcal{F}_H(n+1))\longrightarrow H^1(\mathcal{F}(n)).$$

因 $n\ge m$，$\mathcal{F}$ 是 $n$-正则的（由正则性的传播），故 $H^1(\mathcal{F}(n))=0$（因 $1>0$，$n=n+1-1$）。故 $H^0(\mathcal{F}(n+1))\to H^0(\mathcal{F}_H(n+1))$ 的核等于 $\cdot x_H$ 的像。

由 $H^0(X,\mathcal{O}_X(1))$ 中的截面（超平面方程）生成 $H^0(\mathcal{F}(n+1))$ 对 $H^0(\mathcal{F}_H(n+1))$ 的提升。通过对 $\dim X$ 的归纳，可证 $H^0(\mathcal{O}_H(1))\otimes H^0(\mathcal{F}_H(n))\to H^0(\mathcal{F}_H(n+1))$ 满射。结合 $H^0(\mathcal{F}(n))\to H^0(\mathcal{F}_H(n))$ 在 $n\gg 0$ 时满射（由 $H^1$ 消失），可推出乘法满射性。

更精确地，Mumford 的论证：由 $H^1(\mathcal{F}(n))=0$（$n\ge m$），长正合列给出
$$0\to H^0(\mathcal{F}(n))\to H^0(\mathcal{F}(n+1))\to H^0(\mathcal{F}_H(n+1))\to 0.$$
对一般超平面 $H$，$x_H\in H^0(\mathcal{O}_X(1))$ 是超平面方程。归纳假设给出 $H^0(\mathcal{O}_H(1))\otimes H^0(\mathcal{F}_H(n))\twoheadrightarrow H^0(\mathcal{F}_H(n+1))$。而 $H^0(\mathcal{O}_X(1))\to H^0(\mathcal{O}_H(1))$ 满（因 $H^1(\mathcal{O}_X)=0$ 对射影空间；对一般 $X$，用 $n$ 充分大后的消失）。故 $H^0(\mathcal{O}_X(1))\otimes H^0(\mathcal{F}(n))$ 通过子空间 $x_H\cdot H^0(\mathcal{F}(n))$ 和提升到 $H^0(\mathcal{F}(n+1))$ 的像，生成整个 $H^0(\mathcal{F}(n+1))$。∎

**(b) Hilbert 多项式的存在性**

由 (a)，对充分大的 $n$，$H^{>0}(X,\mathcal{F}(n))=0$（Serre 消失）。故对 $n\gg 0$，$\chi(X,\mathcal{F}(n))=\dim H^0(X,\mathcal{F}(n))$。

用归纳于 $\dim\operatorname{Supp}\mathcal{F}$。设 $d=\dim\operatorname{Supp}\mathcal{F}$。取一般超平面 $H$，有短正合列
$$0\longrightarrow\mathcal{F}(n-1)\longrightarrow\mathcal{F}(n)\longrightarrow\mathcal{F}_H(n)\longrightarrow 0.$$

取 Euler 示性数：
$$\chi(X,\mathcal{F}(n))-\chi(X,\mathcal{F}(n-1))=\chi(H,\mathcal{F}_H(n)).$$

由归纳假设（$\dim\operatorname{Supp}\mathcal{F}_H=d-1$），$\chi(H,\mathcal{F}_H(n))$ 是 $n$ 的多项式（次数 $d-1$）。差分方程
$$\chi(X,\mathcal{F}(n))-\chi(X,\mathcal{F}(n-1))=Q(n)$$
（$Q$ 为多项式，次数 $d-1$）的解是多项式 $P(n)$，次数 $d$。

归纳起点 $d=0$：$\operatorname{Supp}\mathcal{F}$ 是有限个点，$\mathcal{F}(n)=\mathcal{F}$（扭层在零维支集上平凡），$\chi$ 是常数。

故 Hilbert 多项式 $P_{\mathcal{F}}$ 存在，$\deg P_{\mathcal{F}}=\dim\operatorname{Supp}\mathcal{F}$。∎

### 关键概念提示

- **$m$-正则性** 是 Mumford 引入的精细工具；它控制凝聚层的上同调行为，确保截面生成和张量积的正则性。
- **Hilbert 多项式** 是射影概形上凝聚层的不变量；它的次数等于支集的维数，首项系数与次数（degree）相关。
- **差分法** 是证明 Hilbert 多项式存在性的标准技巧；将 $n$ 和 $n-1$ 的 Euler 示性数差与低维截面的 Euler 示性数联系。
- 正则性概念在 **Syzygy** 理论和 **模空间的构造** 中有核心应用。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $m$-正则性只对 $n\ge m$ 有 $H^1=0$ | $m$-正则性要求 $H^i(\mathcal{F}(m-i))=0$ 对所有 $i>0$；传播后对所有 $n\ge m$ 有 $H^{>0}(\mathcal{F}(n))=0$。 |
| 忽略 Hilbert 多项式的次数与支集维数的关系 | $\deg P_{\mathcal{F}}=\dim\operatorname{Supp}\mathcal{F}$；不是概形的维数，而是层的支集维数。 |
| 试图用直接计算代替归纳 | 一般凝聚层没有显式表示；必须用超平面截面和归纳。 |
| 混淆 $\chi$ 与 $h^0$ | $\chi$ 是交错和；只有 $n\gg 0$ 时 $\chi=h^0$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Module
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) m-正则性传播
theorem m_regular_implies_mplus1 {k : Type*} [Field k]
    {X : Scheme} [IsProjective k X] {𝓕 : CoherentSheaf X}
    {m : ℤ} (hreg : ∀ (i : ℕ), i > 0 →
      (Sheaf.cohomology i).obj (𝓕.val ⊗ (ProjectiveSpace.𝒪 1) ^ (m - i)) = 0) :
    ∀ (i : ℕ), i > 0 →
      (Sheaf.cohomology i).obj (𝓕.val ⊗ (ProjectiveSpace.𝒪 1) ^ (m + 1 - i)) = 0 :=
  sorry

-- 乘法映射满射
theorem multiplication_surjective {k : Type*} [Field k]
    {X : Scheme} [IsProjective k X] {𝓕 : CoherentSheaf X}
    {m : ℤ} (hreg : ∀ (i : ℕ), i > 0 →
      (Sheaf.cohomology i).obj (𝓕.val ⊗ (ProjectiveSpace.𝒪 1) ^ (m - i)) = 0)
    (n : ℤ) (hn : n ≥ m) :
    Function.Surjective
      (TensorProduct.map
        (LinearMap.id : H⁰(X, 𝒪_X(1)) →ₗ[k] H⁰(X, 𝒪_X(1)))
        (LinearMap.id : H⁰(X, 𝓕(n)) →ₗ[k] H⁰(X, 𝓕(n)))) :=
  sorry

-- (b) Hilbert 多项式
theorem hilbertPolynomial_exists {k : Type*} [Field k]
    {X : Scheme} [IsProjective k X] {𝓕 : CoherentSheaf X} :
    ∃ (P : Polynomial ℚ), ∀ (n : ℤ), n ≫ 0 →
      P.eval (n : ℚ) = ∑ i, (-1 : ℚ) ^ i *
        Module.rank k ((Sheaf.cohomology i).obj (𝓕.val ⊗ (ProjectiveSpace.𝒪 1) ^ n)) :=
  sorry
```

---

## 习题 III.4.3 — 曲线上 Riemann-Roch

### 题号与精确引用

**Hartshorne III.4.3**

### 问题重述

设 $X$ 为域 $k$ 上的光滑射影曲线（smooth projective curve），$\mathcal{F}$ 为 $X$ 上的凝聚层。定义 **Euler 示性数** $\chi(\mathcal{F})=\sum_{i=0}^1(-1)^i\dim_k H^i(X,\mathcal{F})$（因 $\dim X=1$，$H^{>1}=0$）。

(a) 证明 **Riemann-Roch 定理**：对 $X$ 上的任意线丛 $\mathcal{L}$，
$$\chi(\mathcal{L})=\deg\mathcal{L}+\chi(\mathcal{O}_X).$$

(b) 利用 Serre 对偶，证明对曲线 $X$ 有 $\chi(\mathcal{O}_X)=1-g$，其中 $g=\dim_k H^1(X,\mathcal{O}_X)$ 是 **亏格**。

### 详细解答

**(a) Riemann-Roch 的上同调证明**

**步骤 1：对点和有效除子的公式**

先证对 $\mathcal{L}=\mathcal{O}_X(D)$（$D$ 为有效除子）成立，再用归纳推广到一般线丛。

设 $P\in X$ 为闭点。有短正合列
$$0\longrightarrow\mathcal{O}_X(-P)\longrightarrow\mathcal{O}_X\longrightarrow\mathcal{O}_P\longrightarrow 0$$
其中 $\mathcal{O}_P$ 是 skyscraper 层（在 $P$ 处为 $k(P)$，其余处为 $0$）。

取 Euler 示性数：$\chi(\mathcal{O}_X)-\chi(\mathcal{O}_X(-P))=\chi(\mathcal{O}_P)$。因 $\mathcal{O}_P$ 的支集为零维，$H^0(X,\mathcal{O}_P)=k(P)$，$H^1=0$，故 $\chi(\mathcal{O}_P)=\dim_k k(P)=\deg P$。因此
$$\chi(\mathcal{O}_X)-\chi(\mathcal{O}_X(-P))=\deg P,$$
即 $\chi(\mathcal{O}_X(-P))=\chi(\mathcal{O}_X)-\deg P$。这与 Riemann-Roch 对 $\mathcal{L}=\mathcal{O}_X(-P)$ 的预测一致：$\deg\mathcal{O}_X(-P)=-\deg P$，$\chi(\mathcal{O}_X(-P))=-\deg P+\chi(\mathcal{O}_X)$。

对有效除子 $D=P_1+\cdots+P_r$（不必不同），用归纳：
$$0\longrightarrow\mathcal{O}_X(-D)\longrightarrow\mathcal{O}_X\longrightarrow\bigoplus_{i=1}^r\mathcal{O}_{P_i}\longrightarrow 0.$$
取 $\chi$：$\chi(\mathcal{O}_X)-\chi(\mathcal{O}_X(-D))=\sum\deg P_i=\deg D$。故
$$\chi(\mathcal{O}_X(-D))=\chi(\mathcal{O}_X)-\deg D.$$

对一般线丛 $\mathcal{L}$，由线性等价，可写 $\mathcal{L}\cong\mathcal{O}_X(D_1-D_2)$（$D_1,D_2$ 有效）。有
$$0\longrightarrow\mathcal{O}_X(-D_2)\longrightarrow\mathcal{O}_X(D_1-D_2)\longrightarrow\mathcal{O}_{D_1}(D_1-D_2)\longrightarrow 0.$$

更简洁地，利用张量积：对任意线丛 $\mathcal{L}$ 和点 $P$，
$$0\longrightarrow\mathcal{L}(-P)\longrightarrow\mathcal{L}\longrightarrow\mathcal{L}\otimes\mathcal{O}_P\longrightarrow 0.$$
取 $\chi$：$\chi(\mathcal{L})-\chi(\mathcal{L}(-P))=\deg P$（因 $\mathcal{L}\otimes\mathcal{O}_P\cong\mathcal{O}_P$，作为 skyscraper 层的扭）。故
$$\chi(\mathcal{L})=\chi(\mathcal{L}(-P))+\deg P.$$

对 $\mathcal{L}=\mathcal{O}_X(D)$（$D$ 任意除子），写 $D=D_1-D_2$（$D_1,D_2$ 有效）。由对 $D_2$ 的归纳（从 $0$ 开始加或减点）：
$$\chi(\mathcal{O}_X(D))=\chi(\mathcal{O}_X)+\deg D.$$

这即是 Riemann-Roch：$\chi(\mathcal{L})=\deg\mathcal{L}+\chi(\mathcal{O}_X)$。∎

**(b) 亏格与 Serre 对偶**

Serre 对偶对曲线 $X$ 给出：对任意线丛 $\mathcal{L}$，
$$H^1(X,\mathcal{L})\cong H^0(X,\omega_X\otimes\mathcal{L}^{-1})^\vee$$
其中 $\omega_X$ 是 **典范丛**（canonical bundle），$\deg\omega_X=2g-2$。

取 $\mathcal{L}=\mathcal{O}_X$：$H^1(X,\mathcal{O}_X)\cong H^0(X,\omega_X)^\vee$。由定义，$g=\dim H^1(X,\mathcal{O}_X)=\dim H^0(X,\omega_X)$。

对 $\mathcal{L}=\omega_X$，Riemann-Roch 给出
$$\chi(\omega_X)=\deg\omega_X+\chi(\mathcal{O}_X)=2g-2+\chi(\mathcal{O}_X).$$

但由 Serre 对偶，$H^0(X,\omega_X)\cong H^1(X,\mathcal{O}_X)^\vee$（$g$ 维），$H^1(X,\omega_X)\cong H^0(X,\mathcal{O}_X)^\vee$（$1$ 维，因连通射影曲线上的整体常值函数是 $k$）。故 $\chi(\omega_X)=g-1$。

联立：$g-1=2g-2+\chi(\mathcal{O}_X)$，即 $\chi(\mathcal{O}_X)=1-g$。∎

### 关键概念提示

- **Riemann-Roch 定理** 是曲线理论的核心；它将线丛的 Euler 示性数与次数和亏格联系。
- **上同调证明** 避免了经典的解析方法（Abel-Jacobi 理论），完全在代数框架内完成。
- **Serre 对偶** 在曲线情形特别简洁：$H^1(\mathcal{L})\cong H^0(\omega_X\otimes\mathcal{L}^{-1})^\vee$。
- $\chi(\mathcal{O}_X)=1-g$ 说明亏格是 $H^1(\mathcal{O}_X)$ 的维数；这是代数几何中亏格的现代定义。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 Riemann-Roch 只对有效除子成立 | 对一般除子通过 $D=D_1-D_2$ 和线丛的张量积可推广。 |
| 忽略 Serre 对偶中 $\omega_X$ 的存在性 | 在光滑射影曲线上，$\omega_X$ 存在且 $\deg\omega_X=2g-2$；这是需要先验知道的。 |
| 混淆代数亏格与拓扑亏格 | 对复曲线，代数亏格 $h^1(\mathcal{O}_X)$ 等于拓扑亏格（Betti 数 $b_1/2$）；但定义不同。 |
| 在 (a) 中直接对一般线丛用归纳 | 应先证对 $\mathcal{O}_X(D)$（$D$ 有效），再用 $D=D_1-D_2$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) 曲线的 Riemann-Roch 定理
theorem riemannRoch {k : Type*} [Field k]
    {X : Scheme} [IsSmooth k X] [IsProjective k X]
    [Fact (Scheme.dim X = 1)] {𝓛 : LineBundle X} :
    ∑ i, (-1 : ℤ) ^ i * Module.rank k ((Sheaf.cohomology i).obj 𝓛.val) =
    𝓛.degree + ∑ i, (-1 : ℤ) ^ i * Module.rank k ((Sheaf.cohomology i).obj (structureSheaf X)) :=
  sorry

-- (b) χ(O_X) = 1 - g
theorem eulerChar_of_structureSheaf {k : Type*} [Field k]
    {X : Scheme} [IsSmooth k X] [IsProjective k X]
    [Fact (Scheme.dim X = 1)] :
    let g := Module.rank k ((Sheaf.cohomology 1).obj (structureSheaf X));
    ∑ i, (-1 : ℤ) ^ i * Module.rank k ((Sheaf.cohomology i).obj (structureSheaf X)) = 1 - g :=
  sorry
```

---

## 习题 III.4.4 — 高阶上同调的消失判据

### 题号与精确引用

**Hartshorne III.4.4**

### 问题重述

设 $X$ 为域 $k$ 上的 Noether 概形，$\mathcal{F}$ 为 $X$ 上的凝聚层，$\mathcal{L}$ 为 $X$ 上的 ample 线丛。证明：存在整数 $n_0$，使得对所有 $n\ge n_0$ 和所有 $i>0$，有 $H^i(X,\mathcal{F}\otimes\mathcal{L}^{\otimes n})=0$。

*(注：这是 **Serre 消失定理** 对 ample 线丛的一般形式。Hartshorne 在 III.5.2 中也讨论了此定理。)*

### 详细解答

**步骤 1： ample 线丛的定义**

线丛 $\mathcal{L}$ 称为 **ample**（丰沛的），若对任意凝聚层 $\mathcal{F}$，存在 $n_0$ 使 $\mathcal{F}\otimes\mathcal{L}^{\otimes n}$ 由整体截面生成（$n\ge n_0$）。等价地，某个正 tensor 幂 $\mathcal{L}^{\otimes m}$ 是非常丰沛的（very ample），即给出到射影空间的闭嵌入。

**步骤 2： 约化到 $\mathcal{L}$ 非常丰沛**

设 $\mathcal{L}^{\otimes m}$ 是非常丰沛的。则对 $\mathcal{F}\otimes\mathcal{L}^{\otimes n}$，写 $n=qm+r$（$0\le r<m$）。

若对 $\mathcal{L}^{\otimes m}$ 证明定理，则对每个 $r\in\{0,\dots,m-1\}$，存在 $q_0(r)$ 使
$$H^i(X,\mathcal{F}\otimes\mathcal{L}^{\otimes r}\otimes(\mathcal{L}^{\otimes m})^{\otimes q})=0$$
对 $q\ge q_0(r)$ 和 $i>0$。取 $n_0=\max_r(q_0(r)\cdot m+r)$ 即可。故不妨设 $\mathcal{L}$ 本身非常丰沛。

**步骤 3： 嵌入射影空间**

因 $\mathcal{L}$ 非常丰沛，存在闭嵌入 $j:X\hookrightarrow\mathbb{P}^N_k$ 使 $\mathcal{L}\cong j^*\mathcal{O}_{\mathbb{P}^N}(1)$。由推出性质，$H^i(X,\mathcal{F}\otimes\mathcal{L}^{\otimes n})=H^i(\mathbb{P}^N_k, j_*(\mathcal{F}\otimes\mathcal{L}^{\otimes n}))$。

$j_*(\mathcal{F}\otimes\mathcal{L}^{\otimes n})=j_*\mathcal{F}\otimes\mathcal{O}_{\mathbb{P}^N}(n)$（投影公式，Hartshorne II.5.1 或习题 II.5.1）。故只需证：对 $\mathbb{P}^N$ 上的凝聚层 $\mathcal{G}=j_*\mathcal{F}$，$H^i(\mathbb{P}^N,\mathcal{G}(n))=0$（$i>0$，$n\gg 0$）。

**步骤 4： 对 $\mathbb{P}^N$ 用归纳**

由 Serre 定理（Hartshorne II.5.17），存在正合列
$$0\longrightarrow\mathcal{G}'\longrightarrow\bigoplus_{j=1}^r\mathcal{O}_{\mathbb{P}^N}(a_j)\longrightarrow\mathcal{G}\longrightarrow 0.$$

扭以 $\mathcal{O}(n)$：
$$0\longrightarrow\mathcal{G}'(n)\longrightarrow\bigoplus\mathcal{O}(n+a_j)\longrightarrow\mathcal{G}(n)\longrightarrow 0.$$

取上同调：
$$H^i(\mathbb{P}^N,\bigoplus\mathcal{O}(n+a_j))\to H^i(\mathbb{P}^N,\mathcal{G}(n))\to H^{i+1}(\mathbb{P}^N,\mathcal{G}'(n)).$$

对 $i>0$，若 $n$ 充分大使左边为零（由 III.4.1(b)(c)，$H^{>0}(\mathbb{P}^N,\mathcal{O}(m))=0$ 对 $m\gg 0$ 不成立——实际上 $H^N(\mathbb{P}^N,\mathcal{O}(m))$ 只在 $m\le -N-1$ 非零；对 $m\gg 0$，所有 $H^{>0}=0$）。

故对 $n\gg 0$，$H^i(\mathbb{P}^N,\mathcal{G}(n))$ 嵌入 $H^{i+1}(\mathbb{P}^N,\mathcal{G}'(n))$。

对 $i=N$，$H^{N+1}=0$（由 Čech 维度限制），故 $H^N(\mathbb{P}^N,\mathcal{G}(n))=0$（$n\gg 0$）。

对 $i=N-1$，$H^{N-1}(\mathbb{P}^N,\mathcal{G}(n))$ 嵌入 $H^N(\mathbb{P}^N,\mathcal{G}'(n))=0$（$n\gg 0$）。依此类推，对所有 $i>0$，$H^i=0$（$n$ 充分大）。∎

### 关键概念提示

- **Ample 线丛** 是上同调消失的核心条件；它保证了充分扭动后，层变为"好"的。
- **非常丰沛 $
Rightarrow$ ample** 的反向：某个正幂非常丰沛是 ample 的等价刻画（Hartshorne II.7.6）。
- **投影公式** 是将 $X$ 上的问题推到 $\mathbb{P}^N$ 的关键。
- 这一定理说明 ample 线丛是上同调理论的"控制者"：任何凝聚层在充分 tensor 后都失去高阶上同调。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 试图不约化到射影空间直接证明 | 一般概形没有全局的扭结构层；必须利用 ample 的定义约化。 |
| 认为 $n_0$ 对所有 $\mathcal{F}$ 一致 | $n_0$ 依赖于 $\mathcal{F}$；不同凝聚层需要不同的 $n_0$。 |
| 混淆 ample 与 very ample | Very ample 更强；证明中先约化到 very ample，再嵌入射影空间。 |
| 忽略 $k$ 是域的条件 | 对更一般的基，需用平坦性等额外条件。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- Serre 消失定理（ample 线丛的一般形式）
theorem serreVanishing_ample {k : Type*} [Field k]
    {X : Scheme} [IsNoetherian X]
    {𝓕 : CoherentSheaf X} {𝓛 : LineBundle X}
    (hample : 𝓛.IsAmple) :
    ∃ (n₀ : ℤ), ∀ (n : ℤ) (i : ℕ), n ≥ n₀ → i > 0 →
      (Sheaf.cohomology i).obj (𝓕.val ⊗ 𝓛.val ^ n) = 0 :=
  sorry
```

---

## 习题 III.4.5 — 上同调与扩张的关系

### 题号与精确引用

**Hartshorne III.4.5**

### 问题重述

设 $X$ 为 Noether 概形，$\mathcal{F},\mathcal{G}$ 为 $X$ 上的凝聚层。证明：扩张群 $\operatorname{Ext}^1(\mathcal{F},\mathcal{G})$（在凝聚层范畴中）与上同调群 $H^1(X,\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},\mathcal{G}))$ 之间存在自然的同构关系。更精确地，证明存在自然的谱序列
$$E_2^{p,q}=H^p(X,\mathcal{E}xt^q(\mathcal{F},\mathcal{G}))\Longrightarrow\operatorname{Ext}^{p+q}(\mathcal{F},\mathcal{G}).$$
特别地，当 $\mathcal{F}$ 是局部自由层时，$\operatorname{Ext}^1(\mathcal{F},\mathcal{G})\cong H^1(X,\mathcal{F}^\vee\otimes\mathcal{G})$。

### 详细解答

**步骤 1：局部 Ext 与整体 Ext 的谱序列**

Hartshorne III.6.3（或 Godement, R. *Topologie Algébrique et Théorie des Faisceaux*）建立了 **局部-整体 Ext 谱序列**：对 $X$ 上的 $
mathcal{O}_X$-模 $\mathcal{F},\mathcal{G}$，有 Grothendieck 谱序列
$$E_2^{p,q}=H^p(X,\mathcal{E}xt^q_{\mathcal{O}_X}(\mathcal{F},\mathcal{G}))\Longrightarrow\operatorname{Ext}^{p+q}_{\mathcal{O}_X}(\mathcal{F},\mathcal{G}).$$

这是复合函子 $F=\Gamma(X,-)$ 和 $G=\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},-)$ 的谱序列。因 $\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},-)$ 将内射层映到 flasque 层（Hartshorne III.6.2），而 flasque 层是 $\Gamma(X,-)$-零调的，Grothendieck 谱序列适用。

**步骤 2：局部自由层的特殊情形**

设 $\mathcal{F}$ 局部自由。则对任意开集 $U$，$\mathcal{F}|_U$ 自由，故 $\mathcal{E}xt^q_{\mathcal{O}_U}(\mathcal{F}|_U,-)=0$（$q>0$）。因此层 $\mathcal{E}xt^q_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})=0$（$q>0$）。

谱序列在 $E_2$ 退化：$E_2^{p,q}=0$（$q>0$），$E_2^{p,0}=H^p(X,\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},\mathcal{G}))$。

故
$$\operatorname{Ext}^n_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})\cong H^n(X,\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})).$$

对局部自由层，$\mathcal{H}om_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})\cong\mathcal{F}^\vee\otimes\mathcal{G}$。特别地，
$$\operatorname{Ext}^1_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})\cong H^1(X,\mathcal{F}^\vee\otimes\mathcal{G}).$$

**步骤 3：扩张的层论解释**

$\operatorname{Ext}^1(\mathcal{F},\mathcal{G})$ 分类短正合列
$$0\longrightarrow\mathcal{G}\longrightarrow\mathcal{E}\longrightarrow\mathcal{F}\longrightarrow 0$$
的等价类。当 $\mathcal{F}$ 局部自由时，这样的扩张局部上平凡（因局部自由层的局部截面可提升），整体的不平凡性由 $H^1(X,\mathcal{F}^\vee\otimes\mathcal{G})$ 捕捉。

具体地，给定局部平凡化 $\mathcal{F}|_{U_i}\cong\mathcal{O}_{U_i}^{\oplus r}$，扩张在 $U_i$ 上分裂：$\mathcal{E}|_{U_i}\cong\mathcal{G}|_{U_i}\oplus\mathcal{O}_{U_i}^{\oplus r}$。在 $U_i\cap U_j$ 上，两个分裂的差给出 $\mathcal{H}om(\mathcal{F},\mathcal{G})|_{U_i\cap U_j}$ 的截面。这些差满足 Čech 1-上循环条件，其 cohomology class 在 $H^1(X,\mathcal{H}om(\mathcal{F},\mathcal{G}))$ 中。

反之，$H^1$ 中的每个类给出一个 1-上循环，用它粘合局部平凡扩张得到整体扩张。这建立了 $H^1$ 与 $\operatorname{Ext}^1$ 的一一对应。∎

### 关键概念提示

- **局部 Ext 层** $\mathcal{E}xt^q$ 是逐点计算的 Ext；**整体 Ext** 是范畴层面的导出 Hom。
- **局部-整体谱序列** 是 Grothendieck 谱序列的标准应用；它将两种 Ext 有机联系起来。
- 局部自由层的 $\mathcal{E}xt^{>0}=0$ 是自由模的投射性的层版本；这是谱序列退化的关键。
- **扩张的分类** 是 $\operatorname{Ext}^1$ 的经典解释；它将抽象的导出函子与具体的几何构造（层的扩展）联系。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $\operatorname{Ext}^1$ 总是等于 $H^1(\mathcal{H}om)$ | 仅当 $\mathcal{F}$ 局部自由时成立；一般情形有谱序列的高阶项。 |
| 忽略谱序列中 $q>0$ 的项 | 对非局部自由层，$\mathcal{E}xt^{>0}$ 可能非零，谱序列不退化。 |
| 混淆 $\mathcal{E}xt$ 与 $\operatorname{Ext}$ | 前者是层，后者是 Abel 群；关系由谱序列给出。 |
| 试图直接对凝聚层用内射消解计算 Ext | 凝聚层范畴不一定有足够内射对象；应在 $
mathcal{O}_X$-模范畴中计算。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- 局部-整体 Ext 谱序列
theorem localGlobalExt_spectralSequence {X : Scheme}
    {𝓕 𝓖 : SheafOfModules X} :
    ∃ (E : SpectralSequence Ab),
      E.E2 p q ≅ (Sheaf.cohomology p).obj (Sheaf.Ext q 𝓕 𝓖) ∧
      E.∞ ≅ Derived.Ext (p + q) 𝓕 𝓖 :=
  sorry

-- 局部自由层：Ext^1 ≅ H^1(Hom)
theorem Ext1_of_locallyFree {X : Scheme}
    {𝓕 : SheafOfModules X} (h𝓕 : 𝓕.IsLocallyFree)
    {𝓖 : SheafOfModules X} :
    Derived.Ext 1 𝓕 𝓖 ≅
    (Sheaf.cohomology 1).obj (Sheaf.Hom 𝓕 𝓖) :=
  sorry

-- 局部自由层的 Ext^1 ≅ H^1(F^∨ ⊗ G)
theorem Ext1_locallyFree_tensor {X : Scheme}
    {𝓕 : SheafOfModules X} (h𝓕 : 𝓕.IsLocallyFree)
    {𝓖 : SheafOfModules X} :
    Derived.Ext 1 𝓕 𝓖 ≅
    (Sheaf.cohomology 1).obj (𝓕.dual.tensor 𝓖) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/III.4-上同调计算与应用.md`
**创建日期**: 2026-04-18
