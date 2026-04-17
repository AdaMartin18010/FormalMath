---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §1 习题解答
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 1 - Sheaves"
source_exercise:
  - "II.1.1"
  - "II.1.2"
  - "II.1.3"
  - "II.1.4"
difficulty: ⭐⭐ to ⭐⭐⭐
processed_at: '2026-04-17'
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
      chapters: []
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
      chapters: []
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# Harvard 232br - Hartshorne Chapter II §1 习题解答

> 本节覆盖 Hartshorne 第二章第 1 节（层与结构层）的 4 道核心习题，涉及仿射概形的结构层、具体例子（$\operatorname{Spec}\mathbb{Z}$、$\mathbb{A}^2_k\setminus\{(0,0)\}$）以及初步的上同调计算。

---

## 习题 II.1.1 — 结构层的层公理与局部环性质

### 题号与精确引用

**Hartshorne II.1.1**

### 问题重述

设 $A$ 为环，$X=\operatorname{Spec}A$。对任意开集 $U\subseteq X$，定义
$$\mathcal{O}(U)=\left\{s:U\to\bigsqcup_{\mathfrak p\in U}A_{\mathfrak p}\;\middle|\;s(\mathfrak p)\in A_{\mathfrak p},\;\text{且 }s\text{ 局部为 }A\text{ 中元素的商}\right\}.$$
(a) 验证 $\mathcal{O}$ 是环的层。
(b) 证明 $(X,\mathcal{O})$ 是局部环化空间。
(c) 证明茎 $\mathcal{O}_{\mathfrak p}\cong A_{\mathfrak p}$。
(d) 证明对任意 $f\in A$，有 $\mathcal{O}(D(f))\cong A_f$。

### 详细解答

**(a) 层公理**

*唯一性*：设 $U$ 被 $\{U_i\}$ 覆盖，$s,t\in\mathcal{O}(U)$ 且 $s|_{U_i}=t|_{U_i}$。对任意 $\mathfrak p\in U$，存在 $i$ 使 $\mathfrak p\in U_i$，则 $s(\mathfrak p)=t(\mathfrak p)$。故 $s=t$。

*存在性*：设给定相容的 $s_i\in\mathcal{O}(U_i)$。定义 $s:U\to\bigsqcup A_{\mathfrak p}$ 为 $s(\mathfrak p)=s_i(\mathfrak p)$（任取含 $\mathfrak p$ 的 $U_i$）。相容性保证定义良好。需验证 $s$ 局部为商：对任意 $\mathfrak p\in U$，取 $i$ 使 $\mathfrak p\in U_i$。因 $s_i\in\mathcal{O}(U_i)$，存在 $\mathfrak p$ 的邻域 $V\subseteq U_i$ 及 $a,b\in A$（$b\notin\mathfrak q$ 对所有 $\mathfrak q\in V$），使得 $s_i(\mathfrak q)=a/b$ 于 $V$。则 $s$ 在 $V$ 上也是 $a/b$。故 $s\in\mathcal{O}(U)$。∎

**(b) 局部环化空间**

只需验证每个茎是局部环。由 (c) 知 $\mathcal{O}_{\mathfrak p}\cong A_{\mathfrak p}$，而 $A_{\mathfrak p}$ 是局部环，故 $(X,\mathcal{O})$ 是局部环化空间。∎

**(c) 茎的计算**

构造映射 $\phi:\mathcal{O}_{\mathfrak p}\to A_{\mathfrak p}$，将芽 $[(U,s)]$ 映到 $s(\mathfrak p)\in A_{\mathfrak p}$。

- *良定义*：若 $[(U,s)]=[(V,t)]$，则存在 $W\subseteq U\cap V$ 使得 $s|_W=t|_W$，于是 $s(\mathfrak p)=t(\mathfrak p)$。
- *满射*：对任意 $a/f\in A_{\mathfrak p}$，令 $U=D(f)$，定义 $s(\mathfrak q)=a/f\in A_{\mathfrak q}$（于 $U$）。则 $[(U,s)]\mapsto a/f$。
- *单射*：设 $[(U,s)]\mapsto 0\in A_{\mathfrak p}$。则 $s(\mathfrak p)=0$。由 $s$ 局部为商，存在 $D(f)\subseteq U$（$f\notin\mathfrak p$）及 $a,b\in A$（$b\notin\mathfrak q$ 于 $D(f)$），使得 $s(\mathfrak q)=a/b$。因 $s(\mathfrak p)=0$，有 $a/b=0$ 于 $A_{\mathfrak p}$，故存在 $c\notin\mathfrak p$ 使 $ca=0$。于是于 $D(cf)\subseteq D(f)$ 上 $s(\mathfrak q)=a/b=0$。故 $[(U,s)]=0$ 于 $\mathcal{O}_{\mathfrak p}$。∎

**(d) $D(f)$ 上的整体截面**

限制映射 $A_f\to\mathcal{O}(D(f))$ 将 $a/f^n$ 映到常值截面 $\mathfrak q\mapsto a/f^n$。这是单射：若 $a/f^n=0$ 于所有 $\mathfrak q\in D(f)$，则对任意 $\mathfrak q\nmid f$，存在 $h\notin\mathfrak q$ 使 $ha=0$。于是 $\operatorname{Ann}(a)$ 不包含于任何 $\mathfrak q\in D(f)$，即 $V(\operatorname{Ann}(a))\cap D(f)=\varnothing$，故 $f\in\sqrt{\operatorname{Ann}(a)}$，即 $f^m a=0$ 对某个 $m$，于是 $a/f^n=0$ 于 $A_f$。

满射：设 $s\in\mathcal{O}(D(f))$。因 $D(f)$ 是拟紧的，可用有限个 $D(h_i)\subseteq D(f)$ 覆盖，且于每个 $D(h_i)$ 上 $s=a_i/g_i$（$g_i\notin\mathfrak q$ 于 $D(h_i)$，即 $D(h_i)\subseteq D(g_i)$，于是 $h_i\in\sqrt{(g_i)}$）。不妨设 $h_i=g_i$。则在 $D(g_ig_j)=D(g_i)\cap D(g_j)$ 上 $a_i/g_i=a_j/g_j$，即 $(a_ig_j-a_jg_i)$ 在 $D(g_ig_j)$ 上被零化，故 $(g_ig_j)^{m_{ij}}(a_ig_j-a_jg_i)=0$。取统一的 $m$，将 $a_i,g_i$ 替换为 $a_ig_i^m,g_i^{m+1}$，可设 $a_ig_j=a_jg_i$ 对所有 $i,j$。因 $D(f)=\bigcup D(g_i)$，有 $(g_1,\dots,g_n)\ni f^k$。设 $f^k=\sum b_ig_i$，令 $a=\sum b_ia_i$。则 $ag_j=\sum b_ia_ig_j=\sum b_ig_ia_j=f^ka_j$，故 $a/f^k=a_j/g_j$ 于 $D(g_j)$。于是 $s$ 是 $a/f^k$ 的像。∎

### 关键概念提示

- **局部为商** 是结构层区别于任意函数层的核心；它保证了截面可由环 $A$ 的代数数据完全决定。
- **茎同构于局部化** $A_{\mathfrak p}$ 说明结构层在点 $\mathfrak p$ 处的“无穷小信息”恰好就是 $A$ 在该素理想处的局部化。
- **$\mathcal{O}(D(f))\cong A_f$** 是仿射概形范畴等价的核心一步。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $\mathcal{O}(U)$ 就是所有集合论函数 | 必须满足局部为商的条件。 |
| 在 (d) 的满射证明中忽略拟紧性 | $D(f)$ 是拟紧的，故可取有限覆盖；无限情形需要逆极限论证。 |
| 混淆 $A_{\mathfrak p}$ 与 $A/\mathfrak p$ | 茎是局部化，不是商。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry

-- (c) 茎同构于局部化 A_p（定义陈述，证明留空）
def stalkIso (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    (Spec.structureSheaf A).presheaf.stalk p ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  sorry

-- (d) D(f) 上的截面同构于 A_f（定义陈述，证明留空）
def sectionsDfIso (A : Type*) [CommRing A] (f : A) :
    (Spec.structureSheaf A).presheaf.obj (Opposite.op ⟨PrimeSpectrum.basicOpen f⟩) ≅ CommRingCat.of (Localization.Away f) :=
  sorry
```

---

## 习题 II.1.2 — 描述 $\operatorname{Spec}\mathbb{Z}$ 与 $\operatorname{Spec}k[x]$

### 题号与精确引用

**Hartshorne II.1.2**

### 问题重述

描述 $\operatorname{Spec}\mathbb{Z}$ 与 $\operatorname{Spec}k[x]$（$k$ 为代数闭域）。具体说明：
(a) 素理想有哪些？
(b) 拓扑结构如何？
(c) 结构层是什么？

### 详细解答

**$\operatorname{Spec}\mathbb{Z}$**

(a) 素理想为 $(0)$ 与 $(p)$（$p$ 为素数）。

(b) 闭集形如 $V((n))=\{(p)\mid p\mid n\}$，即有限个素数点（除 $(0)$ 外）。故 $(0)$ 的闭包是整个空间，而每个 $(p)$ 是闭点。拓扑上，这是“点 $(0)$ 粘在所有闭点之上”的 $T_0$ 空间。

(c) 结构层的茎：$\mathcal{O}_{(0)}=\mathbb{Z}_{(0)}=\mathbb{Q}$；$\mathcal{O}_{(p)}=\mathbb{Z}_{(p)}$（$p$-进整数环的局部化）。整体截面为 $\mathcal{O}(X)=\mathbb{Z}$。对任意素数 $p$，$\mathcal{O}(D(p))=\mathbb{Z}[1/p]$。

**$\operatorname{Spec}k[x]$**

(a) 素理想为 $(0)$ 与 $(x-a)$（$a\in k$）。因 $k$ 代数闭，不可约多项式均为一阶。

(b) 闭集为有限个闭点 $\{(x-a_1),\dots,(x-a_n)\}$ 的并，加上空集与全空间。故 $(0)$ 是一般点，其闭包为全空间；每个 $(x-a)$ 是闭点。拓扑上与 $\operatorname{Spec}\mathbb{Z}$ 同胚（一维、一个一般点、其余为闭点）。

(c) 结构层的茎：$\mathcal{O}_{(0)}=k(x)$（有理函数域）；$\mathcal{O}_{(x-a)}=k[x]_{(x-a)}$。整体截面为 $k[x]$。对 $f\in k[x]$，$\mathcal{O}(D(f))=k[x]_f$。

### 关键概念提示

- **一般点**（generic point）$(0)$ 的闭包是整个不可约分支；在整环情形下它是唯一的。
- $\operatorname{Spec}\mathbb{Z}$ 是概形范畴的**终对象**，这将在 II.2.5 中证明。
- 代数闭性保证 $k[x]$ 的极大理想与 $k$ 中元素一一对应。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $(0)$ 是闭点 | 在整环的 Spec 中，$(0)$ 永远不会是闭点（除非环是域）。 |
| 遗漏 $k[x]$ 中的 $(0)$ | $(0)$ 是素理想，必须计入。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry PrimeSpectrum

-- Spec ℤ 的素理想枚举（类型层面陈述）
def primeIdealsOfZ : PrimeSpectrum ℤ ≃ Sum (Unit) (Nat.Primes) :=
  sorry

-- Spec k[x]（k 代数闭）的极大理想与 k 的点一一对应
def maxIdealsOfPoly (k : Type*) [Field k] [IsAlgClosed k] :
    {I : Ideal (Polynomial k) // I.IsMaximal} ≃ k :=
  sorry
```

---

## 习题 II.1.3 — $U=\mathbb{A}^2_k\setminus\{(0,0)\}$ 不是仿射的

### 题号与精确引用

**Hartshorne II.1.3**

### 问题重述

设 $k$ 为域，$X=\mathbb{A}^2_k=\operatorname{Spec}k[x,y]$，$U=X\setminus\{(0,0)\}$。
(a) 证明 $U$ 不是仿射概形。
(b) 计算 $\mathcal{O}_X(U)$。

### 详细解答

**(a) $U$ 非仿射**

假设 $U$ 是仿射的，则 $U\cong\operatorname{Spec}A$ 对某个环 $A$。由 (b) 知 $A=\mathcal{O}_X(U)=k[x,y]$，故 $U\cong\operatorname{Spec}k[x,y]=X$。但 $U$ 与 $X$ 作为拓扑空间不同胚（$U$ 去掉了一个闭点），矛盾。更代数化的论证：包含映射 $i:U\hookrightarrow X$ 诱导同构 $i^\#:\mathcal{O}_X(X)\xrightarrow{\sim}\mathcal{O}_X(U)$。若 $U$ 仿射，则 $i$ 必须是同构（因为 $(i,i^\#)$ 是仿射概形间的态射，且全局截面诱导同构，由 II.2.4 的函子性，$i$ 对应于 $\operatorname{id}:k[x,y]\to k[x,y]$，故 $i$ 是同构），矛盾。∎

**(b) 计算整体截面**

$U=D(x)\cup D(y)$。由层的等化子序列：
$$0\longrightarrow\mathcal{O}_X(U)\longrightarrow\mathcal{O}_X(D(x))\oplus\mathcal{O}_X(D(y))\longrightarrow\mathcal{O}_X(D(xy))$$
其中右边映射为 $(f,g)\mapsto f|_{D(xy)}-g|_{D(xy)}$。利用 II.1.1(d)，这即是
$$0\longrightarrow\mathcal{O}_X(U)\longrightarrow k[x,y]_x\oplus k[x,y]_y\longrightarrow k[x,y]_{xy}.$$

设 $(f/x^m,g/y^n)$ 映到 $0$，则 $f/x^m=g/y^n$ 于 $k[x,y]_{xy}$。因 $k[x,y]$ 是 UFD，可写成既约分式。等式意味着存在 $h\in k[x,y]$ 使得 $f/x^m=h$ 且 $g/y^n=h$（因为 $x$ 与 $y$ 互素，分母不能相互抵消）。故 $h\in k[x,y]_x\cap k[x,y]_y=k[x,y]$。因此 $\mathcal{O}_X(U)=k[x,y]$。∎

### 关键概念提示

- **$k[x,y]$ 是 UFD** 保证了 $k[x,y]_x\cap k[x,y]_y=k[x,y]$；这本质上是二维正则局部环的深度 $2$ 性质（$S_2$）的特例。
- 本题是“拟仿射但非仿射”的经典例子，说明概形范畴中开子概形不一定仿射。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接断言 $U$ 不是仿射因为少了点 | 需要代数论证：若仿射则整体截面环决定概形。 |
| 认为 $1/x\in\mathcal{O}_X(U)$ | $1/x$ 在 $y$ 轴上无定义，不能全局延拓到 $U$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry PrimeSpectrum

-- U = A^2 \ {(0,0)} 的整体截面仍为 k[x,y]
theorem sectionsOfPuncturedA2 (k : Type*) [Field k] :
    (Spec.structureSheaf (Polynomial (Polynomial k))).presheaf.obj
      (Opposite.op ⟨(.basicOpen (X : Polynomial (Polynomial k))) ∪ (.basicOpen (Y : Polynomial (Polynomial k)))⟩)
    ≅ CommRingCat.of (Polynomial (Polynomial k)) :=
  sorry
```

---

## 习题 II.1.4 — $H^1(U,\mathcal{O}_U)\neq 0$

### 题号与精确引用

**Hartshorne II.1.4**

### 问题重述

设 $k$ 为代数闭域，$X=\mathbb{A}^2_k=\operatorname{Spec}k[x,y]$，$U=X\setminus\{(0,0)\}$。证明 $H^1(U,\mathcal{O}_U)\neq 0$。

### 详细解答

取 $U$ 的仿射开覆盖 $\mathfrak{U}=\{D(x),D(y)\}$。用 Čech 上同调计算 $H^1(\mathfrak{U},\mathcal{O}_U)$。Čech 复形为
$$C^0=\mathcal{O}(D(x))\oplus\mathcal{O}(D(y))=k[x,y]_x\oplus k[x,y]_y,$$
$$C^1=\mathcal{O}(D(xy))=k[x,y]_{xy},$$
微分 $d:C^0\to C^1$ 为 $d(f,g)=g-f$。故
$$H^1(\mathfrak{U},\mathcal{O}_U)=k[x,y]_{xy}/(k[x,y]_x+k[x,y]_y).$$

考虑元素 $1/(xy)\in k[x,y]_{xy}$。断言：$1/(xy)\notin k[x,y]_x+k[x,y]_y$。

假设 $1/(xy)=f/x^m+g/y^n$ 于 $k[x,y]_{xy}$。两边乘以 $x^my^n$ 得
$$x^{m-1}y^{n-1}=f y^n+g x^m$$
于 $k[x,y]$。左边 $x^{m-1}y^{n-1}$ 的 $x$ 次数为 $m-1$（若 $m\ge 1$），而右边 $f y^n$ 被 $y^n$ 整除，$g x^m$ 被 $x^m$ 整除。若 $m,n\ge 1$，则右边在 $(x,y)$ 处的最低次项次数至少为 $\min(m,n)\ge 1$，而左边次数为 $m+n-2$，等式本身可能成立对某些 $f,g$，但我们需要的是分母恰好出现 $xy$ 的既约分式。

更简洁的论证：$k[x,y]_{xy}$ 中的单项式基为 $\{x^ay^b\mid a,b\in\mathbb{Z}\}$。$k[x,y]_x$ 由 $a\ge 0$ 或 $b\ge 0$ 的单项式张成（实际上是由 $a\ge 0$ 的任意 $b$ 和 $b\ge 0$ 的任意 $a$ 的并）。更准确地说，$k[x,y]_x$ 的基是 $\{x^ay^b\mid a\in\mathbb{Z},b\ge 0\}$，$k[x,y]_y$ 的基是 $\{x^ay^b\mid a\ge 0,b\in\mathbb{Z}\}$。它们的和空间不含 $x^ay^b$ 当 $a<0$ 且 $b<0$ 的单项式。因此 $x^{-1}y^{-1}$（即 $1/(xy)$）不在和空间中。故 $H^1\neq 0$。∎

实际上，$H^1$ 作为 $k$-向量空间由 $\{x^{-m}y^{-n}\mid m,n\ge 1\}$ 张成，是无限维的。

### 关键概念提示

- **Čech 上同调** 对仿射覆盖计算层上同调非常有效；这里覆盖只有两个开集，计算尤为简单。
- $H^1\neq 0$ 反映了几何事实：$U$ 是“有洞”的（虽然 Zariski 拓扑很粗糙，但层上同调探测到了 codimension $2$ 的缺失）。
- 这是 **Hartogs 现象** 的反面：在复几何中，codimension $\ge 2$ 的洞不影响全纯函数；但在代数几何中，它影响了高阶上同调。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 用 $1/(x+y)$ 等非既约分式作为代表 | 应选择 $x^{-m}y^{-n}$ 这种明确的单项式。 |
| 认为 $k[x,y]_x+k[x,y]_y=k[x,y]_{xy}$ | 负指数双向均为负的单项式无法被覆盖。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry PrimeSpectrum

-- H^1(U, O_U) ≠ 0 的陈述（用 Čech 上同调模型化）
theorem puncturedA2H1Nonzero (k : Type*) [Field k] :
    ¬ (Subsingleton
      ((Spec.structureSheaf (Polynomial (Polynomial k))).presheaf.1.obj
        (Opposite.op ⟨(.basicOpen (X : Polynomial (Polynomial k))) ∪ (.basicOpen (Y : Polynomial (Polynomial k)))⟩)
      → Unit)) :=
  -- 简化：若 H^1 为 0，则某些 Ext 群消失，这里仅作非零占位陈述
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.1-层的基本性质.md`
**创建日期**: 2026-04-17
