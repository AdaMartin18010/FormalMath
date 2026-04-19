---
title: Étale上同调
description: 深入介绍平展态射、平展拓扑、平展上同调的定义、比较定理以及它在韦伊猜想证明中的核心作用。
msc_primary: 14

  - 14F20
  - 14F30
  - 14G15
processed_at: '2026-04-16'
---

# Étale 上同调

## 引言

1960年代，格洛腾迪克为了解决韦伊猜想（Weil conjectures），创造了一种革命性的上同调理论——**étale 上同调**。Zariski 拓扑过于粗糙，无法提供足够的拓扑信息来计算满足韦伊猜想所需的上同调群。格洛腾迪克的深刻洞察是：不放宽 Zariski 拓扑，而是放宽"覆盖"的概念，用**平展态射**（étale morphisms）作为覆盖映射，从而定义一种新的**Grothendieck 拓扑**。

这一理论最终由 Deligne 在1974年完成韦伊猜想的证明，成为20世纪数学最伟大的成就之一。本教程将系统介绍 étale 上同调的定义、性质与核心应用。

---

## 一、平展态射

### 1.1 定义

概形态射 $f: X \to Y$ 称为**平展的**（étale），如果它同时满足：
1. $f$ 是**平坦的**（flat）；
2. $f$ 是**非分歧的**（unramified）。

平展态射是代数几何中的**局部同构**。若将概形类比于复流形，则平展态射类似于局部双全纯映射。

### 1.2 等价刻画

对局部有限展示的态射，以下条件等价：
- $f$ 是平展的；
- 对每个 $x \in X$，茎 $\mathcal{O}_{X,x}$ 是 $\mathcal{O}_{Y,f(x)}$ 上的有限展示平坦代数，且 $\Omega_{X/Y} = 0$；
- $f$ 局部上具有形式 $\text{Spec}(B) \to \text{Spec}(A)$，其中 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_n)$，且 Jacobian 行列式在 $B$ 中可逆。

### 1.3 基本例子

- **开浸入**：是平展的（但不是满射的）。
- **域的有限可分扩张**：$\text{Spec}(L) \to \text{Spec}(K)$ 是平展的当且仅当 $L/K$ 是有限可分的。
- **非分歧覆叠**：在特征零的代数闭域上，光滑曲线之间的有限覆叠若是非分歧的，则它是平展的。

---

## 二、平展位型与平展层

### 2.1 Grothendieck 拓扑

设 $X$ 是概形。$X$ 上的**平展位型**（étale site）$X_{\text{ét}}$ 定义如下：
- **对象**：所有平展态射 $U \to X$；
- **覆盖**：一族平展态射 $\{U_i \to U\}$ 是覆盖，如果 $\bigcup_i \text{Im}(U_i) = U$（在底拓扑空间中满射）。

这一定义的关键在于：对象不再是 $X$ 的开子集，而是所有平展到 $X$ 的概形。这使得"邻域"的概念大大扩展。

### 2.2 平展层

**平展层**（étale sheaf）是 $X_{\text{ét}}$ 上的层，即一个反变函子 $\mathcal{F}: X_{\text{ét}}^{\text{op}} \to \mathbf{Set}$（或 $\mathbf{Ab}$），满足对平展覆盖的粘合条件。

**例子**：
- **常层**：$\underline{A}(U) = A^{\pi_0(U)}$
- **结构层**：$\mathbb{G}_a(U) = \Gamma(U, \mathcal{O}_U)$
- **乘法群层**：$\mathbb{G}_m(U) = \Gamma(U, \mathcal{O}_U^\times)$
- **根层**：$\mu_n(U) = \{f \in \Gamma(U, \mathcal{O}_U^\times) \mid f^n = 1\}$

### 2.3 可构造层

在 étale 上同调中，**可构造层**（constructible sheaf）是最重要的研究对象之一。一个 Abel 群平展层 $\mathcal{F}$ 称为可构造的，如果存在 $X$ 的有限分划为局部闭子集，使得 $\mathcal{F}$ 在每个子集上的限制是局部常值的，且茎是有限 Abel 群。

---

## 三、平展上同调的定义

### 3.1 平展上同调群

设 $\mathcal{F}$ 是 $X$ 上的 Abel 群平展层。**平展上同调群**定义为：

$$H_{\text{ét}}^i(X, \mathcal{F}) = R^i \Gamma_{\text{ét}}(X, \mathcal{F})$$

即全局截面函子 $\Gamma_{\text{ét}}(X, -): \mathbf{Ab}(X_{\text{ét}}) \to \mathbf{Ab}$ 的右导出函子。

### 3.2 高阶直像

设 $f: X \to Y$ 是概形态射，$\mathcal{F}$ 是 $X$ 上的平展层。可以定义**高阶直像层**：

$$R^i f_* \mathcal{F}$$

它是 $Y$ 上的平展层，其茎满足：

$$(R^i f_* \mathcal{F})_{\bar{y}} = H_{\text{ét}}^i(X \times_Y \text{Spec}(\mathcal{O}_{Y,\bar{y}}^{\text{sh}}), \mathcal{F})$$

这里使用了**严格 Hensel 局部环**，它是 étale 拓扑中"点"的局部化。

---

## 四、比较定理

### 4.1 与奇异上同调的比较

étale 上同调最伟大的成就之一是与经典拓扑上同调的比较定理。

**Artin 比较定理**：设 $X$ 是复代数簇（即有限型 $\mathbb{C}$-概形），$\mathcal{F}$ 是有限 Abel 群上的局部常值平展层。则对所有 $i \geq 0$：

$$H_{\text{ét}}^i(X, \mathcal{F}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathcal{F})$$

其中右边是 $X$ 的解析拓扑空间上的奇异上同调。

这一定理说明，étale 上同调确实"捕获"了经典拓扑的信息。

### 4.2 复形比较

对局部系统 $\mathbb{Z}/\ell^n\mathbb{Z}$，Artin 比较定理给出：

$$H_{\text{ét}}^i(X, \mathbb{Z}/\ell^n\mathbb{Z}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{Z}/\ell^n\mathbb{Z})$$

取逆向极限，得到 **$\ell$-进上同调**的比较：

$$H_{\text{ét}}^i(X, \mathbb{Z}_\ell) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{Z}_\ell$$

---

## 五、$\ell$-进上同调与韦伊猜想

### 5.1 $\ell$-进上同调

设 $X$ 是域 $k$ 上的概形，$\ell \neq \text{char}(k)$ 是素数。**$\ell$-进上同调**定义为：

$$H_{\text{ét}}^i(X, \mathbb{Q}_\ell) = \left(\varprojlim_n H_{\text{ét}}^i(X, \mathbb{Z}/\ell^n\mathbb{Z})\right) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$$

这是一个 $\mathbb{Q}_\ell$-向量空间，具有与经典上同调类似的性质：
- Poincaré 对偶
- Künneth 公式
- Lefschetz 不动点公式
- Hard Lefschetz 定理（由 Deligne 证明）

### 5.2 Frobenius 作用

设 $X$ 是有限域 $\mathbb{F}_q$ 上的概形。几何 Frobenius 映射 $F: X \to X$ 在坐标上作用为 $x \mapsto x^q$。它在 $H_{\text{ét}}^i(X_{\overline{\mathbb{F}}_q}, \mathbb{Q}_\ell)$ 上诱导一个线性自同态。

**Lefschetz 迹公式**（Grothendieck）：

$$|X(\mathbb{F}_{q^n})| = \sum_{i=0}^{2d} (-1)^i \text{Tr}(F^n | H_{\text{ét}}^i(X_{\overline{\mathbb{F}}_q}, \mathbb{Q}_\ell))$$

这直接联系了点数与上同调，是韦伊猜想证明的核心公式。

---

## 六、习题

### 习题 1
证明：若 $L/K$ 是有限 Galois 扩张，则 $\text{Spec}(L) \to \text{Spec}(K)$ 是平展的，且平展覆盖 $\{\text{Spec}(L) \to \text{Spec}(K)\}$ 对应于 Galois 理论中的正规扩张。

### 习题 2
设 $X = \mathbb{G}_m = \text{Spec}(k[x, x^{-1}])$（$k$ 代数闭，$\text{char}(k) \nmid n$）。计算 $H_{\text{ét}}^1(X, \mu_n)$，并解释其与 $X$ 上 $n$ 次覆叠的关系。

### 习题 3
解释为什么 étale 上同调中的 Poincaré 对偶需要 $X$ 是光滑固有概形，且维数为 $d$，形式为：
$$H_{\text{ét}}^i(X, \mathbb{Q}_\ell) \times H_{\text{ét}}^{2d-i}(X, \mathbb{Q}_\ell) \to \mathbb{Q}_\ell(-d)$$

### 习题 4
设 $E/\mathbb{F}_q$ 是椭圆曲线。利用 $|E(\mathbb{F}_q)| = q + 1 - a$，其中 $a = \text{Tr}(F | H_{\text{ét}}^1(E, \mathbb{Q}_\ell))$，证明 Hasse 界 $|a| \leq 2\sqrt{q}$。（提示：利用 Weil 配对。）

---

## 延伸阅读

- **教材推荐**：Milne, J.S. *Étale Cohomology*, Princeton University Press, 1980.
- **网络资源**：Stacks Project, Tag [03Q3](https://stacks.math.columbia.edu/tag/03Q3).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/02-étale上同调](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/02-étale上同调.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/07-平展基本群](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/07-平展基本群.md)

---

**文档状态**：✅ 完成  
**字数**：约 3,000 字  
**最后更新**：2026-04-16
