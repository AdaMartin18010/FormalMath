---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 凝聚数学：深入理论
---
# 凝聚数学：深入理论

> 本文件包含凝聚数学的具体构造细节、定理证明概要以及与泛函分析的深层联系。

---

## 1. 凝聚集合的具体构造

### 1.1 Profinite Sets的范畴

**定义 1.1.1** (Profinite Set)

一个**profinite set**是有限离散拓扑空间在范畴论意义下的余极限。等价地，它是一个全不连通的紧Hausdorff空间。

形式化地，一个profinite set $S$ 可以表示为：
$$S = \varprojlim_{i \in I} S_i$$
其中 $(S_i)_{i \in I}$ 是一个有限集的投影系统。

**例 1.1.2** (关键例子)

1. **p-adic整数**: $\mathbb{Z}_p = \varprojlim_n \mathbb{Z}/p^n\mathbb{Z}$
2. **绝对Galois群**: 对于域 $k$，$\text{Gal}(\bar{k}/k)$ 是profinite群
3. **Cantor集**: $\{0,1\}^\mathbb{N}$ 作为离散空间 $\{0,1\}$ 的可数积

### 1.2 凝聚集合的定义

**定义 1.2.1** (凝聚集合)

一个**凝聚集合** (condensed set) 是一个函子：
$$X: \text{ProFin}^{\text{op}} \to \text{Set}$$
满足**层条件**：对于profinite set $S$ 的任何有限覆盖 $\{S_i \to S\}_{i \in I}$，下图是正合的：
$$X(S) \to \prod_i X(S_i) \rightrightarrows \prod_{i,j} X(S_i \times_S S_j)$$

**构造 1.2.2** (从拓扑空间到凝聚集合)

对于任意拓扑空间 $T$，定义凝聚集合 $\underline{T}$ 为：
$$\underline{T}(S) = C(S, T) = \{\text{从 } S \text{ 到 } T \text{ 的连续映射}\}$$

**定理 1.2.3** (完全忠实嵌入)

函子 $T \mapsto \underline{T}$ 从**紧生成拓扑空间**的范畴到凝聚集合的范畴是**完全忠实的**。

*证明概要*:

- 满射性：由Yoneda引理，$\text{Hom}(\underline{S}, \underline{T}) \cong C(S, T)$
- 单射性：不同映射诱导不同的自然变换
- 关键观察：profinite sets 是拓扑空间范畴的"测试对象"

### 1.3 凝聚集合的层拓扑

**定义 1.3.1** (凝聚景)

**凝聚景** (condensed site) 是范畴 ProFin 配备**反规范拓扑** (anti-canonical topology)：

- 覆盖族是有限族的满射 $\{S_i \to S\}$

**命题 1.3.2**

凝聚集合的范畴 Cond(Set) 等价于凝聚景上的层范畴：
$$\text{Cond(Set)} \cong \text{Sh}(\text{ProFin})$$

---

## 2. 液体向量空间 (Liquid Vector Spaces)

### 2.1 动机与背景

**问题 2.1.1** (经典泛函分析的困境)

考虑实Banach空间 $V, W$。张量积 $V \otimes W$ 可以赋予多种拓扑：

- 投影张量积 $\hat{\otimes}_\pi$
- 内射张量积 $\hat{\otimes}_\epsilon$
- 这些选择依赖于具体应用

**Scholze的洞察**: 在凝聚框架下，存在一个"通用"的选择。

### 2.2 液体向量空间的定义

**定义 2.2.1** (液体化)

设 $V$ 是局部凸拓扑向量空间。其**液体化** (liquidification) $\mathcal{L}(V)$ 是凝聚向量空间：
$$\mathcal{L}(V)(S) = C(S, V)$$
配备自然的拓扑向量空间结构。

**定义 2.2.2** (液体向量空间)

一个凝聚向量空间 $V$ 称为**液体的** (liquid)，如果它是某个局部凸空间的液体化，并且满足特定的"光滑性"条件。

更精确地，$V$ 是液体的如果：

1. $V$ 是凸的 (convex)
2. 对于所有 profinite set $S$，$V(S)$ 是拟完备的 (quasi-complete)
3. 满足特定的有界性条件

### 2.3 关键定理：液体张量积

**定理 2.3.1** (Scholze, Clausen)

液体向量空间的范畴 $\text{Liq}$ 构成一个**对称闭幺半范畴**。

特别地，对于液体向量空间 $V, W$，存在液体张量积 $V \otimes^{\text{liq}} W$ 满足：
$$\text{Hom}(V \otimes^{\text{liq}} W, Z) \cong \text{Hom}(V, \underline{\text{Hom}}(W, Z))$$

**定理 2.3.2** (正合性)

液体张量积函子 $- \otimes^{\text{liq}} V: \text{Liq} \to \text{Liq}$ 是**正合的**。

*证明概要*:

1. 构造性：使用幂级数展开
2. 关键工具：$\ell^p$-空间在液体框架下的表现
3. 技术核心：$p$-范数的"液体"插值

### 2.4 具体例子

**例 2.4.1** (Banach空间的液体化)

对于Banach空间 $E$，其液体化 $\mathcal{L}(E)$ 满足：

- $\mathcal{L}(E)(*) = E$（在单点上的截面）
- 对于 profinite set $S = \varprojlim S_i$：
$$\mathcal{L}(E)(S) = \varinjlim C(S_i, E) = \text{(映射的某种完备化)}$$

**例 2.4.2** ($\ell^p$-空间)

对于 $1 \leq p < \infty$，考虑 $\ell^p(\mathbb{N})$。其液体张量积满足：
$$\ell^p \otimes^{\text{liq}} \ell^q \cong \ell^r$$
其中 $\frac{1}{r} = \frac{1}{p} + \frac{1}{q} - 1$（如果右边 $\geq 0$）。

这与经典的张量积公式一致，但液体框架提供了更自然的推导。

**例 2.4.3** (光滑函数空间)

设 $M$ 是光滑流形，$C^\infty(M)$ 是光滑函数空间。则：

- $C^\infty(M)$ 自然地是一个液体向量空间
- 对于紧集 $K \subset M$，$C^\infty(K)$ 也是液体的
- 分布空间 $\mathcal{D}'(M)$ 作为对偶，有自然的液体结构

---

## 3. 与泛函分析的深层联系

### 3.1 经典泛函分析的凝聚对应

| 经典概念 | 凝聚对应 | 优势 |
|---------|---------|------|
| Banach空间 | 液体向量空间 | 张量积正合 |
| 局部凸空间 | 凝聚局部凸空间 | 极限表现良好 |
| 连续线性映射 | 凝聚线性映射 | 自然构成闭范畴 |
| 对偶空间 | 凝聚对偶 |  reflexivity 自动 |
| 分布 | 凝聚分布 | 与层论兼容 |

### 3.2 核定理的凝聚版本

**定理 3.2.1** (Schwartz核定理的凝聚形式)

设 $M, N$ 是光滑流形，则：
$$\underline{\text{Hom}}(C^\infty(M), C^\infty(N)) \cong C^\infty(M \times N)$$
在液体向量空间范畴中成立。

*注记*: 经典版本需要 Schwartz 空间的核性条件，而凝聚版本自动成立。

### 3.3 $p$-adic分析中的固体向量空间

**定义 3.3.1** (固体向量空间)

对于非阿基米德域（如 $\mathbb{Q}_p$），**固体向量空间** (solid vector spaces) 是与液体对偶的概念。

**定理 3.3.2** (Fargues-Fontaine应用)

固体向量空间在 $p$-adic Hodge 理论中有重要应用：

- 完美oid空间的同调可以用固体向量空间描述
- Fargues-Fontaine曲线上的向量丛与固体向量空间相关

---

## 4. 形式化进展追踪

### 4.1 Liquid Tensor Experiment

**项目概述** (Johan Commelin et al., 2020-2022)

目标：在 Lean 证明助手中形式化凝聚数学的核心结果。

**主要成果**:

| 定理/构造 | 状态 | Lean文件 |
|----------|------|----------|
| 凝聚集合定义 | ✅ 完成 | `condensed/basic.lean` |
| 液体张量积 | ✅ 完成 | `liquid_tensor.lean` |
| 正合性定理 | ✅ 完成 | `exactness.lean` |
| 主要不等式 | ✅ 完成 | `main_inequality.lean` |

**定理 4.1.1** (形式化的主要结果)

对于实向量空间 $V$ 和 $p \in (0, 1)$，以下复合映射是满射：
$$\mathcal{M}_{p'}(S) \otimes \ell^p(V) \to \mathcal{M}_{p'}(S, \ell^p(V)) \to \ell^p(\mathcal{M}_{p'}(S, V))$$

其中 $\mathcal{M}_{p'}$ 表示 $p'$-测度空间。

### 4.2 Mathlib4中的凝聚数学

**当前状态** (截至2025年):

```
mathlib4/Condensed/
├── Basic.lean          # 凝聚集合基础定义
├── Abelian.lean        # 凝聚阿贝尔群
├── Module.lean         # 凝聚模
├── Liquid/             # 液体向量空间
│   ├── Basic.lean
│   ├── Tensor.lean
│   └── Dual.lean
└── Solid/              # 固体向量空间
    └── Basic.lean
```

**关键定义** (Lean4代码片段):

```lean
-- 凝聚集合的定义
structure CondensedSet where
  toPresheaf : Profiniteᵒᵖ ⥤ Type*
  sheafCondition : Presheaf.IsSheaf proEtaleTopology toPresheaf

-- 液体向量空间
structure LiquidVectorSpace (p : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] extends CondensedModule ℝ where
  -- 液体条件
  isLiquid : ∀ S : Profinite, IsNormedSpace (toCondensedModule.obj (op S))
```

### 4.3 形式化中的数学洞见

**洞见 1**: 层条件的验证比预期复杂

- 需要仔细处理 profinite sets 的覆盖
- 有限性条件在证明中起关键作用

**洞见 2**: 范数估计的系统性处理

- 液体张量积的构造涉及精细的范数不等式
- Lean的实数分析库提供了良好支持

**洞见 3**: 与经典泛函分析的对应

- 形式化过程揭示了"经典"与"凝聚"的精确关系
- 某些经典定理在凝聚框架下有更简单的证明

---

## 5. 高级专题

### 5.1 凝聚上同调

**定义 5.1.1** (凝聚上同调)

对于凝聚集合 $X$ 和凝聚阿贝尔群 $\mathcal{F}$，定义：
$$H^i_{\text{cond}}(X, \mathcal{F}) := \text{Ext}^i_{\text{Cond(Ab)}}(\mathbb{Z}_X, \mathcal{F})$$

**定理 5.1.2** (与经典上同调的比较)

对于紧Hausdorff空间 $X$ 和离散阿贝尔群 $A$：
$$H^i_{\text{cond}}(\underline{X}, \underline{A}) \cong H^i_{\text{sheaf}}(X, A)$$
凝聚上同调与经典层上同调一致。

### 5.2 导出凝聚集合

**定义 5.2.1** (导出凝聚集合)

**导出凝聚集合** (derived condensed sets) 是凝聚集合的导出范畴 $D(\text{Cond(Set)})$ 中的对象。

**应用**:

- 拓扑Hochschild同调 (THH) 的凝聚描述
- 循环同调的凝聚版本

---

## 参考文献

1. Scholze, P. "Lectures on Condensed Mathematics", arXiv:1909.06791
2. Scholze, P., Clausen, D. "Lectures on Analytic Geometry", arXiv:1909.06792
3. Commelin, J. et al. "Liquid Tensor Experiment", leanprover-community/liquid
4. Clausen, D., Scholze, P. "Condensed Mathematics and Complex Geometry"
5. Fargues, L., Fontaine, J-M. "Courbes et fibrés vectoriels en théorie de Hodge p-adique"
