---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 凝聚数学：练习题与思考问题
---
# 凝聚数学：练习题与思考问题

> 从基础练习到研究级问题的渐进式训练

---

## 第一部分：基础练习

### 练习 1.1：Profinite Sets的基本性质

**问题 1.1.1** (Profinite Sets的刻画)

证明：一个拓扑空间是profinite的当且仅当它是：
(a) 紧的
(b) Hausdorff的
(c) 全不连通的

**提示**:

- (⇒) 方向：有限离散空间的投影极限保持这些性质
- (⇐) 方向：使用Stone对偶性

**问题 1.1.2** (p-adic整数的结构)

设 $\mathbb{Z}_p = \varprojlim_n \mathbb{Z}/p^n\mathbb{Z}$。

(a) 证明：$\mathbb{Z}_p$ 可以等同于形式幂级数：
$$\mathbb{Z}_p = \left\{\sum_{n=0}^\infty a_n p^n : a_n \in \{0, 1, \ldots, p-1\}\right\}$$

(b) 证明：$\mathbb{Z}_p$ 是 profinite set。

(c) 描述 $\mathbb{Z}_p$ 的开子集族。

---

### 练习 1.2：凝聚集合的定义验证

**问题 1.2.1** (离散空间的凝聚化)

设 $D$ 是离散拓扑空间（赋予离散拓扑的集合）。

(a) 描述凝聚集合 $\underline{D}$：对于 profinite set $S$，$\underline{D}(S)$ 是什么？

(b) 证明 $\underline{D}$ 满足层条件。

**问题 1.2.2** (凝聚映射)

设 $X, Y$ 是凝聚集合。一个**凝聚映射** $f: X \to Y$ 是自然变换。

(a) 如果 $X = \underline{S}, Y = \underline{T}$ 来自拓扑空间，证明：
$$\text{Hom}_{\text{Cond}}(\underline{S}, \underline{T}) \cong C(S, T)$$

(b) 给出一个不是 $\underline{f}$ 形式的凝聚映射的例子（提示：考虑非紧生成空间）。

---

### 练习 1.3：凝聚阿贝尔群

**问题 1.3.1** (核与余核)

设 $f: A \to B$ 是凝聚阿贝尔群的态射。

(a) 描述 $\ker(f)$ 作为凝聚集合：对于 profinite set $S$，$(\ker f)(S)$ 是什么？

(b) 类似地描述 $\text{coker}(f)$。

(c) 验证：$\ker(f)(S) = \ker(f_S: A(S) \to B(S))$，并证明这定义了一个凝聚集合。

**问题 1.3.2** (正合序列)

在凝聚阿贝尔群范畴中，序列
$$0 \to A \to B \to C \to 0$$
是正合的当且仅当对于每个 profinite set $S$，序列
$$0 \to A(S) \to B(S) \to C(S) \to 0$$
是群的正合序列。

证明这一论断。

---

## 第二部分：中级练习

### 练习 2.1：与泛函分析的联系

**问题 2.1.1** ($\ell^p$空间的液体化)

设 $\ell^p = \ell^p(\mathbb{N})$，$1 \leq p < \infty$。

(a) 描述 $\mathcal{L}(\ell^p)(S)$ 对于 profinite set $S$。

(b) 证明：$\mathcal{L}(\ell^p)$ 是液体向量空间。

(c) 计算 $\mathcal{L}(\ell^p) \otimes^{\text{liq}} \mathcal{L}(\ell^q)$（对于适当的 $p, q$）。

**问题 2.1.2** (连续函数空间)

设 $K$ 是紧Hausdorff空间，$C(K)$ 是连续函数空间。

(a) 证明 $C(K)$ 有自然的液体向量空间结构。

(b) 对于 profinite set $S$，描述 $(\mathcal{L}(C(K)))(S)$。

(c) 如果 $K = [0, 1]$，与 $C([0, 1])$ 的经典泛函分析性质比较。

---

### 练习 2.2：层条件的深入理解

**问题 2.2.1** (Čech上同调)

设 $\mathcal{F}$ 是凝聚阿贝尔群，$S$ 是 profinite set，$\mathfrak{U} = \{U_i \to S\}$ 是有限覆盖。

定义Čech复形 $\check{C}^\bullet(\mathfrak{U}, \mathcal{F})$，并证明：
$$\check{H}^0(\mathfrak{U}, \mathcal{F}) = \mathcal{F}(S)$$

**问题 2.2.2** (下降数据)

设 $f: T \to S$ 是 profinite sets 的满射。一个**下降数据**是...

描述在凝聚集合范畴中，下降有效性的条件。

---

### 练习 2.3：张量积的计算

**问题 2.3.1** (有限维空间)

设 $V = \mathbb{R}^n, W = \mathbb{R}^m$。

(a) 计算 $V \otimes^{\text{liq}} W$。

(b) 与经典张量积 $V \otimes W \cong \mathbb{R}^{nm}$ 比较。

**问题 2.3.2** (序列空间)

计算（在适当的意义下）：
$$c_0 \otimes^{\text{liq}} \ell^1$$
其中 $c_0$ 是收敛到0的序列空间。

---

## 第三部分：高级练习

### 练习 3.1：液体张量积的正合性

**问题 3.1.1** (正合序列的保持)

设 $0 \to V_1 \to V_2 \to V_3 \to 0$ 是液体向量空间的短正合序列。

(a) 证明：对于任何液体向量空间 $W$，序列
$$0 \to V_1 \otimes^{\text{liq}} W \to V_2 \otimes^{\text{liq}} W \to V_3 \otimes^{\text{liq}} W \to 0$$
是正合的。

(b) 讨论为什么这在经典局部凸空间理论中不成立。

**问题 3.1.2** (Scholze的主要不等式)

考虑以下构造（来自 Liquid Tensor Experiment）：

设 $S$ 是 profinite set，$V$ 是Banach空间，$p \in (0, 1)$。

定义空间 $\mathcal{M}_p(S, V)$ 为 $p$-可求和测度空间。

证明存在常数 $C > 0$ 使得：
$$\|\cdot\|_{\mathcal{M}_p(S, \ell^p(V))} \leq C \|\cdot\|_{\mathcal{M}_{p'}(S) \otimes \ell^p(V)}$$

这是液体张量实验中的核心不等式。

---

### 练习 3.2：导出范畴

**问题 3.2.1** (Ext群)

设 $A, B$ 是凝聚阿贝尔群。

(a) 定义 $\text{Ext}^i_{\text{Cond(Ab)}}(A, B)$。

(b) 对于 $A = \underline{\mathbb{Z}}, B = \underline{\mathbb{Z}}$，计算 $\text{Ext}^1$。

(c) 与经典Ext群 $\text{Ext}^i_{\text{Ab}}(A(*), B(*))$ 比较。

**问题 3.2.2** (凝聚上同调计算)

设 $X = \underline{[0, 1]}$（单位区间的凝聚化），$\mathcal{F} = \underline{\mathbb{Z}}$。

计算 $H^i_{\text{cond}}(X, \mathcal{F})$ 并与经典奇异上同调比较。

---

### 练习 3.3：与代数几何的联系

**问题 3.3.1** (凝聚结构层)

设 $X$ 是复解析空间。定义凝聚结构层 $\mathcal{O}_X^{\text{cond}}$。

(a) 对于 $X = \mathbb{C}$，描述 $\mathcal{O}_\mathbb{C}^{\text{cond}}(S)$。

(b) 证明：凝聚全纯函数与经典全纯函数有正确的对应关系。

**问题 3.3.2** (GAGA的凝聚版本)

设 $X$ 是复射影簇。讨论凝聚GAGA原理：
$$\text{Coh}(X^{\text{an}}) \cong \text{Coh}(X)$$
在凝聚框架下如何表述。

---

## 第四部分：研究级问题

### 问题 4.1：开放问题探索

**问题 4.1.1** (紧生成假设)

经典凝聚理论假设空间是紧生成的。

(a) 研究：哪些非紧生成空间可以被凝聚化？

(b) 对于 $X = \mathbb{R}^\mathbb{N}$（赋乘积拓扑），研究其凝聚化行为。

**问题 4.1.2** (凝聚代数K-理论)

设 $X$ 是凝聚空间。

(a) 如何定义 $K_0^{\text{cond}}(X)$？

(b) 与经典拓扑K-理论 $K^0(X(*))$ 的关系是什么？

(c) 研究高阶凝聚K-群的存在性。

---

### 问题 4.2：形式化项目

**问题 4.2.1** (Lean4练习)

(a) 在Mathlib4中，找到凝聚集合的定义并理解其结构。

(b) 尝试证明：对于 profinite sets $S, T$，有：
$$\underline{S \times T} \cong \underline{S} \times \underline{T}$$

(c) 研究液体张量积在Mathlib4中的实现。

**问题 4.2.2** (新形式化目标)

提出一个可以在Lean4中形式化的凝聚数学定理，并制定实施计划。

---

### 问题 4.3：与其他领域的交叉

**问题 4.3.1** (与∞-范畴的联系)

研究凝聚集合的范畴与∞-topos理论的关系。

(a) Cond(Set) 是一个∞-topos吗？

(b) 如果是，对应的景是什么？

**问题 4.3.2** (在数论中的应用)

研究凝聚方法在以下问题中的应用潜力：
(a) Iwasawa理论
(b) $p$-adic Hodge理论
(c) 局部Langlands对应

---

## 解答提示与参考文献

### 第一部分提示

**练习 1.1.1**: 使用Stone空间的对偶性定理。

**练习 1.2.1**: 对于离散空间 $D$，$\underline{D}(S) = D^{\pi_0(S)}$。

### 第二部分提示

**练习 2.1.1**: 使用液体张量积的定义和 $\ell^p$ 空间的插值理论。

**练习 2.3.2**: 答案涉及 $c_0 \hat{\otimes}_\pi \ell^1$ 的经典计算。

### 第三部分提示

**练习 3.1.1**: 参考 Liquid Tensor Experiment 的证明策略。

**练习 3.2.1**: 使用凝聚阿贝尔群有足够内射对象的性质。

### 推荐参考文献

1. **基础**: Scholze, "Lectures on Condensed Mathematics", Lectures 1-3
2. **液体**: Clausen-Scholze, "Lectures on Analytic Geometry", Lectures 1-5
3. **形式化**: Commelin et al., Liquid Tensor Experiment 文档
4. **练习**: 基于上述文献和作者整理

---

## 学习路径建议

```
基础阶段
├── 完成练习 1.1 - 1.3
├── 阅读 Scholze 讲义第1-3讲
└── 理解 profinite sets 和层条件

进阶阶段
├── 完成练习 2.1 - 2.3
├── 阅读 Clausen-Scholze 解析几何讲义
└── 尝试理解液体张量积的构造

高级阶段
├── 完成练习 3.1 - 3.3
├── 研究 Liquid Tensor Experiment
└── 探索与其他领域的联系

研究阶段
├── 尝试问题 4.1 - 4.3
├── 参与形式化项目
└── 探索开放问题
```

---

*最后更新: 2026年4月 | FormalMath项目*
