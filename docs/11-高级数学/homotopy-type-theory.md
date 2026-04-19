---
title: 同伦类型论深度版 / Homotopy Type Theory - In Depth
msc_primary: 00

  - 00A99
  - 18G55
  - 00A99
processed_at: '2026-04-05'
---
# 同伦类型论深度版 / Homotopy Type Theory - In Depth

## 目录

- [同伦类型论深度版 / Homotopy Type Theory - In Depth](#同伦类型论深度版--homotopy-type-theory---in-depth)
  - [目录](#目录)
  - [1. 深入概念 / Deep Concepts](#1-深入概念--deep-concepts)
    - [1.1 类型作为空间 / Types as Spaces](#11-类型作为空间--types-as-spaces)
    - [1.2 恒等类型的几何解释 / Geometric Interpretation of Identity Types](#12-恒等类型的几何解释--geometric-interpretation-of-identity-types)
    - [1.3 高阶归纳类型 / Higher Inductive Types](#13-高阶归纳类型--higher-inductive-types)
    - [1.4 单值公理的深层含义 / Deep Meaning of Univalence](#14-单值公理的深层含义--deep-meaning-of-univalence)
  - [2. 现代观点 / Modern Perspectives](#2-现代观点--modern-perspectives)
    - [2.1 ∞-范畴视角 / ∞-Category Perspective](#21--范畴视角---category-perspective)
    - [2.2 合成同伦论 / Synthetic Homotopy Theory](#22-合成同伦论--synthetic-homotopy-theory)
    - [2.3 立方类型论 / Cubical Type Theory](#23-立方类型论--cubical-type-theory)
    - [2.4 模态同伦类型论 / Modal Homotopy Type Theory](#24-模态同伦类型论--modal-homotopy-type-theory)
  - [3. 研究前沿 / Research Frontiers](#3-研究前沿--research-frontiers)
    - [3.1 计算化同伦类型论 / Computational HoTT](#31-计算化同伦类型论--computational-hott)
    - [3.2 凝聚类型论 / Cohesive Type Theory](#32-凝聚类型论--cohesive-type-theory)
    - [3.3 定向类型论 / Directed Type Theory](#33-定向类型论--directed-type-theory)
    - [3.4 高阶归纳-归纳类型 / Higher Inductive-Inductive Types](#34-高阶归纳-归纳类型--higher-inductive-inductive-types)
  - [4. 应用前沿 / Frontier Applications](#4-应用前沿--frontier-applications)
    - [4.1 形式化数学 / Formalized Mathematics](#41-形式化数学--formalized-mathematics)
    - [4.2 计算机辅助证明 / Computer-Assisted Proofs](#42-计算机辅助证明--computer-assisted-proofs)
    - [4.3 量子同伦类型论 / Quantum Homotopy Type Theory](#43-量子同伦类型论--quantum-homotopy-type-theory)
  - [5. 参考文献 / References](#5-参考文献--references)
    - [5.1 经典文献 / Classical Works](#51-经典文献--classical-works)
    - [5.2 现代专著 / Modern Monographs](#52-现代专著--modern-monographs)
    - [5.3 前沿论文 / Frontier Papers](#53-前沿论文--frontier-papers)
    - [5.4 在线资源 / Online Resources](#54-在线资源--online-resources)

---

## 1. 深入概念 / Deep Concepts

### 1.1 类型作为空间 / Types as Spaces

同伦类型论（Homotopy Type Theory, HoTT）的核心理念是将类型论中的类型解释为拓扑空间（或更准确地说是∞-群胚）。这一对应关系可以概括为：

| 类型论概念 | 拓扑/几何解释 |
|-----------|--------------|
| 类型 $A$ | 空间 $|A|$ |
| 项 $a : A$ | 点 $a
| |A|$ |
| 函数 $f : A   o B$ | 连续映射 $|f| : |A|   o |B|$ |
| 恒等类型 $  ext{Id}_A(a,b)$ | 路径空间 $  ext{Path}_{|A|}(a,b)$ |
| 路径 $p : a =_A b$ | 从 $a$ 到 $b$ 的道路 |
| 路径之间的相等 $q : p =_{a=b} r$ | 路径同伦 |

**命题即类型的深化理解**:

在Martin-Löf类型论中，命题被视为类型。在HoTT中，这一对应被深化为：

- 命题对应于具有至多一个元素的空间（即 $(-1)$-型）
- 结构对应于具有更丰富同伦信息的空间

```
命题层级（h-levels）:
- h-level 0: 可缩类型（单点空间）
- h-level 1: 命题（至多一个点）
- h-level 2: 集合（无高阶路径）
- h-level n+1: n-群胚
```

**路径归纳原理的拓扑意义**:

路径归纳（path induction）表明：要证明关于任意路径 $p : a = b$ 的命题，只需证明关于自反路径 $  ext{refl}_a : a = a$ 的情况。这在拓扑上对应于：路径空间是可缩的（当固定起点时）。

### 1.2 恒等类型的几何解释 / Geometric Interpretation of Identity Types

恒等类型 $  ext{Id}_A(a,b)$ 是同伦类型论中最核心的概念。其几何解释揭示了类型论与拓扑学之间的深刻联系。

**高阶路径结构**:

对于类型 $A$ 中的元素 $a, b$，恒等类型 $a =_A b$ 本身又是一个类型，因此可以有：

- $p, q : a =_A b$（两条路径）
- $  ext{Id}_{a=_A b}(p, q)$（路径之间的路径，即同伦）

这形成了自然的∞-群胚结构：

$$
A
ightsquigarrow   ext{Id}_A
ightsquigarrow   ext{Id}_{  ext{Id}_A}
ightsquigarrow   ext{Id}_{  ext{Id}_{  ext{Id}_A}}
ightsquigarrow \
cdots
$$

**圆圈的构造**:

高阶归纳类型允许我们通过生成元直接定义具有非平凡同伦类型的空间。例如，圆 $S^1$ 可以定义为：

```
Inductive Circle : Type where
  | base : Circle
  | loop : base = base
```

这对应于拓扑学中的标准构造：圆有一个基点和一个非平凡环路。重要的是，$  ext{loop}$ 不是自反路径，这给出了圆的基本群 $
\pi_1(S^1) \cong \mathbb{Z}$。

**路径运算**:

- **逆路径**: $p^{-1} : b = a$，几何上表示反向行走
- **路径复合**: $p \cdot q : a = c$，几何上表示路径的串联
- **常值路径**: $\text{refl}_a : a = a$，几何上表示静止不动

这些运算满足群胚律（groupoid laws），但在HoTT中它们只成立到同伦等价，而非严格相等。

### 1.3 高阶归纳类型 / Higher Inductive Types

高阶归纳类型（Higher Inductive Types, HITs）是HoTT中最强大的特性之一，它允许在定义类型时同时指定点和路径（以及更高维的路径）的生成元。

**基本形式**:

HIT的一般形式包括：

- **点构造子**: $c : A$ — 生成类型的点
- **路径构造子**: $p : a =_A b$ — 生成类型中的路径
- **高阶路径构造子**: $h : p =_{a=b} q$ — 生成路径之间的路径

**重要例子**:

1. **区间 $I$**:

   ```
   Inductive Interval : Type where
     | zero : Interval
     | one  : Interval
     | seg  : zero = one
   ```

2. **球面 $S^n$**:

   ```
   Inductive Sphere (n : ℕ) : Type where
     | base : Sphere n
     | surf : refl_base = refl_base  [当 n > 1]
   ```

3. **推出（Pushout）**:
   给定 $f : A \to B$ 和 $g : A \to C$，推出是商空间 $B \sqcup_A C$。

**HITs的表达能力**:

HITs使得我们可以在类型论中构造：

- 商类型（ Quotient types）
- 像（Images of functions）
- 局部化（Localization）
- 谱序列的构造

### 1.4 单值公理的深层含义 / Deep Meaning of Univalence

单值公理（Univalence Axiom）由Vladimir Voevodsky提出，是HoTT的标志性公理。

**形式表述**:

对于类型 $A, B : \mathcal{U}$，单值公理断言：

$$(A \simeq B) \simeq (A =_\mathcal{U} B)$$

其中 $A \simeq B$ 表示类型等价（具有互逆的函数），$A =_\mathcal{U} B$ 表示类型在宇宙 $\mathcal{U}$ 中的恒等类型。

**深层含义**:

1. **结构即性质**: 单值公理表明，两个类型之间的等价结构可以转化为它们之间的恒等（路径）。这实现了数学中的"结构即性质"（Structure Identity Principle）。

2. **同构即相等**: 在集合层面，单值公理意味着同构的结构在逻辑上是不可区分的。这在数学实践中是直观的，但在传统形式系统中难以表达。

3. **数学的自然形式化**: 单值公理使得数学形式化更接近数学家的实际思维，避免了大量的"传输"（transport）引理。

**与函数外延性的关系**:

单值公理蕴含函数外延性：如果两个函数在所有输入上相等，则它们作为函数是相等的。

$$
(\forall x, f(x) = g(x)) \to (f = g)
$$

**单值数学**:

基于单值公理的数学体系被称为"单值基础"（Univalent Foundations），它提供了：

- 更自然的数学形式化
- 更强的抽象能力
- 与∞-拓扑理论的深刻联系

---

## 2. 现代观点 / Modern Perspectives

### 2.1 ∞-范畴视角 / ∞-Category Perspective

同伦类型论与∞-范畴理论之间存在深刻的对应关系。

**∞-群胚假设**:

Grothendieck的"∞-群胚假设"（Homotopy Hypothesis）指出：

- 拓扑空间的同伦类型与∞-群胚是等价的
- 同伦类型论中的类型自然地承载∞-群胚结构

在同伦类型论中，这一假设被"内置"：每个类型 $A$ 自动具有∞-群胚结构，其中：

- 对象是 $A$ 的元素
- 1-态射是恒等类型的元素
- n-态射是第n层恒等类型的元素

**语义模型**:

HoTT的标准模型在∞-Topos中：

- 类型对应于空间（ fibrant objects）
- 函数对应于纤维化之间的映射
- 恒等类型对应于路径空间纤维化

这种对应由Voevodsky的" simplicial set model" 和后续的"cubical set model"实现。

**与导出范畴的联系**:

同伦类型论与导出代数几何和导出范畴理论有密切联系：

- 导出范畴中的复形可以表示为高阶类型
- 拟同构可以对应于类型等价
- 三角结构对应于（高阶）纤维序列

### 2.2 合成同伦论 / Synthetic Homotopy Theory

合成同伦论是在HoTT框架内"从头开始"构建同伦论的方法。

**与经典同伦论的对比**:

| 方面 | 经典同伦论 | 合成同伦论 |
|-----|----------|-----------|
| 基础 | 集合论 + 拓扑学 | 类型论公理 |
| 空间 | 点集拓扑空间 | 原始概念（类型） |
| 路径 | 连续映射 $[0,1] \to X$ | 恒等类型的元素 |
| 同伦 | 连续变形 | 高阶恒等 |
| 同伦群 | 拓扑不变量的计算 | 类型论构造的证明 |

**合成同伦论的优势**:

1. **构造性**: 所有证明都是构造性的，可以提取计算内容
2. **机器可检验**: 证明可以在计算机上验证
3. **抽象性**: 不依赖于具体的拓扑模型

**重要成果**:

在同伦类型论中已经合成地证明了：

- $\pi_1(S^1) \cong \mathbb{Z}$（圆的基本群）
- $\pi_k(S^n) = 0$ for $k < n$（球的低维同伦群）
- Freudenthal suspension theorem
- Blakers-Massey theorem

### 2.3 立方类型论 / Cubical Type Theory

立方类型论（Cubical Type Theory）是HoTT的一种变体，它提供了计算意义上的单值公理。

**立方视角**:

在立方类型论中：

- 路径不是原始概念，而是"区间变量"的函数
- $p : a =_A b$ 表示为 $p(i) : A$ 其中 $i$ 是区间变量，$p(0) = a$，$p(1) = b$
- 高维立方体自然地对应于高阶路径

**计算规则**:

立方类型论的主要优势是：

- 单值公理具有计算内容
- 路径替代（path substitution）可以计算
- 类型检查是可判定的

**立方模型**:

Coquand等人发展的立方集合模型提供了：

- 严格的单值公理解释
- 良好的计算性质
- 与经典同伦论的兼容性

### 2.4 模态同伦类型论 / Modal Homotopy Type Theory

模态同伦类型论扩展了HoTT，引入了模态算子，用于表达各种数学和物理概念。

**动机**:

在数学和物理中，经常需要谈论：

- 必然性和可能性（模态逻辑）
- 上同调运算（如离散化、连续化）
- 相干性和一致性条件

**凝聚类型论**:

Schreiber-Shulman的凝聚类型论（Cohesive Homotopy Type Theory）引入了三种模态：

- $\int$（形状/离散化）: 提取类型的"纯形状"
- $\flat$（平坦）: 将离散类型嵌入连续类型
- $\sharp$（尖锐）: 从类型提取其"点状"信息

**形式化表述**:

这些模态形成伴随三元组：

$$\int \dashv \flat \dashv \sharp$$

满足：

- $\int$ 保持有限极限
- $\flat$ 和 $\sharp$ 是幂等模态
- 存在各种一致性公理

**应用**:

模态HoTT可以形式化：

- 微分几何（流形、切丛）
- 上同调理论（de Rham上同调）
- 物理中的规范理论

---

## 3. 研究前沿 / Research Frontiers

### 3.1 计算化同伦类型论 / Computational HoTT

计算化同伦类型论致力于使HoTT具有实际可计算性。

**挑战**:

经典HoTT中的单值公理是"公理"而非"构造"，这意味着：

- 使用单值公理的证明不携带计算内容
- 无法提取程序或进行计算

**解决方案**:

1. **立方类型论**: 提供计算意义的单值公理
2. **笛卡尔立方类型论**: Angiuli等人的发展
3. **注记语义**: 使用注记（annotation）追踪证明计算内容

**实现系统**:

- **Cubical Agda**: 完全立方类型论的实现
- **Cubical Type Theory in Coq**: Coq中的立方类型论扩展
- **redtt**: 实验性的立方类型论证明助手

**当前研究方向**:

- 优化立方类型论的性能
- 开发更好的高维自动推理技术
- 建立更高效的语义模型

### 3.2 凝聚类型论 / Cohesive Type Theory

凝聚类型论是HoTT的几何扩展，旨在形式化微分几何和物理。

**核心思想**:

凝聚拓扑（Cohesive Topos）是既包含"连续"又包含"离散"结构的范畴。在类型论中，这对应于引入表达"几何"和"代数"不同层面的模态。

**具体构造**:

凝聚类型论通常包含：

- **形状模态 $\int$**: 提取类型的同伦类型（去掉几何信息）
- **离散模态 $\flat$**: 将离散空间嵌入
- **收缩模态 $\sharp$**: 将空间收缩为其点集

**微分凝聚类型论**:

进一步扩展包括微分结构：

- **无穷小形状 $\int_{\text{inf}}$**: 提取无穷小信息
- **de Rham模态**: 构造de Rham复形
- **切∞-丛**: 形式化切空间

**与物理的联系**:

凝聚类型论可以形式化：

- 规范理论（gauge theory）
- 弦论中的背景场
- 拓扑量子场论

### 3.3 定向类型论 / Directed Type Theory

定向类型论（Directed Type Theory）旨在形式化有向（非对称）结构，如范畴、有向空间等。

**动机**:

经典HoTT处理的是∞-群胚（所有箭头可逆），但数学中许多重要结构是"有向"的：

- 范畴（只有可逆态射才是同构）
- 偏序集
- 有向拓扑空间

**挑战**:

将HoTT推广到有向情况面临困难：

- 路径复合不再满足对称性
- 恒等类型的规则需要重新设计
- 语义模型更加复杂

**研究方向**:

1. **2-层类型论**: Riehl-Shulman的发展
2. **有向立方类型论**: 使用有向区间
3. **Segal类型论**: 基于Segal条件

**应用前景**:

- 形式化∞-范畴论
- 形式化综合微分几何
- 形式化有向代数拓扑

### 3.4 高阶归纳-归纳类型 / Higher Inductive-Inductive Types

高阶归纳-归纳类型（Higher Inductive-Inductive Types, HIITs）允许同时定义相互递归的高阶归纳类型。

**基本思想**:

在HITs中，我们可以定义具有点、路径和高维路径的类型。在HIITs中，可以同时定义多个相互依赖的此类类型。

**例子：类型论语法**:

形式化类型论自身的语法时，需要同时定义：

- 类型上下文（contexts）
- 类型（types）
- 项（terms）

这些定义是相互递归的：

- 上下文由类型组成
- 类型在上下文中定义
- 项属于某个类型

**重要性**:

HIITs对于形式化以下内容是必要的：

- 类型论自身的元理论
- 代数理论（algebraic theories）
- 归纳-归纳定义（如序数、Conway游戏）

**当前研究**:

- 建立HIITs的一般理论
- 证明HIITs的消去原理
- 在证明助手中实现HIITs

---

## 4. 应用前沿 / Frontier Applications

### 4.1 形式化数学 / Formalized Mathematics

同伦类型论为形式化数学提供了新的范式。

**形式化项目**:

1. **Lean中的HoTT**: 使用Lean证明助手进行同伦类型论研究
2. **UniMath**: 基于Coq的单值数学库
3. **HoTT Library**: 另一个基于Coq的HoTT库
4. **cubicaltt**: 实验性的立方类型论实现

**形式化成果**:

在同伦类型论中已经形式化了：

- 基础同伦论（基本群、高阶同伦群）
- 同调代数（链复形、导出函子）
- 代数拓扑（谱序列、纤维化）
- 范畴论（伴随、极限、Monad）

**优势**:

- **数学的正确性**: 机器验证保证无错误
- **重构数学基础**: 提供新的数学基础视角
- **发现新结构**: 计算机辅助发现新的数学联系

### 4.2 计算机辅助证明 / Computer-Assisted Proofs

HoTT为计算机辅助证明提供了新的工具和方法。

**证明策略**:

在HoTT框架中：

- 同伦等价可以替代严格的等式
- 高阶结构可以表达复杂的证明依赖关系
- 合成方法可以简化证明构造

**自动化技术**:

- **高维自动推理**: 自动处理路径和高阶路径
- **同伦等价自动发现**: 自动寻找类型之间的等价
- **运输自动化**: 自动处理命题在等价下的传输

**具体应用**:

- **代数拓扑证明**: 如Blakers-Massey定理的形式化
- **同伦群计算**: 自动化同伦群的某些计算
- **范畴论证明**: 自动化伴随函子的构造

### 4.3 量子同伦类型论 / Quantum Homotopy Type Theory

量子同伦类型论是将量子力学概念融入HoTT的新兴领域。

**基本思想**:

探索类型论与量子力学的对应：

- 类型可以视为量子系统的"空间"
- 路径可以表示量子演化
- 高阶结构可以表达量子纠缠

**研究方向**:

1. **线性同伦类型论**: 结合线性逻辑和HoTT
2. **量子计算的形式化**: 使用HoTT形式化量子算法
3. **拓扑量子场论**: 在HoTT中形式化TQFT

**潜在应用**:

- 量子编程语言的语义基础
- 量子纠错码的形式化验证
- 拓扑量子计算的理论基础

---

## 5. 参考文献 / References

### 5.1 经典文献 / Classical Works

1. **The HoTT Book** (2013)
   - *Homotopy Type Theory: Univalent Foundations of Mathematics*
   - The Univalent Foundations Program, Institute for Advanced Study
   - 同伦类型论的奠基性著作
   - 在线版本: https://homotopytypetheory.org/book/[需更新[需更新]]

2. **Voevodsky, V.** (2006-2014)
   - 系列关于单值基础的工作
   - 包括Notes on Type Systems, Univalent Foundations等
   - 奠定了单值公理的理论基础

3. **Awodey, S.** (2012)
   - *Type Theory and Homotopy*
   - 对HoTT概念的清晰介绍
   - 在哲学家和逻辑学家中有广泛影响

### 5.2 现代专著 / Modern Monographs

1. **Riehl, E.** (2014)
   - *Categorical Homotopy Theory*
   - Cambridge University Press
   - ∞-范畴和模型范畴的权威参考

2. **Lurie, J.** (2009)
   - *Higher Topos Theory*
   - Princeton University Press
   - ∞-Topos理论的里程碑著作
   - 提供了HoTT的语义基础

3. **UFP (Univalent Foundations Program)** (2020)
   - *Symmetry Book* (进行中)
   - 使用HoTT重新表述群论和对称性

4. **Coquand, T., Huber, S., & Mörtberg, A.** (2018)
   - *On Higher Inductive Types in Cubical Type Theory*
   - LICS 2018
   - 立方类型论中高阶归纳类型的系统研究

### 5.3 前沿论文 / Frontier Papers

1. **Angiuli, C., Cavallo, E., Mörtberg, A., & Zeuner, M.** (2021)
   - *Internalizing Representation Independence with Univalence*
   - POPL 2021
   - 单值公理在软件验证中的应用

2. **Riehl, E. & Shulman, M.** (2017)
   - *A Type Theory for Synthetic ∞-Categories*
   - 高阶范畴论的类型论基础

3. **Schreiber, U. & Shulman, M.** (2014)
    - *Quantum Gauge Field Theory in Cohesive Homotopy Type Theory*
    - QPL 2014
    - 凝聚类型论在物理中的应用

4. **Cohen, C., Coquand, T., Huber, S., & Mörtberg, A.** (2018)
    - *Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom*
    - TYPES 2015
    - 立方类型论的奠基论文

5. **Licata, D. & Finster, E.** (2014)
    - *Eilenberg-MacLane Spaces in Homotopy Type Theory*
    - LICS 2014
    - 在HoTT中构造Eilenberg-MacLane空间

6. **Sozeau, M. & Tabareau, N.** (2019)
    - *The Marriage of Univalence and Parametricity*
    - Journal of Functional Programming
    - 单值性与参数多态性的结合

### 5.4 在线资源 / Online Resources

1. **Homotopy Type Theory Website**
    - https://homotopytypetheory.org/[需更新[需更新]]
    - 社区主页，包含博客、论文和讨论

2. **nLab**
    - https://ncatlab.org/nlab/show/homotopy+type+theory
    - 数学物理wiki，包含大量HoTT相关条目

3. **Lean Community**
    - https://leanprover-community.github.io/[需更新[需更新]]
    - Lean证明助手社区，包含HoTT相关内容

4. **Cubical Agda Documentation**
    - https://agda.readthedocs.io/en/v2.6.1/language/cubical.html[需更新[需更新]]
    - 立方类型论实现的官方文档

5. **UniMath Repository**
    - https://github.com/UniMath/UniMath
    - 基于Coq的单值数学形式化库

6. **HoTT/HoTT-Agda Repository**
    - https://github.com/HoTT/HoTT-Agda
    - Agda中的HoTT形式化

---

**文档信息**:

- **创建日期**: 2026年4月4日
- **更新状态**: 首次发布
- **目标读者**: 数学专业研究生、研究人员、类型论学者
- **前置知识**: 基础同伦论、类型论基础、范畴论入门

---

**相关链接**:

- [15-同伦类型论](./15-同伦类型论.md) - 基础版本
- [06-无穷范畴理论](./06-无穷范畴理论.md) - 相关理论
- [07-高阶同伦论](./07-高阶同伦论.md) - 同伦论深入
