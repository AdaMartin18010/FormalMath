---
title: 无穷范畴深度版 / Infinity-Categories - In Depth
msc_primary: 18N60
msc_secondary:
- 00A99
- 18G55
- 00A99
processed_at: '2026-04-05'
---
# 无穷范畴深度版 / Infinity-Categories - In Depth

## 目录

- 无穷范畴深度版 / Infinity-Categories - In Depth
  - [目录](#目录)
  - [1. 深入概念 / Deep Concepts](#1-深入概念-deep-concepts)
    - [1.1 从范畴到无穷范畴 / From Categories to Infinity-Categories](#11-从范畴到无穷范畴-from-categories-to-infinity-categories)
    - [1.2 拟范畴与无穷范畴 / Quasicategories and Infinity-Categories](#12-拟范畴与无穷范畴-quasicategories-and-infinity-categories)
    - [1.3 高维结构与单纯集 / Higher Structures and Simplicial Sets](#13-高维结构与单纯集-higher-structures-and-simplicial-sets)
    - [1.4 同伦相干性与复合 / Homotopy Coherence and Composition](#14-同伦相干性与复合-homotopy-coherence-and-composition)
  - [2. 现代观点 / Modern Perspectives](#2-现代观点-modern-perspectives)
    - [2.1 模型独立方法 / Model-Independent Approach](#21-模型独立方法-model-independent-approach)
    - [2.2 无穷Topos理论 / Infinity-Topos Theory](#22-无穷topos理论-infinity-topos-theory)
    - [2.3 稳定无穷范畴 / Stable Infinity-Categories](#23-稳定无穷范畴-stable-infinity-categories)
    - [2.4 导出与谱代数几何 / Derived and Spectral Algebraic Geometry](#24-导出与谱代数几何-derived-and-spectral-algebraic-geometry)
  - [3. 研究前沿 / Research Frontiers](#3-研究前沿-research-frontiers)
    - [3.1 无穷范畴的计算机形式化 / Formalization of Infinity-Categories](#31-无穷范畴的计算机形式化-formalization-of-infinity-categories)
    - [3.2 凝聚无穷Topos / Cohesive Infinity-Toposes](#32-凝聚无穷topos-cohesive-infinity-toposes)
    - [3.3 高阶代数结构 / Higher Algebraic Structures](#33-高阶代数结构-higher-algebraic-structures)
    - [3.4 几何表示论 / Geometric Representation Theory](#34-几何表示论-geometric-representation-theory)
  - [4. 应用前沿 / Frontier Applications](#4-应用前沿-frontier-applications)
    - [4.1 代数K-理论与拓扑循环同调 / Algebraic K-Theory and TC](#41-代数k-理论与拓扑循环同调-algebraic-k-theory-and-tc)
    - [4.2 椭圆上同调与拓扑模形式 / Elliptic Cohomology and TMFs](#42-椭圆上同调与拓扑模形式-elliptic-cohomology-and-tmfs)
    - [4.3 朗兰兹纲领的几何化 / Geometrization of Langlands](#43-朗兰兹纲领的几何化-geometrization-of-langlands)
  - [5. 参考文献 / References](#5-参考文献-references)
    - [5.1 奠基性著作 / Foundational Works](#51-奠基性著作-foundational-works)
    - [5.2 现代专著 / Modern Monographs](#52-现代专著-modern-monographs)
    - [5.3 前沿研究论文 / Frontier Research Papers](#53-前沿研究论文-frontier-research-papers)
    - [5.4 在线资源与工具 / Online Resources and Tools](#54-在线资源与工具-online-resources-and-tools)

---

## 1. 深入概念 / Deep Concepts

### 1.1 从范畴到无穷范畴 / From Categories to Infinity-Categories

无穷范畴（Infinity-Categories）是范畴论在高维同伦背景下的自然推广。

**动机与需求**:

经典范畴论在许多数学领域遇到了限制：
- **同伦论**: 连续映射的同伦类构成的范畴丢失了太多信息
- **导出范畴**: 复形之间的链同伦需要更精细的结构
- **代数拓扑**: 谱和无穷回路空间需要高阶结构

**核心思想**:

无穷范畴中的态射不仅有复合，还有"高阶态射"连接不同的复合方式，这些高阶态射本身又可以被复合，以此类推，形成无穷层次的相互关联。

**从范畴到无穷范畴的演变**:

```
范畴论 → 2-范畴（自然变换作为2-态射）
       → n-范畴（有限高阶）
       → 无穷范畴（无限高阶，非平凡高阶态射）
       → (无穷,1)-范畴（高阶态射可逆）
```

**(无穷,1)-范畴**:

目前理论和应用最成熟的是(无穷,1)-范畴，其中：
- 对于 k > 1，所有 k-态射都是可逆的（等价于同伦）
- 1-态射可以不可逆（真正的"映射"）
- 这恰好捕捉了拓扑空间和同伦类的结构

### 1.2 拟范畴与无穷范畴 / Quasicategories and Infinity-Categories

拟范畴（Quasicategories）是Joyal和Lurie发展的(无穷,1)-范畴的主要模型。

**单纯集视角**:

拟范畴是满足特定条件的单纯集 X：
- **内Horn填充条件**: 对于 0 < i < n，任何内Horn Λ^n_i → X 都可以扩展到 n-单形 Δ^n → X

这对应于：在拟范畴中，虽然复合不一定唯一，但总是存在的，且不同复合方式之间由可逆的高阶态射连接。

**直观理解**:

| 单纯集结构 | 无穷范畴解释 |
|-----------|-----------|
| 0-单形 | 对象 |
| 1-单形 | 1-态射（箭头） |
| 2-单形 | 复合关系（h ≃ g ∘ f） |
| n-单形 | n个可复合1-态射的"记录" |

**同伦范畴**:

每个拟范畴 C 都有一个关联的普通范畴 hC（称为同伦范畴）：
- 对象是 C 的对象
- 态射是1-态射的同伦类

这提供了从无穷范畴回到普通范畴的桥梁。

**与其他模型的比较**:

除了拟范畴，还有多种等价的(无穷,1)-范畴模型：
- **单纯范畴**（Simplicial categories）: Bergner模型结构
- **完备Segal空间**（Complete Segal spaces）: Rezk
- **相对范畴**（Relative categories）: Barwick-Kan
- **拓扑范畴**（Topologically enriched categories）

### 1.3 高维结构与单纯集 / Higher Structures and Simplicial Sets

理解无穷范畴需要熟悉单纯集（simplicial sets）这一基本工具。

**单纯集基础**:

单纯集是单纯范畴 Δ 到集合范畴的反变函子 X: Δ^op → Set。

- **面映射** d_i: X_n → X_{n-1}: 删除第 i 个顶点
- **退化映射** s_i: X_n → X_{n+1}: 重复第 i 个顶点

**单纯集的几何实现**:

每个单纯集 |X| 可以几何实现为拓扑空间，这是联系组合与几何的桥梁。

**Nerve构造**:

从范畴 C 可以构造其Nerve N(C)，这是一个拟范畴（实际上是"普通"范畴的嵌入）：
- N(C)_n = Fun([n], C)
- [n] 是有 n+1 个对象的路径范畴

**高阶同伦群**:

在拟范畴框架中，可以定义：
- **映射空间**: Map_C(x,y) 是一个Kan复形
- **同伦群**: π_n(C, x) 通过循环空间定义

**无穷群胚作为Kan复形**:

如果拟范畴 X 中的所有1-单形都可逆（即 X 是Kan复形），则 X 表示一个无穷群胚。

**Grothendieck的无穷群胚假设**:

> 拓扑空间的同伦类型与无穷群胚是等价的。

这构成了无穷范畴论的拓扑基础。

### 1.4 同伦相干性与复合 / Homotopy Coherence and Composition

同伦相干性（Homotopy Coherence）是无穷范畴理论的核心概念。

**复合的非唯一性**:

在无穷范畴中，复合不是唯一确定的运算。给定可复合的1-态射 f, g，可能存在多个"复合" h，它们之间由可逆的2-态射连接。

**严格化问题**:

给定一个"同伦交换"的图表，何时可以严格化？这引出了：
- **A_无穷-代数**: 结合律仅成立到同伦
- **E_无穷-代数**: 交换律和结合律仅成立到同伦

**Mac Lane相干性定理的无穷-版本**:

在无穷范畴中，所有的相干性条件都被自动满足——这不是需要证明的定理，而是内置于定义中的性质。

**无穷-函子**:

无穷范畴之间的"正确"映射是无穷-函子，它保持结构到同伦等价。在拟范畴模型中，这是单纯集之间的内映射。

**同伦极限与余极限**:

无穷范畴中最强大的工具之一是：
- **同伦极限**（Homotopy limits）: 在同伦意义下的极限
- **同伦余极限**（Homotopy colimits）: 在同伦意义下的余极限

这些概念在导出范畴和拓扑中至关重要。

---

## 2. 现代观点 / Modern Perspectives

### 2.1 模型独立方法 / Model-Independent Approach

随着无穷范畴理论的发展，研究者们开始追求"模型独立"的方法。

**动机**:

- 不同的无穷范畴模型（拟范畴、单纯范畴、Segal空间等）都有优缺点
- 应该有一种"抽象"的无穷范畴理论，不依赖于具体模型
- 这类似于可以在不提及具体表示的情况下研究群或拓扑空间

**Riehl-Verity方法**:

Emily Riehl和Dominic Verity发展了基于无穷-余森（infinity-cosmos）的框架：
- 定义了"无穷范畴的宇宙"（infinity-cosmos）
- 在其中可以发展无穷范畴论而不指定具体模型
- 证明了各个模型之间的等价性

**形式语言**:

正在发展中的"形式无穷范畴论"使用：
- 高阶类型论
- 合成无穷范畴论
- 模态类型论

**优点**:

- 概念更清晰，避免模型特定的技术细节
- 证明更通用，适用于所有模型
- 更接近数学家的直观

### 2.2 无穷Topos理论 / Infinity-Topos Theory

无穷-Topos是普通Topos理论的高维推广，由Lurie系统发展。

**定义**:

无穷-Topos是满足以下条件的无穷范畴 X：
- 存在"小"无穷范畴 C 和 fully faithful geometric embedding X ↪ P(C)
- 或者等价地：满足无穷-Giraud公理

**关键性质**:

无穷-Topos具有：
- **无穷-余完备性**: 所有小无穷-余极限存在
- **局部笛卡尔闭性**: 切片范畴良好 behaved
- **对象分类子**: 可以"分类"一族对象

**例子**:

1. **无穷-预层无穷-Topos**: P(C) = Fun(C^op, S)
   - 其中 S 是无穷-群胚的无穷范畴
   
2. **拓扑空间的无穷-Topos**: Shv(X)
   - 空间上的无穷-层（sheaves of spaces）
   
3. **凝聚无穷-Topos**: 具有"凝聚结构"的无穷-Topos

**应用**:

无穷-Topos论为以下领域提供了基础：
- 导出代数几何
- 代数拓扑中的层论
- 同伦型理论（Homotopy Type Theory）的语义

### 2.3 稳定无穷范畴 / Stable Infinity-Categories

稳定无穷范畴是三角范畴的无穷-推广，在同调代数中至关重要。

**动机**:

在经典同调代数中：
- 链复形范畴具有同伦范畴（导出范畴）
- 导出范畴是三角范畴
- 但导出范畴的结构丢失了一些信息

**定义**:

无穷范畴 C 是**稳定**的，如果：
1. 存在零对象 0 ∈ C
2. 每个态射都有纤维和余纤维
3. 纤维和余纤维序列重合（即三角形既是纤维序列又是余纤维序列）

**与三角范畴的关系**:

稳定无穷范畴的同伦范畴是三角范畴：
hC = 三角范畴

但稳定无穷范畴保留了更多结构（高阶同伦信息）。

**重要例子**:

1. **谱的无穷范畴** Sp:
   - 对象: 谱（spectra）
   - 这是稳定的"普适"例子

2. **导出无穷范畴** D(A):
   - Abel范畴 A 的导出无穷范畴
   - 对象是链复形

3. **模的无穷范畴**:
   - 环谱 R 上的模

**t-结构**:

稳定无穷范畴可以配备t-结构：
- 将范畴分解为" connective"和" coconnective"部分
- 对应于同调度数的分解

### 2.4 导出与谱代数几何 / Derived and Spectral Algebraic Geometry

导出代数几何（DAG）和谱代数几何（SAG）是代数几何的高维推广。

**导出代数几何**:

由Toen-Vezzosi和Lurie独立发展：
- 使用交换微分分次代数（cdgas）代替交换环
- 允许"高阶结构"和"同伦信息"
- 可以处理真正的"交点"（virtual intersections）

**谱代数几何**:

更进一步，使用 E_无穷-环谱：
- 对象是谱，具有交换乘性结构
- 包含拓扑信息
- 与稳定同伦论密切相关

**核心构造**:

1. **导出概形 / 谱概形**:
   - 局部仿射的环化无穷-Topos
   - 仿射导出概形: Spec(A) 对于 A 是cdga或 E_无穷-环谱

2. **导出栈**:
   - 高阶 stack 的导出版本
   - 可以表示模函子到无穷-群胚

3. **拟相干层**:
   - 导出/谱概形上的层
   - 取值在链复形或谱中

**与经典代数几何的关系**:

- 经典概形嵌入为0-截断的导出概形
- 导出几何提供了"形变理论"的正确框架
- 谱几何提供了拓扑信息的编码

**应用**:

- 枚举几何（Gromov-Witten理论）
- 形变理论
- 拓扑循环同调

---

## 3. 研究前沿 / Research Frontiers

### 3.1 无穷范畴的计算机形式化 / Formalization of Infinity-Categories

将无穷范畴论形式化到计算机中是当前的重要研究方向。

**挑战**:

- 无穷范畴涉及无限层次的高阶结构
- 传统类型论难以直接表达
- 需要新的形式化方法

**合成无穷范畴论**:

Riehl-Shulman的**合成无穷范畴论**（Synthetic Infinity-Category Theory）：
- 在类型论中引入新的原语表达无穷范畴结构
- 使用"箭图"（arrows）和"纤维"（fibrations）作为基本概念
- 在同伦类型论框架内工作

**立方类型论方法**:

使用立方类型论（Cubical Type Theory）：
- 提供计算意义的单值公理
- 允许直接操作高维立方体（对应高阶路径）
- 可以定义和计算无穷范畴构造

**进展**:

- **agda-unimath**: 使用Agda形式化无穷范畴论
- **rzk**: 专门的合成无穷范畴证明助手
- **Lean中的形式化**: 使用Lean的HoTT库

**未来方向**:

- 完整形式化Lurie的《Higher Topos Theory》
- 形式化导出代数几何
- 形式化稳定无穷范畴理论

### 3.2 凝聚无穷Topos / Cohesive Infinity-Toposes

凝聚无穷-Topos由Schreiber发展，融合了微分几何和无穷-范畴论。

**基本概念**:

凝聚无穷-Topos H 配备了一组伴随函子：

∫ ⊣ ♭ ⊣ ♯ ⊣ ♯'

或更常见的形式：

Disc ⊣ Γ ⊣ coDisc : H → ∞Grpd

加上额外的"凝聚"结构：
- ∫（形状/离散化）
- ♭（平坦）
- ♯（尖锐）

**几何解释**:

这些模态对应于：
- **形状**: 提取空间的"纯同伦类型"
- **平坦**: 将离散无穷-群胚嵌入为"平坦"对象
- **尖锐**: 收缩空间为点集

**微分凝聚**:

进一步加入无穷小结构：
- **无穷小形状** ∫_inf
- **de Rham模态**
- 允许形式化切无穷-丛、微分形式等

**物理应用**:

凝聚无穷-Topos可以形式化：
- **规范理论**: 主丛、联络、曲率
- **弦论**: Kalb-Ramond场、陈-西蒙斯理论
- **M-理论**: 高阶规范场

**数学应用**:

- de Rham上同调的无穷-范畴表述
- 微分上同调（Differential cohomology）
- Chern-Weil理论

### 3.3 高阶代数结构 / Higher Algebraic Structures

无穷-范畴论使得严格定义和研究高阶代数结构成为可能。

**E_n-代数**:

- **E_1-代数**: 同伦结合代数（A_无穷-代数）
- **E_2-代数**: 具有两个相容的结合乘积
- **E_无穷-代数**: 同伦交换代数

这些结构在拓扑学和物理学中自然出现。

**Operads**:

无穷-Operads是组织高阶代数结构的工具：
- **无穷-Operad**: 推广经典Operad到无穷-范畴
- **little n-cubes operad**: 对应 E_n-结构
- **交换Operad**: 对应 E_无穷-结构

**环谱与模**:

在稳定无穷-范畴中：
- **结合环谱**: A_无穷-环谱
- **交换环谱**: E_无穷-环谱
- **模的无穷范畴**: Mod_R

**高阶群**:

无穷-群是只有一个对象的无穷-群胚：
- **拓扑群**: 作为无穷-群
- **单纯群**: Kan复形模型
- **带附加结构的群**: Lie 无穷-群、形式群等

**当前研究**:

- 高阶Hopf代数
- 无穷-李代数（L-无穷代数）
- 高阶表示论

### 3.4 几何表示论 / Geometric Representation Theory

几何表示论使用几何方法（特别是无穷-范畴方法）研究表示论。

**基本思想**:

不直接研究群的表示，而是研究与群相关的几何对象，然后从这些几何对象"提取"表示。

**D-模与导出范畴**:

- **D-模**: 代数簇上的微分方程层
- **导出范畴** D(X): 具有丰富结构的无穷-范畴
- **Riemann-Hilbert对应**: D-模与局部系统的等价

**范畴化**:

几何表示论常常涉及"范畴化"：
- 将数字（维数）替换为范畴（导出范畴）
- 将等式替换为等价
- 这自然地导向无穷-范畴

**Langlands纲领的几何化**:

- **几何Langlands对应**: 函数域Langlands的几何版本
- **量子几何Langlands**: 含参数的版本
- **范畴化Langlands**: 上升到无穷-范畴层次

**重要发展**:

- **Gaitsgory**的量子几何Langlands纲领
- **Ben-Zvi, Nadler**的拓扑场论与表示论联系
- **Arinkin-Gaitsgory**的奇异支撑理论

**当前前沿**:

- 导出代数几何在表示论中的应用
- 周期结构（Period sheaves）
- 迹公式（Trace formulas）的无穷-范畴表述

---

## 4. 应用前沿 / Frontier Applications

### 4.1 代数K-理论与拓扑循环同调 / Algebraic K-Theory and TC

代数K-理论是代数几何和数论中的核心不变量，无穷-范畴提供了新的研究工具。

**代数K-理论**:

对于环 R，其代数K-群 K_i(R) 是重要的不变量。在无穷-范畴框架中：
- 可以定义环谱的K-理论
- K-理论是加性不变量
- 与拓扑循环同调（TC）有密切联系

**拓扑循环同调**:

拓扑循环同调 TC(R) 是：
- 逼近K-理论的同伦不变量
- 更容易计算
- 与微分形式、de Rham-Witt复形有关

**Dundas-Goodwillie-McCarthy定理**:

K(R) → TC(R)

在相对设置中是同伦纤维序列，这是计算K-理论的强大工具。

**导出代数几何中的应用**:

- **虚基本类**: 在导出几何中自然出现
- **枚举几何**: Gromov-Witten不变量
- **形变理论**: 通过K-理论理解形变

**当前研究**:

- 拓扑Hochschild同调（THH）的计算
- 周期性拓扑循环同调（TP）
- 棱柱上同调（Prismatic cohomology）与K-理论

### 4.2 椭圆上同调与拓扑模形式 / Elliptic Cohomology and TMFs

椭圆上同调是将椭圆曲线与代数拓扑联系起来的深刻理论。

**椭圆上同调**:

椭圆上同调是一种广义上同调理论 E，满足：
- 形式群律由椭圆曲线给出
- 与弦论有深刻联系

**拓扑模形式**:

**拓扑模形式谱**（Topological Modular Forms, TMF）是：
- 对应于模形式层的环谱
- 具有极其丰富的同伦群结构
- 包含稳定同伦群中的重要信息

**无穷-范畴视角**:

TMF的构造本质上是无穷-范畴的：
- 定义在椭圆曲线的模空间上
- 需要层条件的高阶版本
- 涉及导出代数几何

**与弦论的联系**:

- **Witten亏格**: 与椭圆上同调相关的拓扑不变量
- **弦的指标定理**: 涉及Dirac算子和椭圆曲线
- **二维共形场论**: 与TMF的结构相关

**最新发展**:

- **高阶椭圆上同调**: 对应更高维的Abel簇
- **topological automorphic forms**: 自守形式的拓扑版本
- **equivariant elliptic cohomology**: 等变版本

### 4.3 朗兰兹纲领的几何化 / Geometrization of Langlands

Langlands纲领是数论和表示论中的宏伟统一理论，其几何版本使用无穷-范畴技术。

**几何Langlands对应**:

对于曲线 X 和可约群 G，存在猜想对应：

D-Mod(Bun_G(X)) ⟷ Qcoh(Loc_{G^L}(X))

- 左边: G-丛模空间上的D-模
- 右边: G^L-局部系统模空间上的拟相干层

**无穷-范畴的作用**:

- D-模范畴是无穷-范畴
- 需要导出代数几何的技术
- 函子性的高阶版本

**量子几何Langlands**:

Gaitsgory发展的量子版本：
- 包含形变参数
- 涉及量子群和Kac-Moody代数
- 使用因子化代数（factorization algebras）

**算术与几何的联系**:

- **函数域**: 几何Langlands最成熟的设置
- **数域**: 仍在发展中，但有几何启发
- **几何方法在算术中的应用**: 如shtukas、迹公式

**当前前沿**:

- **范畴化Langlands**: 上升到无穷-范畴层次
- **wild ramification**: 非驯顺分歧的处理
- **p-adic Langlands**: p-adic版本的进展

---

## 5. 参考文献 / References

### 5.1 奠基性著作 / Foundational Works

1. **Lurie, J.** (2009)
   - *Higher Topos Theory*
   - Annals of Mathematics Studies, Princeton University Press
   - 无穷-Topos理论的奠基性著作，定义了拟范畴框架

2. **Lurie, J.** (2017)
   - *Higher Algebra*
   - 在线版本: www.math.harvard.edu/~lurie/
   - 稳定无穷-范畴、代数结构、环谱的系统研究

3. **Joyal, A.** (2002, 2008)
   - *Quasi-categories and Kan complexes*
   - 拟范畴理论的奠基工作
   - *The Theory of Quasi-categories and its Applications* (2008, CRM Barcelona)

4. **Boardman, J.M. & Vogt, R.M.** (1973)
   - *Homotopy Invariant Algebraic Structures on Topological Spaces*
   - Lecture Notes in Mathematics 347, Springer
   - 早期使用Operad研究同伦代数结构

### 5.2 现代专著 / Modern Monographs

5. **Riehl, E.** (2014)
   - *Categorical Homotopy Theory*
   - Cambridge University Press
   - 模型范畴和无穷-范畴的入门经典

6. **Riehl, E. & Verity, D.** (2022)
   - *Elements of Infinity-Category Theory*
   - Cambridge University Press
   - 模型独立的无穷-范畴理论

7. **Cisinski, D.-C.** (2019)
   - *Higher Categories and Homotopical Algebra*
   - Cambridge University Press
   - 从模型范畴到无穷-范畴的现代视角

8. **Toen, B.** (2014)
   - *Derived Algebraic Geometry*
   - EMS Surveys in Mathematical Sciences
   - 导出代数几何的综述

9. **Lurie, J.** (2018)
   - *Spectral Algebraic Geometry*
   - 在线版本
   - 谱代数几何的完整理论

10. **Richter, B.** (2020)
    - *From Categories to Homotopy Theory*
    - Cambridge University Press
    - 从范畴论到同伦论的桥梁

### 5.3 前沿研究论文 / Frontier Research Papers

11. **Rezk, C.** (2001)
    - *A Model for the Homotopy Theory of Homotopy Theory*
    - Transactions of the AMS
    - 完备Segal空间的奠基论文

12. **Bergner, J.E.** (2007)
    - *Three models for the homotopy theory of homotopy theories*
    - Topology
    - 比较不同无穷-范畴模型的等价性

13. **Riehl, E. & Shulman, M.** (2017)
    - *A Type Theory for Synthetic Infinity-Categories*
    - Higher Structures
    - 合成无穷-范畴论的开创性工作

14. **Schreiber, U.** (2013)
    - *Differential cohomology in a cohesive infinity-topos*
    - arXiv:1310.7930
    - 凝聚无穷-Topos的全面论述

15. **Gaitsgory, D. & Rozenblyum, N.** (2017)
    - *A Study in Derived Algebraic Geometry*
    - Volumes I & II, AMS
    - 导出代数几何和几何表示论的权威著作

16. **Blumberg, A.J., Gepner, D. & Tabuada, G.** (2013)
    - *A universal characterization of higher algebraic K-theory*
    - Geometry & Topology
    - 无穷-范畴中K-理论的普遍性质

17. **Hopkins, M.J. & Lurie, J.** (2019)
    - *Ambidexterity in K(n)-local stable homotopy theory*
    - 高阶代数拓扑的深入结果

18. **Arinkin, D. & Gaitsgory, D.** (2015)
    - *Singular support of coherent sheaves and the geometric Langlands conjecture*
    - Selecta Mathematica
    - 几何Langlands纲领的突破性工作

19. **Barwick, C. & Kan, D.M.** (2012)
    - *Relative categories: Another model for the homotopy theory of homotopy theories*
    - Indagationes Mathematicae
    - 相对范畴作为无穷-范畴模型

20. **Antieau, B., Gepner, D. & Heller, J.** (2018)
    - *K-theoretic obstructions to bounded t-structures*
    - Inventiones Mathematicae
    - K-理论与t-结构的现代研究

### 5.4 在线资源与工具 / Online Resources and Tools

21. **nLab** - https://ncatlab.org/nlab/show/higher+category+theory
    - 关于高阶范畴论的综合wiki

22. **Kerodon** - https://kerodon.net/[需更新[需更新]]
    - Jacob Lurie维护的无穷-范畴论在线资源

23. **MathOverflow** - https://mathoverflow.net/questions/tagged/higher-category-theory
    - 高阶范畴论相关问题讨论

24. **Lurie's Website** - https://www.math.ias.edu/~lurie/[需更新[需更新]]
    - 所有论文和著作的原始版本

25. **Riehl's Website** - https://math.jhu.edu/~eriehl/[需更新[需更新]]
    - Emily Riehl的讲义和补充材料

26. **GitHub: agda-unimath** - https://github.com/UniMath/agda-unimath
    - Agda中无穷-范畴论的形式化

27. **GitHub: rzk** - https://github.com/rzk-lang/rzk
    - 合成无穷-范畴的证明助手

---

**文档信息**:
- **创建日期**: 2026年4月4日
- **更新状态**: 首次发布
- **目标读者**: 代数几何、代数拓扑、范畴论研究人员和研究生
- **前置知识**: 基础范畴论、同伦论、代数几何入门

---

**相关链接**:
- [06-无穷范畴理论](./06-无穷范畴理论.md) - 基础版本
- [05-导出代数几何](./05-导出代数几何.md) - 导出几何深入
- [homotopy-type-theory.md](./homotopy-type-theory.md) - 同伦类型论深度版
