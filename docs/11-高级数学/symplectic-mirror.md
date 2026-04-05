---
title: 辛几何与镜像对称深度版 / Symplectic Geometry and Mirror Symmetry - In Depth
msc_primary: 00A99
msc_secondary:
- 14J33
- 32Q25
- 81T30
processed_at: '2026-04-05'
---
# 辛几何与镜像对称深度版 / Symplectic Geometry and Mirror Symmetry - In Depth

## 目录

- 辛几何与镜像对称深度版 / Symplectic Geometry and Mirror Symity - In Depth
  - [目录](#目录)
  - [1. 深入概念 / Deep Concepts](#1-深入概念-deep-concepts)
    - [1.1 辛流形的现代观点 / Modern Perspectives on Symplectic Manifolds](#11-辛流形的现代观点-modern-perspectives-on-symplectic-manifolds)
    - [1.2 Fukaya范畴的深层结构 / Deep Structure of Fukaya Categories](#12-fukaya范畴的深层结构-deep-structure-of-fukaya-categories)
    - [1.3 导出范畴与相干性 / Derived Categories and Coherence](#13-导出范畴与相干性-derived-categories-and-coherence)
    - [1.4 特殊拉格朗日子流形 / Special Lagrangian Submanifolds](#14-特殊拉格朗日子流形-special-lagrangian-submanifolds)
  - [2. 现代观点 / Modern Perspectives](#2-现代观点-modern-perspectives)
    - [2.1 同调镜像对称 / Homological Mirror Symmetry](#21-同调镜像对称-homological-mirror-symmetry)
    - [2.2 SYZ猜想的几何 / Geometry of SYZ Conjecture](#22-syz猜想的几何-geometry-of-syz-conjecture)
    - [2.3 热带几何与退化的镜 / Tropical Geometry and Degenerating Mirrors](#23-热带几何与退化的镜-tropical-geometry-and-degenerating-mirrors)
    - [2.4 Landau-Ginzburg模型 / Landau-Ginzburg Models](#24-landau-ginzburg模型-landau-ginzburg-models)
  - [3. 研究前沿 / Research Frontiers](#3-研究前沿-research-frontiers)
    - [3.1 一般型流形的镜像 / Mirrors of General Type](#31-一般型流形的镜像-mirrors-of-general-type)
    - [3.2 非交换几何与矩阵分解 / NC Geometry and Matrix Factorizations](#32-非交换几何与矩阵分解-nc-geometry-and-matrix-factorizations)
    - [3.3 量子上同调的深层结构 / Deep Structure of Quantum Cohomology](#33-量子上同调的深层结构-deep-structure-of-quantum-cohomology)
    - [3.4 Floer理论与开弦 / Floer Theory and Open Strings](#34-floer理论与开弦-floer-theory-and-open-strings)
  - [4. 应用前沿 / Frontier Applications](#4-应用前沿-frontier-applications)
    - [4.1 弦论与数学物理 / String Theory and Mathematical Physics](#41-弦论与数学物理-string-theory-and-mathematical-physics)
    - [4.2 计数几何与Gromov-Witten理论 / Enumerative Geometry and GW Theory](#42-计数几何与gromov-witten理论-enumerative-geometry-and-gw-theory)
    - [4.3 规范理论与低维拓扑 / Gauge Theory and Low-Dimensional Topology](#43-规范理论与低维拓扑-gauge-theory-and-low-dimensional-topology)
  - [5. 参考文献 / References](#5-参考文献-references)
    - [5.1 经典与奠基性著作 / Classical and Foundational Works](#51-经典与奠基性著作-classical-and-foundational-works)
    - [5.2 现代专著 / Modern Monographs](#52-现代专著-modern-monographs)
    - [5.3 前沿研究论文 / Frontier Research Papers](#53-前沿研究论文-frontier-research-papers)
    - [5.4 在线资源 / Online Resources](#54-在线资源-online-resources)

---

## 1. 深入概念 / Deep Concepts

### 1.1 辛流形的现代观点 / Modern Perspectives on Symplectic Manifolds

辛几何是研究辛流形的数学分支，其现代发展深刻影响了数学物理和代数几何。

**辛结构的本质**:

辛形式 $\omega$ 是流形 $M$ 上的闭非退化2-形式。非退化性条件：
$$\forall v \neq 0, \exists w \text{ s.t. } \omega(v,w) \neq 0$$

使得辛流形必须是偶数维的，并且具有自然的体积形式 $\omega^n/n!$。

**现代观点的演变**:

1. **经典力学观点**: 辛形式来自相空间（位置-动量）的自然结构
   - 哈密顿系统: $\iota_{X_H}\omega = dH$
   - 泊松括号: $\{f,g\} = \omega(X_f, X_g)$

2. **复几何观点**: Kähler流形是辛流形的特例
   - Kähler形式: $\omega = -\text{Im}(h)$ 对于Hermitian度量 $h$
   - 辛结构 + 复结构 + 黎曼结构 = Kähler结构

3. **拓扑观点**: 辛拓扑学研究辛流形的整体不变量
   - Gromov的伪全纯曲线理论
   - Floer同调
   - 辛 capacities

**几乎复结构**:

辛流形 $(M, \omega)$ 允许相容的几乎复结构 $J$，满足：
- $\omega(Jv, Jw) = \omega(v, w)$（$J$ 保持 $\omega$）
- $g(v,w) = \omega(v, Jw)$ 是黎曼度量

这使得辛流形具有"近复几何"结构。

**群胚与动量映射**:

李群作用下的辛几何：
- **动量映射** $\mu: M \to \mathfrak{g}^*$: 编码对称性
- **Marsden-Weinstein约化**: $M/\!\!/G = \mu^{-1}(0)/G$

这在规范理论和表示论中至关重要。

### 1.2 Fukaya范畴的深层结构 / Deep Structure of Fukaya Categories

Fukaya范畴是辛几何中的$A_\infty$-范畴，是同调镜像对称猜想的核心对象。

**对象与态射**:

- **对象**: 拉格朗日子流形 $L \subset M$（配备局部系统和 grading）
- **态射**: Lagrangian Floer复形 $CF^*(L_0, L_1)$
  - 生成元: 交点 $L_0 \cap L_1$
  - 微分: 计数全纯条带

**$A_\infty$-结构**:

Fukaya范畴的关键在于其高阶乘法运算 $m_k$:

$$m_k: CF^*(L_{k-1}, L_k) \otimes \cdots \otimes CF^*(L_0, L_1) \to CF^*(L_0, L_k)[2-k]$$

这些运算由计数高维多边形定义，满足$A_\infty$-关系：
$$\sum_{i+j=n+1} \sum_{k} (-1)^{\circ} m_i(\ldots, m_j(\ldots), \ldots) = 0$$

**生成元与分裂生成**:

Fukaya范畴通常是"大"的（真类大小的对象集合）。实践中：
- 寻找**分裂生成集**: 一小部分对象，其扭曲复形生成整个范畴
- **Thomason定理的辛版本**: 确定何时子范畴生成整个Fukaya范畴

**阻碍理论**:

拉格朗日子流形要成为Fukaya范畴的对象，必须满足：
- **$m_0 = 0$**: 即 $L$ 是有界的（unobstructed）
- 这涉及计数全纯盘，边界在 $L$ 上

存在两种主要的有界性条件：
- **弱有界性**（来自Cho-Oh的工作）
- **有界性**（来自FOOO的框架）

**多截面与虚拟基本链**:

构造Fukaya范畴的主要技术挑战：
- 模空间 $\overline{\mathcal{M}}_{k+1}(L; \beta)$ 可能有奇点
- 需要使用Kuranishi结构或多截面技术
- FOOO（Fukaya-Oh-Ohta-Ono）理论的复杂构造

### 1.3 导出范畴与相干性 / Derived Categories and Coherence

复代数几何中，导出范畴是镜像对称的B面核心结构。

**凝聚层与导出范畴**:

对于光滑射影簇 $X$：
- **凝聚层** $\text{Coh}(X)$: 局部有限 presentation 的 $\mathcal{O}_X$-模
- **导出范畴** $D^b(X) = D^b(\text{Coh}(X))$: 有界导出范畴

**三角结构与t-结构**:

导出范畴具有：
- **三角结构**: 表达上同调的长正合序列
- **标准t-结构**:  hearts 是凝聚层范畴
- ** hearts**: 同调对象

** Fourier-Mukai变换 **:

导出范畴之间的主要函子构造：
$$\Phi_{\mathcal{E}}: D^b(X) \to D^b(Y), \quad F \mapsto R\pi_{Y*}(\mathcal{E} \otimes^L L\pi_X^* F)$$

其中 $\mathcal{E} \in D^b(X \times Y)$ 是核（kernel）。

** Bridgeland稳定性条件 **:

导出范畴上的稳定性条件是镜像对称的重要工具：
- **中心** $Z: K(X) \to \mathbb{C}$
- **heart of a bounded t-structure** $\mathcal{A} \subset D^b(X)$
- 对于 $0 \neq E \in \mathcal{A}$，要求 $\text{Im}\, Z(E) > 0$ 且稳定性条件

**导出自等价**:

$\text{Auteq}(D^b(X))$ 包含：
- 张量积线丛
- 自同构拉回
- 平移函子 $[1]$
- 更复杂的: 球面函子、 twist 函子等

### 1.4 特殊拉格朗日子流形 / Special Lagrangian Submanifolds

特殊拉格朗日子流形是Calabi-Yau几何中的极小对象，在SYZ镜像对称猜想中起核心作用。

**定义**:

在Calabi-Yau $n$-fold $(X, \omega, \Omega)$ 中，拉格朗日子流形 $L$ 是**特殊拉格朗日的**，如果：
$$\text{Im}(e^{-i\theta}\Omega)|_L = 0$$

对于某个常数相 $\theta$（称为 $L$ 的相）。

等价地，这意味着 $L$ 校准（calibrated）由 $\text{Re}(e^{-i\theta}\Omega)$。

**性质**:

- **极小性**: 特殊拉格朗日子流形是体积极小的
- **稳定性**: 在辛变形下相对稳定
- **相交性质**: 两个不同相的特殊拉格朗日子流形几乎处处横截相交

**模空间**:

特殊拉格朗日子流形的形变由第一上同调 $H^1(L; \mathbb{R})$ 控制：
- **局部模空间**: $H^1(L; \mathbb{R})$ 中的开集
- **整体模空间**: 可能具有奇点结构（墙穿越现象）

**计数与不变量**:

Thomas提出计数特殊拉格朗日子流形定义**Donaldson-Thomas不变量**的辛几何类似物：
- 与物理中的BPS态计数相关
- 涉及特殊拉格朗日子流形的模空间的紧化
- 尚未完全解决（主要的开问题之一）

**在SYZ中的作用**:

SYZ猜想预测：
- 特殊拉格朗日子流形的纤维化的纤维是镜的环面纤维
- 奇点纤维对应于镜的奇点

---

## 2. 现代观点 / Modern Perspectives

### 2.1 同调镜像对称 / Homological Mirror Symmetry

同调镜像对称（HMS）是Kontsevich提出的镜像对称的数学精确表述。

**基本表述**:

对于镜对 $(X, X^\vee)$：

$$\text{Fuk}(X) \simeq D^b(X^\vee)$$

- 左边: $X$ 的Fukaya范畴（辛几何）
- 右边: $X^\vee$ 的凝聚导出范畴（代数几何）

**更精确的版本**:

完整的HMS应包含：
1. 三角等价的范畴
2. 与Strominger-Yau-Zaslow（SYZ）几何的相容
3. 与T-对偶的相容
4. 量子上同调的同构（经典镜像对称）

**证明策略**:

HMS已在许多例子中得到证明：
- **椭圆曲线**: Polishchuk-Zaslow
- **Abel簇**: Fukaya
- **四次曲面**: Seidel
- **Fano簇**: 大量工作（Auroux, Katzarkov, Orlov等）

证明方法包括：
- 构造明确的生成元和关系
- 使用T-对偶和SYZ纤维化
-  tropical 退化方法
- 装饰簇（cluster algebras）方法

**推论与应用**:

从HMS可以导出：
- 量子上同调的同构（通过Hochschild同调）
- 辛拓扑不变量与代数几何不变量的对应
- 自同构群的对应
- 稳定性条件的对应

**一般Calabi-Yau的HMS**:

对于一般维数的Calabi-Yau流形，HMS仍是猜想：
- 维数 $\geq 3$ 时的主要困难: 高阶修正、奇点处理
- 近年来Abouzaid, Auroux, Ganatra, Sheridan等的重要进展

### 2.2 SYZ猜想的几何 / Geometry of SYZ Conjecture

SYZ猜想提供了镜像对称的几何直观。

**基本陈述**:

Strominger, Yau, Zaslow（1996）提出：
- 镜对 $(X, X^\vee)$ 应对偶地具有特殊拉格朗日环面纤维化
- 镜变换对应于**T-对偶**（纤维的T-对偶）

$$\begin{array}{ccc}
X & \longleftrightarrow & X^\vee \\
\downarrow & & \downarrow \\
B & = & B
\end{array}$$

**T-对偶**:

对于环面 $T = V/\Lambda$：
- **T-对偶环面** $T^\vee = V^*/\Lambda^*$
- 与复结构 ↔ Kähler结构的交换相关
- 镜像对称的"半经典"（大复结构极限）近似

**奇点与纠正**:

SYZ纤维化的奇点纤维是关键：
- **焦点纤维**（Focus-focus fibers）: 2维中的典型奇点
- **拓扑变化**: 奇点处纤维化拓扑改变
- **瞬子纠正**: 全理圆盘的贡献纠正T-对偶的复结构

**SYZ的数学表述**:

Gross, Hacking, Keel, Kontsevich等人的工作将SYZ严格化：
- **Integral affine structures**: 基空间 $B$ 的几何
- **Tropical geometry**: 在 $B$ 上的"热带"结构
- **散射 diagrams**: 编码瞬子纠正的组合结构
- **装饰簇变量**: 在SYZ框架中的出现

**从SYZ到HMS**:

SYZ为HMS提供几何基础：
- Fukaya范畴的对象 → 纤维化截面 + 纤维上的线丛
- 导出范畴的对象 → 扭转层、结构层等
- 态射的对应通过T-对偶和全理圆盘计数

### 2.3 热带几何与退化的镜 / Tropical Geometry and Degenerating Mirrors

热带几何是研究镜像对称的重要组合工具。

**热带几何基础**:

热带半环 $(\mathbb{R} \cup \{-\infty\}, \oplus, \odot)$：
- $a \oplus b = \max(a,b)$
- $a \odot b = a + b$

**热带变种**:

经典代数簇的"退化"：
- 通过非Archimedean估值的Berkovich解析
-  amoeba 的 spine
- 组合结构: 多面体复形

**在镜像对称中的作用**:

1. **退化的Calabi-Yau**: 
   - 复杂的几何 → 简单的热带对象
   - 镜像对应对应于热带对偶

2. **Gromov-Witten不变量的计算**:
   - 热带曲线计数经典曲线
   - Mikhalkin的对应定理

3. **Fukaya范畴的近似**:
   - 拉格朗日子流形 → 热带对象
   - Floer理论 → 热带相交理论

**Gross-Siebert程序**:

Mark Gross和Bernd Siebert发展了使用热带几何构造镜像的系统方法：
- **Log Calabi-Yau空间**: 退化Calabi-Yau的中心纤维
- **散射 diagrams**: 从热带数据构造镜像
- **装饰簇代数**: 从散射 diagram 提取

**家族Floer理论**:

Sydney的学派发展了基于家族的Fukaya范畴构造：
- 在SYZ纤维化的基础上
- 使用热带数据编码瞬子纠正
- 与Gross-Siebert方法汇合

### 2.4 Landau-Ginzburg模型 / Landau-Ginzburg Models

Landau-Ginzburg（LG）模型是镜像对称的重要扩展，适用于非Calabi-Yau流形。

**定义**:

Landau-Ginzburg模型是一对 $(X, W)$：
- $X$: 非紧Kähler流形（通常是$(\mathbb{C}^*)^n$或更一般的簇）
- $W: X \to \mathbb{C}$: 超势（全纯函数）

**辛几何侧面（A模型）**:

LG模型的Fukaya-Seidel范畴：
- **对象**:  Lefschetz 纤维化的 vanishing 循环
- **态射**: Floer同调，考虑超势的影响
- **范畴结构**: $A_\infty$-范畴

**代数几何侧面（B模型）**:

矩阵分解范畴：
- **对象**: 一对 $(P, Q)$，配备映射 $d_P: P \to Q$, $d_Q: Q \to P$
- 满足 $d_Q \circ d_P = W \cdot \text{id}_P$, $d_P \circ d_Q = W \cdot \text{id}_Q$
- **态射**: 链映射模同伦
- **范畴**: $\text{MF}(X, W)$ 或奇点范畴 $D_{\text{sg}}(X, W)$

**HMS for LG models**:

$$
\text{Fuk}(W) \simeq \text{MF}(X^\vee, W^\vee)
$$

已在许多情况下得到证明：
- toric Fano簇
- 加权射影空间
- 部分旗簇

**与几何的关系**:

LG模型与以下几何对象相关：
- **Fano簇的镜像**: Fano簇 ↔ LG模型
- **一般型簇的镜像**: 一般型簇 ↔ LG模型
- **带除子的Calabi-Yau**: 通过超势编码边界条件

**Hori-Vafa构造**:

Hori和Vafa从物理角度提出构造toric簇的镜像：
- 使用对偶性论证
- 给出明确的超势公式
- 与Givental的镜像定理一致

---

## 3. 研究前沿 / Research Frontiers

### 3.1 一般型流形的镜像 / Mirrors of General Type

一般型代数簇（$K_X$ ample）的镜像对称是当前的重要前沿。

**挑战**:

与Fano或Calabi-Yau情况不同：
- 一般型流形没有明显的镜像对
- 辛几何侧面可能不存在（或非常退化）
- 需要新的数学框架

**Kapustin-Katzarkov-Orlov-Yotov提案**:

KKOY提出：一般型流形的镜像是"Landau-Ginzburg轨道ifold"：
- 不是几何对象，而是带有超势的轨道ifold
- 辛侧面通过"广义复几何"理解

**Gross-Katzarkov-Ruddat方法**:

使用热带几何和log结构：
- 从退化数据构造镜像
- 利用scattering diagrams
- 处理一般型流形的复杂性

**Heegaard Floer同调的联系**:

一般型曲面的辛几何与3维流形的不变量有联系：
- Lefschetz纤维化与3维流形的边界
- Heegaard Floer同调的计算
- 与规范理论的联系

**当前进展**:

- Abouzaid-Auroux 关于一般型曲面的工作
- Sheridan 在高维的工作
- 仍有许多未解决问题

### 3.2 非交换几何与矩阵分解 / NC Geometry and Matrix Factorizations

矩阵分解和非交换几何为镜像对称提供了新的视角。

**矩阵分解的深层结构**:

对于超势 $W: X \to \mathbb{C}$，矩阵分解范畴 $\text{MF}(X, W)$ 具有丰富的结构：
- **三角范畴**: 具有移位和三角形
- **张量结构**: 对于可交换的超势
- **对偶性**: Grothendieck-Verdier对偶

**Orlov的定理**:

Orlov证明：对于孤立超曲面奇点 $(X, W)$：

$$\text{MF}(X, W) \simeq D_{\text{sg}}(X_0)$$

其中 $X_0 = W^{-1}(0)$，$D_{\text{sg}}$ 是奇点范畴（凝聚模有界导出范畴模完美复形）。

**高维矩阵分解**:

对于矩阵值超势或更一般的设置：
- **曲线上的矩阵分解**
- **非交换超曲面**
- **非几何Landau-Ginzburg模型**

**与拓扑场论的联系**:

矩阵分解在拓扑场论中出现：
- **2维拓扑场论的B模型**: 对应于矩阵分解范畴
- **矩阵因子的2-范畴**: Kapranov-Schechtman
- **高阶范畴结构**: Rozansky-Witten理论的输入

**非交换Hodge理论**:

Kontsevich和 Katzarkov-Nadler-Pantev 发展了非交换Hodge理论：
- **周期映射**: 对于DG范畴
- **Hodge结构**: 推广到非交换设置
- **镜像对称**: 在Hodge理论层面的对应

### 3.3 量子上同调的深层结构 / Deep Structure of Quantum Cohomology

量子上同调是镜像对称的经典（非范畴）侧面。

**定义回顾**:

量子上同调环 $QH^*(X)$：
- 作为模: $H^*(X) \otimes \Lambda$，其中 $\Lambda$ 是Novikov环
- 乘积: 3点Gromov-Witten不变量定义
$$a \star b = \sum_{\beta} \langle a, b, - \rangle_{0,3,\beta} \, q^\beta$$

**Frobenius流形**:

量子上同调具有Frobenius流形结构：
- **度量**: Poincaré配对
- **乘法**: 量子上同调配对
- **单位**: 基本类
- **Frobenius条件**: $(a \star b, c) = (a, b \star c)$

**Dubrovin连接**:

Frobenius流形上的平坦连接：
$$\nabla_X Y = \nabla_X^{\text{LC}} Y + z^{-1} X \star Y$$

其中 $z$ 是形式参数。平坦性等价于WDVV方程。

**与镜像对称的联系**:

经典镜像对称预言：
- $QH^*(X)$ 的生成函数对应于 $X^\vee$ 上的周期积分
- $I$-函数和 $J$-函数的对应
- Givental的镜像定理（toric情形）

**Teleman的论文**:

Constantin Teleman关于量子上同调和低维拓扑的工作：
- Gromov-Witten理论与拓扑场论的联系
- 量子上同调的更深层结构
- 半单Frobenius流形的分类

### 3.4 Floer理论与开弦 / Floer Theory and Open Strings

Floer理论是辛几何和镜像一个面的核心工具，与开弦理论密切相关。

**Hamiltonian Floer同调**:

对于闭辛流形 $(M, \omega)$：
- 链复形: 1-周期Hamilton轨道的生成
- 微分: 计数连接轨道的全理圆柱
- 同调: $HF^*(M) \cong H^*(M)$（对于合适类别）

**Lagrangian Floer同调**:

对于拉格朗日子流形 $L_0, L_1$：
- 链复形: $CF^*(L_0, L_1)$，生成元是交点
- 微分: 计数边界在 $L_0$ 和 $L_1$ 上的全理条带

**与开弦的联系**:

在弦论中：
- **闭弦**: 对应Hamiltonian Floer同调
- **开弦**: 对应Lagrangian Floer同调，边界在D-膜（拉格朗日子流形）上

**obstruction与 Maurer-Cartan方程**:

拉格朗日子流形的有界性（unobstructedness）：
- **$m_0$ 障碍**: $m_0(1) = \sum_{\beta} n_\beta(L) T^{\omega(\beta)} \cdot [L]$
- **弱有界性**: $m_0(1) = c \cdot [L]$ 对于常数 $c$
- **变形**: 使用 local system 或 bounding cochain 纠正

**浸入Floer理论**:

Akaho-Joyce和Seidel的发展：
- 允许拉格朗日浸入，而不仅是嵌入
- 自交点成为额外的生成元
- 与装饰簇和可积系统的联系

---

## 4. 应用前沿 / Frontier Applications

### 4.1 弦论与数学物理 / String Theory and Mathematical Physics

镜像对称起源于弦论，现在反过来为物理提供了深刻的数学工具。

**弦论背景**:

在弦论中，镜像对称对应于：
- **Type IIA弦**: 在Calabi-Yau $X$ 上紧致化，复结构模量
- **Type IIB弦**: 在镜 $X^\vee$ 上紧致化，Kähler模量
- 两种理论的物理等价

**超弦理论中的镜像**:

- **$N=2$超共形场论**: 在世界面上的对称性
- **chiral ring**: 拓扑扭变后的算子代数
- **A-twist ↔ B-twist**: 对应于辛几何 ↔ 复几何

**D-膜与范畴**:

在弦论中，D-膜是开弦的边界条件：
- **A-膜**: 拉格朗日子流形（A-模型）
- **B-膜**: 复子流形或复的层（B-模型）
- **HMS**: D-膜范畴的等价

**BPS态计数**:

镜像对称预言BPS态的生成函数：
- **Donaldson-Thomas不变量**: 计数BPS粒子
- **Gopakumar-Vafa不变量**: 从Gromov-Witten不变量提取
- **稳定性条件**: 决定哪些态是BPS的

**量子引力的数学**:

镜像对称为量子引力的数学理解提供窗口：
- **黑洞熵**: 通过镜像对称计算
- **AdS/CFT对应**: 与弦论对偶性的联系
- **涌现时空**: 从范畴结构重构几何

### 4.2 计数几何与Gromov-Witten理论 / Enumerative Geometry and GW Theory

镜像对称在计数几何中提供了计算工具，解决了经典的枚举问题。

**经典枚举问题**:

- **平面曲线**: 经过 $3d-1$ 个一般点的 $d$ 次有理平面曲线的数目
- **五次 threefold 的曲线**: Clemens猜想的内容
- **一般Calabi-Yau的曲线**: 未解决的难题

**Gromov-Witten不变量**:

Gromov-Witten理论提供了系统的方法：
- **模空间**: $\overline{\mathcal{M}}_{g,n}(X, \beta)$ 稳定映射的模空间
- **虚基本类**: $[\overline{\mathcal{M}}_{g,n}(X, \beta)]^{\text{vir}}$
- **不变量**: 通过与评估映射的推拉定义

**镜像定理**:

Givental和Lian-Liu-Yau证明的镜像定理：
- toric Fano和Calabi-Yau的完整解
- $I$-函数和 $J$-函数的对应
- 通过双霍奇结构和GKZ系统

**Severi次数与热带几何**:

Mikhalkin的对应定理：
- 平面曲线的经典计数 = 热带曲线的计数
- 通过Toric退化证明
- 推广到高维和高亏格

**Vakil的突破**:

Ravi Vakil关于曲线模空间和计数几何的工作：
- **曲线模空间的相交理论**: 通过退化方法
- **纤维化方法**: 从低维到高维
- **数学软件**: Macaulay2在计数几何中的应用

### 4.3 规范理论与低维拓扑 / Gauge Theory and Low-Dimensional Topology

镜像对称与规范理论有深刻联系，特别是在低维拓扑中。

**Donaldson理论**:

4维流形的不变量：
- **瞬子模空间**: ASD连接的模空间
- **Donaldson不变量**: 相交理论的积分
- **与Floer理论的联系**: 3维边界条件

**Seiberg-Witten理论**:

Witten提出的简化：
- **单极方程**: 比瞬子方程更简单
- **Seiberg-Witten不变量**: 更容易计算
- **与辛几何的联系**: Taubes的工作

**Atiyah-Floer猜想**:

关于3维流形不变量的猜想：
- **瞬子Floer同调**: 从规范理论构造
- **拉格朗日Floer同调**: 从辛几何构造
- **猜想**: 对于曲面 $\times$ 圆周，两者同构

**Heegaard Floer同调**:\n
Ozsváth和Szabó的不变量：
- **构造**: 来自对称积的拉格朗日Floer同调
- **性质**: 类似于Seiberg-Witten Floer同调
- **应用**:  Lens space surgeries, knot invariants

**规范理论与HMS**:

Abouzaid和Smith等人的工作：
- **曲面的Fukaya范畴**: 与表示论的联系
- **HMS for 局部曲面**: 通过规范理论理解
- **Nadler-Zaslow定理**: 余切丛的Fukaya范畴与 constructible sheaves

**低维拓扑的未来方向**:

- 4维流形分类的完整理解
- 结不变量的范畴化
- 3维流形的信息完全由Fukaya范畴决定

---

## 5. 参考文献 / References

### 5.1 经典与奠基性著作 / Classical and Foundational Works

1. **McDuff, D. & Salamon, D.** (2017, 3rd ed.)
   - *Introduction to Symplectic Topology*
   - Oxford University Press
   - 辛拓扑的标准入门教材

2. **Cannas da Silva, A.** (2001)
   - *Lectures on Symplectic Geometry*
   - Lecture Notes in Mathematics, Springer
   - 辛几何的清晰介绍

3. **Hori, K., Katz, S., Klemm, A., Pandharipande, R., Thomas, R., Vafa, C., Vakil, R., & Zaslow, E.** (2003)
   - *Mirror Symmetry*
   - Clay Mathematics Monographs, AMS
   - 镜像对称的权威综合教材

4. **Kontsevich, M.** (1995)
   - *Homological Algebra of Mirror Symmetry*
   - ICM Proceedings, Zürich
   - 同调镜像对称猜想的开创性论文

5. **Seidel, P.** (2008)
   - *Fukaya Categories and Picard-Lefschetz Theory*
   - European Mathematical Society
   - Fukaya范畴的权威专著

6. **Gross, M., Hacking, P., & Keel, S.** (2015)
   - *Mirror Symmetry for Log Calabi-Yau Surfaces I*
   - Publications mathématiques de l'IHÉS
   - SYZ和装饰簇方法的重要工作

### 5.2 现代专著 / Modern Monographs

7. **Auroux, D.** (2009)
   - *A Beginner's Introduction to Fukaya Categories*
   - Contact and Symplectic Topology, Springer
   - Fukaya范畴的入门讲义

8. **Fukaya, K., Oh, Y.-G., Ohta, H., & Ono, K.** (2009-2020)
   - *Lagrangian Intersection Floer Theory: Anomaly and Obstruction*
   - Parts I & II, AMS/IP Studies in Advanced Mathematics
   - FOOO理论，Fukaya范畴的完整技术基础

9. **Gross, M., Hacking, P., Keel, S., & Kontsevich, M.** (2018)
   - *Canonical Bases for Cluster Algebras*
   - Journal of the AMS
   - 装饰簇与镜像对称的联系

10. **Ganatra, S.** (2012)
    - *Symplectic Cohomology and Duality for the Wrapped Fukaya Category*
    - MIT PhD Thesis
    - 开弦理论的现代视角

11. ** Sheridan, N.** (2017)
    - *Versality of the Fukaya Category*
    - 高维同调镜像对称的重要工作

12. **Cox, D.A. & Katz, S.** (1999)
    - *Mirror Symmetry and Algebraic Geometry*
    - Mathematical Surveys and Monographs, AMS
    - 代数几何侧面

### 5.3 前沿研究论文 / Frontier Research Papers

13. **Strominger, A., Yau, S.-T., & Zaslow, E.** (1996)
    - *Mirror Symmetry is T-Duality*
    - Nuclear Physics B
    - SYZ猜想的奠基论文

14. **Abouzaid, M.** (2012)
    - *On the Wrapped Fukaya Category and the Commutative Picard Variety*
    - Acta Mathematica
    - HMS在Abel簇上的证明

15. **Auroux, D., Katzarkov, L., & Orlov, D.** (2005)
    - *Mirror Symmetry for Weighted Projective Planes and Their Noncommutative Deformations*
    - Annals of Mathematics
    - 非交换几何与镜像对称

16. **Givental, A.** (1998)
    - *A Mirror Theorem for Toric Complete Intersections*
    - Contemporary Mathematics
    - toric簇镜像定理

17. **Mikhalkin, G.** (2005)
    - *Enumerative Tropical Algebraic Geometry in $\mathbb{R}^2$
    - Journal of the AMS
    - 热带几何与枚举几何的对应

18. **Gross, M. & Siebert, B.** (2011)
    - *From Real Affine Geometry to Complex Geometry*
    - Annals of Mathematics
    - Gross-Siebert镜像构造

19. **Polishchuk, A. & Zaslow, E.** (1998)
    - *Categorical Mirror Symmetry: The Elliptic Curve*
    - Advances in Theoretical and Mathematical Physics
    - 椭圆曲线的HMS

20. **Seidel, P.** (2003)
    - *A Long Exact Sequence for Symplectic Floer Cohomology*
    - Topology
    - Lefschetz纤维化的Floer理论

21. **Ganatra, S., Pardon, J., & Shende, V.** (2020)
    - *Microlocal Morse Theory of Wrapped Fukaya Categories*
    - arXiv:1909.94957
    - Wrapped Fukaya范畴的深层结构

22. **Abouzaid, M., Auroux, D., & Katzarkov, L.** (2016)
    - *Lagrangian Fibrations on Blowups of Toric Varieties and Mirror Symmetry for Hypersurfaces*
    - Publications mathématiques de l'IHÉS
    - SYZ纤维化的显式构造

### 5.4 在线资源 / Online Resources

23. **Auroux's Mirror Symmetry Seminar Notes** - https://math.berkeley.edu/~auroux/
    - Denis Auroux的讲义和笔记

24. **HMS Seminar Archive** - Various university websites
    - 同调镜像对称研讨会的资源

25. **Gross-Siebert Program Website** - Various publications
    - 热带几何镜像对称的最新进展

26. **nLab: Mirror Symmetry** - https://ncatlab.org/nlab/show/mirror+symmetry
    - 镜像对称的wiki页面

27. **String Wiki** - http://www.stringwiki.org/[需更新[需更新]]
    - 弦论wiki中的镜像对称资源

28. **ArXiv Tag: Symplectic Geometry** - https://arxiv.org/list/math.SG/recent
    - 辛几何最新论文

29. **ArXiv Tag: Algebraic Geometry** - https://arxiv.org/list/math.AG/recent
    - 代数几何最新论文（含镜像对称）

30. **Clay Mathematics Institute: Mirror Symmetry** - https://www.claymath.org/[需更新[需更新]]
    - Clay数学研究所的相关资源

---

**文档信息**:
- **创建日期**: 2026年4月4日
- **更新状态**: 首次发布
- **目标读者**: 辛几何、代数几何、数学物理研究人员和研究生
- **前置知识**: 微分几何、复几何、同调代数基础

---

**相关链接**:
- [04-数学物理高级主题](./04-数学物理高级主题.md) - 数学物理基础
- [21-现代代数几何前沿](./21-现代代数几何前沿.md) - 代数几何前沿
- [38-几何分析前沿](./38-几何分析前沿.md) - 几何分析深入
