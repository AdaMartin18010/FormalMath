---
msc_primary: "14A20"
msc_secondary: ['18Gxx', '14Fxx', '55Pxx']
---

# 导出代数几何深度版 / Derived Algebraic Geometry - Deep Dive

**主题编号**: B.11.D05
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日

---

## 目录

- [导出代数几何深度版 / Derived Algebraic Geometry - Deep Dive](#导出代数几何深度版--derived-algebraic-geometry---deep-dive)
  - [目录](#目录)
  - [1. 深入概念 / Deep Concepts](#1-深入概念--deep-concepts)
    - [1.1 导出代数的起源与动机](#11-导出代数的起源与动机)
    - [1.2 同伦代数结构](#12-同伦代数结构)
    - [1.3 导出概形与导出栈](#13-导出概形与导出栈)
  - [2. 现代观点 / Modern Perspectives](#2-现代观点--modern-perspectives)
    - [2.1 无穷范畴框架](#21-无穷范畴框架)
    - [2.2 几何Langlands纲领](#22-几何langlands纲领)
    - [2.3 导出辛几何](#23-导出辛几何)
  - [3. 研究前沿 / Research Frontiers](#3-研究前沿--research-frontiers)
    - [3.1 凝聚态数学](#31-凝聚态数学)
    - [3.2 完全相交上的矩阵因子化](#32-完全相交上的矩阵因子化)
    - [3.3 高阶代数群与表示](#33-高阶代数群与表示)
  - [4. 参考文献 / References](#4-参考文献--references)

---

## 1. 深入概念 / Deep Concepts

### 1.1 导出代数的起源与动机

**历史渊源**:

导出代数几何的思想可以追溯到多个数学传统：
- **同伦论**: Quillen的模型范畴（1967）
- **相交理论**: Serre的Tor公式（1958）
- **形变理论**: Deligne、Goldman-Millson的工作（1980s）
- **镜像对称**: Kontsevich的同调镜像对称（1994）

**核心问题**:

经典代数几何中，许多构造是"不完整的"：

1. **纤维积**: 概形的纤维积可能有"意外"的奇异性（非Tor-独立相交）
2. **模空间**: 实际的模空间维数常与"预期"维数不符
3. **层上同调**: 正合列不保持全局截面

**导出化解决方案**:

在导出代数几何中，结构层被替换为**微分分次代数**（differential graded algebra, dga）：
- 允许"负次函数"（来自Tor）
- 同伦等价取代严格同构
- 自然的变形-障碍理论

### 1.2 同伦代数结构

**微分分次代数**:

一个dga是链复形$A^\bullet$配备：
- 乘法：$A^p \otimes A^q \to A^{p+q}$
- 微分：$d: A^n \to A^{n+1}$，满足Leibniz法则

**同伦交换性**:

严格交换的dga太少。我们需要**$E_\infty$-代数**（或等价的，交换谱代数）：乘法在同伦意义下交换，且有一致的高阶同伦。

**关键概念**:

| 经典概念 | 导出对应 |
|---------|---------|
| 交换环 | simplicial commutative ring / $E_\infty$-ring |
| 模 | 谱模 / dg-模 |
| 张量积 | 导出张量积 $\otimes^L$ |
| 极限 | 同伦极限（holim） |
| 余极限 | 同伦余极限（hocolim） |

**Quillen模型范畴**:

导出代数几何使用模型范畴（或$(\infty,1)$-范畴）的框架：
- **弱等价**: 拟同构（quasi-isomorphism）
- **纤维化**: 满射（在正次数）
- **余纤维化**: 有特定提升性质的态射

### 1.3 导出概形与导出栈

**导出仿射概形**:

对于simplicial commutative ring $A$，定义：
$$\text{dSpec}(A) = (\text{Spec}(\pi_0(A)), \mathcal{O}^{\text{der}})$$

其中结构层$\mathcal{O}^{\text{der}}$取值于simplicial ring。

**截断函子**:

存在伴随对：
$$t_0: \text{dSch} \rightleftarrows \text{Sch}: i$$
- $t_0$：取经典截断（$\pi_0$）
- $i$：将经典概形视为离散导出概形

**导出栈**:

导出栈是$(\infty,1)$-函子：
$$\mathcal{X}: \text{dAff}^{\text{op}} \to \mathcal{S}$$
（取值于空间/同伦类型）

满足下降条件（对于导出下降双复形的同伦极限）。

**关键例子**:

1. **导出临界轨迹**: 对于函数$f: X \to \mathbb{A}^1$，导出零点轨迹：
   $$\text{Crit}^{\text{der}}(f) = \text{dSpec}(\text{Sym}(\mathbb{T}_X[1] \xrightarrow{df} \mathcal{O}_X))$$

2. **导出交截**: 对于不交截的浸入$i: Y \hookrightarrow X$，导出自交：
   $$Y \times_X^{\text{der}} Y = \text{dSpec}(\text{Sym}_Y(\mathbb{N}_{Y/X}[1]))$$

---

## 2. 现代观点 / Modern Perspectives

### 2.1 无穷范畴框架

**为什么需要无穷范畴**:

在导出代数几何中，我们需要追踪高阶同伦信息：
- 导出范畴是三角范畴，但丢失同伦类型信息
- 导出函子应有更高阶的凝聚结构

**$(\infty,1)$-范畴**:

- 对象间有映射空间（空间而非集合）
- 结合性仅成立到同伦
- 有更高阶的相干同伦

**模型**:

- **Quasi-categories** (Joyal, Lurie): simplicial set满足inner horn填充
- **Complete Segal spaces** (Rezk)
- **Simplicial categories**

**稳定无穷范畴**:

导出代数几何使用**稳定无穷范畴**（如谱范畴）：
- 有零对象
- 每个态射有纤维和余纤维
-  fiber sequences 等价于 cofiber sequences

**谱代数几何**:

更一般的框架，使用$E_\infty$-ring spectra：
- 包含拓扑K-理论、椭圆上同调等
- 与稳定同伦论有深刻联系

### 2.2 几何Langlands纲领

**算术Langlands纲领**:

数论中，Langlands纲领连接：
- Galois表示
- 自守形式
- 动机L-函数

**几何Langlands纲领**:

对于曲线$C$在代数闭域$k$上，连接：
- $^L G$-局部系统（$G$的Langlands对偶群）
- $G$-丛的D-模（或反常层）

**导出代数几何的角色**:

1. **Hecke算子**: 在导出范畴上作用
2. **范畴化**: 几何Langlands是范畴化的（2-范畴）
3. **量子化**: 形变量子化给出"量子"几何Langlands

**Arinkin-Gaitsgory奇异性条件**:

对于非约化群，需要允许奇异性。导出代数几何提供自然的框架处理：
- 导出Hecke范畴
- 导出几何Satake等价

**前沿发展**:

- **局部几何Langlands**: $p$-adic域上的类似理论
- **量子几何Langlands**: 包含Planck常数的形变
- **超Kähler方法**: 与3d N=4超对称QFT的联系

### 2.3 导出辛几何

**经典辛几何回顾**:

辛流形$(X, \omega)$有闭非退化2-形式$\omega \in \Omega^2(X)$。

**导出辛结构**:

Pantev-Toën-Vaquié-Vezzosi引入的**(-1)-辛结构**：
- 在导出Artin栈上
- 闭2-形式$\omega \in \mathcal{A}^{2,cl}(X, -1)$（权-1的闭形式）
- 诱导出$\mathbb{L}_X \simeq \mathbb{T}_X[-1]$（切复形与余切复形的等价）

**例子**:

1. **导出临界轨迹**: 对于函数$f$，有自然的(-1)-辛结构
2. **$BG$**: 约化群分类栈有(-1)-辛结构
3. **Hamiltonian约化**: 导出Hamiltonian约化保持(-1)-辛结构

**A-model与B-model**:

在导出辛几何中，有：
- **B-model**: 凝聚层（或矩阵因子化）的导出范畴
- **A-model**: Fukaya范畴（需进一步发展）

**应用**:

-  categorified Hall代数
-  3d N=4超对称理论的Higgs分支
-  Rozansky-Witten理论

---

## 3. 研究前沿 / Research Frontiers

### 3.1 凝聚态数学

**历史背景**:

"凝聚态数学"（Condensed Mathematics）由Dustin Clausen和Peter Scholze在2019年提出，旨在统一：
- 拓扑空间（分析）
- 代数几何（代数）

**凝聚集合**:

对于紧Hausdorff空间$S$，凝聚集合是在$\text{ProFin}_S$上的层。等价地，是light condensed set（在极不连续空间上）。

**凝聚环与凝聚代数几何**:

- 可以定义凝聚结构层
- 可以形成导出凝聚环（animated condensed ring）
- 几何对象：凝聚代数空间、凝聚栈

**优势**:

1. **分析-代数统一**: $\mathbb{R}$和$\mathbb{Z}_p$在统一框架中
2. **无交换性假设**: 自然地处理非交换几何
3. **导出构造**: 自然的导出框架

**应用**:

- $p$-adic Hodge理论的简化证明
- 黎曼-希尔伯特对应
- 固体模（solid modules）

### 3.2 完全相交上的矩阵因子化

**矩阵因子化**:

对于超曲面奇点$W: \mathbb{A}^n \to \mathbb{A}^1$，$W^{-1}(0)$的奇点范畴由**矩阵因子化**描述：

一对自由模$M, N$和态射：
$$M \xrightarrow{d_0} N \xrightarrow{d_1} M$$
满足$d_1 \circ d_0 = W \cdot \text{id}_M$，$d_0 \circ d_1 = W \cdot \text{id}_N$。

**Orlov的定理**:

对于孤立超曲面奇点，有范畴等价：
$$\text{MF}(W) \simeq D_{\text{sing}}^b(W^{-1}(0))$$

其中右边是奇点的导出范畴（凝聚层模完美复形）。

**完全交集的推广**:

对于完全交集$X = V(f_1, \ldots, f_c) \subset \mathbb{A}^n$，需要：
- **超矩阵因子化** (Eisenbud, 1980)
- **$\mathbb{Z}/2$-分级 dg-范畴**
- **矩阵因子化的范畴化**

**应用**:

1. **Landau-Ginzburg模型**: 矩阵因子化描述D-膜
2. **拓扑弦理论**: B-模型范畴化
3. **Knot homology**: Khovanov-Rozansky同调与矩阵因子化

### 3.3 高阶代数群与表示

**高阶群**:

在导出代数几何中，可以定义**高阶群**（higher groups）：
- 群对象是群的同伦类型
- $BG$是高阶栈
- 表示是$BG$上的层

**导出代数群**:

对于simplicial commutative ring $A$，可以定义群概形$G \to \text{dSpec}(A)$，其中群结构在同伦意义下。

**高阶表示论**:

- 高阶群的表示是谱范畴
- 可以发展特征标理论、诱导表示等
- 与拓扑量子场论的联系

**前沿方向**:

1. **2-表示论**: 群在范畴上的作用
2. **局部几何Langlands**: 高阶群在$p$-adic域上
3. **因子化代数**: E_n-代数与拓扑量子场论

**与物理的联系**:

- 规范场的导出描述
- 异常匹配（anomaly matching）
- 超对称代数的导出几何

---

## 4. 参考文献 / References

### 奠基性著作

1. **Toën, B. & Vezzosi, G.** - *Homotopical Algebraic Geometry I, II* (2005, 2008)
   - HAG I: Topos理论；HAG II: 导出代数几何的公理化

2. **Lurie, J.** - *Derived Algebraic Geometry* (博士论文, 2004)
   - 导出代数几何的系统发展

3. **Lurie, J.** - *Higher Algebra* (2017)
   - 无穷范畴与代数结构的标准参考

4. **Lurie, J.** - *Spectral Algebraic Geometry* (2018)
   - 谱代数几何的综合论述

### 专题著作

5. **Kontsevich, M.** - *Homological Algebra of Mirror Symmetry* (1994 ICM)
   - 同调镜像对称的奠基论文

6. **Pantev, T., Toën, B., Vaquié, M. & Vezzosi, G.** - *Shifted Symplectic Structures* (2013)
   - 导出辛几何的奠基论文

7. **Arinkin, D. & Gaitsgory, D.** - *Singular Support of Coherent Sheaves and the Geometric Langlands Conjecture* (2015)
   - 几何Langlands的导出方法

### 凝聚态数学

8. **Clausen, D. & Scholze, P.** - *Condensed Mathematics* (2019-2020)
   - 凝聚态数学的讲义

9. **Scholze, P.** - *Lectures on Condensed Mathematics* (2019)
   - 凝聚态数学的入门

10. **Mann, L.** - *A p-Adic 6-Functor Formalism in Rigid Analytic Geometry* (2022)
    - 凝聚态方法在$p$-adic几何中的应用

### 矩阵因子化与奇点

11. **Orlov, D.** - *Triangulated Categories of Singularities and D-Branes in Landau-Ginzburg Models* (2004)
    - 矩阵因子化与奇点范畴的等价

12. **Eisenbud, D.** - *Homological Algebra on a Complete Intersection, with an Application to Group Representations* (1980)
    - 矩阵因子化的起源

13. **Preygel, A.** - *Thom-Sebastiani & Duality for Matrix Factorizations* (2011)
    - 矩阵因子化的高级专题

### 综述与讲义

14. **Toën, B.** - *Derived Algebraic Geometry* (2014 EMS Surveys)
    - 导出代数几何的综述

15. **Calaque, D. & Grivaux, J.** - *A Survey on Brackets and Derived Geometry* (2022)
    - 导出几何与李理论的联系

16. **Porta, M. & Vezzosi, G.** - *The Loyola Symposium on Derived Algebraic Geometry* (2020)
    - 当代研究综述

### 在线资源

- [Kerodon](https://kerodon.net/) - Jacob Lurie的高阶代数资源
- [Geometric Langlands Seminar](https://math.mit.edu/research/pure/applied-sem-future.html) - 几何Langlands讲义
- [Derived Algebraic Geometry Seminar](https://math.berkeley.edu/~arinkin/) - Arinkin的DAG研讨班

---

**文档版本**: 1.0  
**维护者**: FormalMath项目  
**许可证**: CC BY-SA 4.0
