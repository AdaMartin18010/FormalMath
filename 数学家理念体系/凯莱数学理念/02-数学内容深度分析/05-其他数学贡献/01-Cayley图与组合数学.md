---
msc_primary: "05C25"
msc_secondary: ["05Cxx", "20F65", "20E08", "68R10"]
---

# Cayley图：群的几何表示与组合群论的开端

> **文档状态**: ✅ 新建（教学级/研究级）
> **创建日期**: 2026年4月3日
> **MSC分类**: 05C25 (群与图), 20F65 (几何群论)

---

## 📋 目录

- [Cayley图：群的几何表示与组合群论的开端](#cayley图群的几何表示与组合群论的开端)
  - [📋 目录](#-目录)
  - [一、历史背景：群论的几何化](#一历史背景群论的几何化)
    - [1.1 凯莱的早期图论工作](#11-凯莱的早期图论工作)
    - [1.2 从置换图到Cayley图](#12-从置换图到cayley图)
    - [1.3 德恩与组合群论的诞生](#13-德恩与组合群论的诞生)
  - [二、Cayley图的定义与基本性质](#二cayley图的定义与基本性质)
    - [2.1 形式化定义](#21-形式化定义)
    - [2.2 基本例子](#22-基本例子)
    - [2.3 作为图的性质](#23-作为图的性质)
  - [三、Cayley图与群的代数性质](#三cayley图与群的代数性质)
    - [3.1 顶点传递性](#31-顶点传递性)
    - [3.2 自同构群](#32-自同构群)
    - [3.3 Sabidussi定理](#33-sabidussi定理)
  - [四、群的Growth Function](#四群的growth-function)
    - [4.1 Growth Function的定义](#41-growth-function的定义)
    - [4.2 多项式增长与指数增长](#42-多项式增长与指数增长)
    - [4.3 Gromov多项式增长定理](#43-gromov多项式增长定理)
  - [五、在现代几何群论中的应用](#五在现代几何群论中的应用)
    - [5.1 字度量与几何性质](#51-字度量与几何性质)
    - [5.2 双曲群与负曲率](#52-双曲群与负曲率)
    - [5.3 自动群与有限状态自动机](#53-自动群与有限状态自动机)
  - [六、与计算机科学的联系](#六与计算机科学的联系)
    - [6.1 算法群论](#61-算法群论)
    - [6.2 在编码理论中的应用](#62-在编码理论中的应用)
    - [6.3 网络拓扑设计](#63-网络拓扑设计)
  - [七、数学公式总结](#七数学公式总结)
    - [核心公式](#核心公式)
  - [八、参考文献](#八参考文献)
    - [原始文献](#原始文献)
    - [几何群论经典](#几何群论经典)
    - [现代教材](#现代教材)
    - [Cayley图与网络](#cayley图与网络)
    - [计算群论](#计算群论)

---

## 一、历史背景：群论的几何化

### 1.1 凯莱的早期图论工作

**亚瑟·凯莱**在图论方面的工作起源于对**树**（tree）的计数问题。

**凯莱的树计数公式**（1857）：

具有$n$个标记顶点的树的数目为：

$$T_n = n^{n-2}$$

**例子**：

- $n = 2$：$T_2 = 2^{0} = 1$
- $n = 3$：$T_3 = 3^{1} = 3$
- $n = 4$：$T_4 = 4^{2} = 16$

这项工作是组合数学的经典结果，也是图论的开端之一。

### 1.2 从置换图到Cayley图

**Cayley图的诞生**：

虽然凯莱本人没有明确提出"Cayley图"这一概念，但他研究置换群时使用的图示方法蕴含了这一思想。

**关键发展**：

- **Burnside**（1897）：在《群论》一书中使用图示表示群作用
- **Dehn**（1910s）：将图用于研究群的字问题
- **Cayley图**这一名称在20世纪中期正式确立

### 1.3 德恩与组合群论的诞生

**Max Dehn**（1878-1952）是组合群论的创始人之一。

**德恩问题**（1911）：

给定群的有限表示$G = \langle S | R \rangle$，以下三个问题是基本的：

1. **字问题**（Word Problem）：给定字$w$，是否$w =_G 1$？
2. **共轭问题**（Conjugacy Problem）：给定字$u, v$，是否$u$与$v$共轭？
3. **同构问题**（Isomorphism Problem）：给定两个表示，是否定义同构的群？

**几何方法**：德恩引入**Cayley图**作为研究这些问题的几何工具。

---

## 二、Cayley图的定义与基本性质

### 2.1 形式化定义

**定义（Cayley图）**：

设$G$是一个群，$S$是$G$的一个**生成集**（generating set），且满足$1 \notin S$和$S = S^{-1}$（对逆封闭）。群$G$关于生成集$S$的**Cayley图**$\Gamma = \text{Cay}(G, S)$定义为：

- **顶点集**：$V(\Gamma) = G$
- **边集**：$E(\Gamma) = \{(g, gs) : g \in G, s \in S\}$

**有向 vs 无向**：

- 若$S$对逆封闭，Cayley图可以看作**无向图**
- 若不对逆封闭，则为**有向图**

### 2.2 基本例子

**例子1：无限循环群$\mathbb{Z}$**

取生成集$S = \{1, -1\}$，则$\text{Cay}(\mathbb{Z}, S)$是**双边无限路径**：

$$\cdots - 2 - 1 - 0 - 1 - 2 - \cdots$$

**例子2：有限循环群$\mathbb{Z}_n$**

取生成集$S = \{1, -1\}$，则$\text{Cay}(\mathbb{Z}_n, S)$是**n-循环图**$C_n$。

**例子3：克莱因四元群$V_4 = \{e, a, b, c\}$**

取生成集$S = \{a, b\}$（其中$c = ab$），Cayley图是：

```
    a ——— ab
    |     |
    e ——— b
```

这是一个**4-循环**。

**例子4：自由群$F_2$**

取生成集$S = \{a, b, a^{-1}, b^{-1}\}$，Cayley图是**4-正则树**。

**例子5：二面体群$D_4$**

取生成集$S = \{r, s\}$（$r$为旋转，$s$为反射），Cayley图是一个8顶点的图，反映了正方形的对称性。

### 2.3 作为图的性质

**基本性质**：

**定理**：设$\Gamma = \text{Cay}(G, S)$，则：

1. **连通性**：$\Gamma$连通当且仅当$S$生成$G$
2. **正则性**：$\Gamma$是$|S|$-正则图
3. **顶点数**：$|V(\Gamma)| = |G|$
4. **边数**：$|E(\Gamma)| = \frac{1}{2}|G||S|$（对无向图）

**证明**：

1. 连通性：两点$g, h$之间有路径当且仅当$g^{-1}h$可表示为$S$中元素的乘积。
2. 正则性：每个顶点$g$的邻居为$\{gs : s \in S\}$，共$|S|$个。

---

## 三、Cayley图与群的代数性质

### 3.1 顶点传递性

**定义**：图$\Gamma$是**顶点传递的**（vertex-transitive），如果对任意$u, v \in V(\Gamma)$，存在自同构$\varphi$使得$\varphi(u) = v$。

**定理**：Cayley图是顶点传递的。

**证明**：对任意$h \in G$，定义**左平移**：

$$L_h: G \to G, \quad L_h(g) = hg$$

$L_h$是$\text{Cay}(G, S)$的自同构，因为对任意边$(g, gs)$：

$$L_h(g) = hg, \quad L_h(gs) = hgs$$

且$(hg, hgs)$也是边。

由于左平移传递作用在$G$上，Cayley图是顶点传递的。

### 3.2 自同构群

**定义**：图$\Gamma$的**自同构群**记为$\text{Aut}(\Gamma)$。

**定理**：对于$\Gamma = \text{Cay}(G, S)$：

$$G \leq \text{Aut}(\Gamma)$$

即$G$可以嵌入到$\Gamma$的自同构群中（通过左平移作用）。

**例子**：$\text{Cay}(\mathbb{Z}_n, \{1, -1\}) = C_n$

$$\text{Aut}(C_n) = D_n \text{（二面体群）}$$

而$\mathbb{Z}_n \leq D_n$对应于旋转子群。

### 3.3 Sabidussi定理

**定理（Sabidussi, 1958）**：

一个图$\Gamma$是Cayley图当且仅当$\text{Aut}(\Gamma)$包含一个作用正则（regularly）在顶点上的子群。

**意义**：

- 给出了Cayley图的**群论刻画**
- 可用于判断一个图是否为Cayley图

**正则作用**：群$G$作用在集合$X$上是**正则的**，如果它是**传递且自由**的（即$|G| = |X|$且稳定化子是平凡的）。

---

## 四、群的Growth Function

### 4.1 Growth Function的定义

**定义**：设$G$是有限生成群，$S$是有限生成集。定义**增长函数**：

$$\gamma_S(n) = |B_S(n)|$$

其中$B_S(n) = \{g \in G : |g|_S \leq n\}$是以单位元为中心、半径为$n$的**球**，$|g|_S$是字$g$关于生成集$S$的**字长**。

**等价表述**：$\gamma_S(n)$是Cayley图$\text{Cay}(G, S)$中以单位元为起点、长度不超过$n$的路径的终点数目。

### 4.2 多项式增长与指数增长

**增长类型分类**：

**定义**：两个增长函数$\gamma_1, \gamma_2$是**等价**的，如果存在$C > 1$使得：

$$\gamma_1(n) \leq \gamma_2(Cn), \quad \gamma_2(n) \leq \gamma_1(Cn)$$

**定理**：增长函数的等价类与生成集的选择无关。

**增长类型**：

| 类型 | 定义 | 例子 |
|------|------|------|
| **常数增长** | $\gamma(n) \sim 1$ | 有限群 |
| **线性增长** | $\gamma(n) \sim n$ | $\mathbb{Z}$ |
| **二次增长** | $\gamma(n) \sim n^2$ | $\mathbb{Z}^2$ |
| **多项式增长** | $\gamma(n) \leq Cn^d$ | $\mathbb{Z}^d$ |
| **指数增长** | $\gamma(n) \sim a^n$ ($a > 1$) | 自由群$F_2$ |

**例子**：

1. **$\mathbb{Z}^d$**：$\gamma(n) = (2n+1)^d \sim n^d$（多项式增长）

2. **自由群$F_k$**：$\gamma(n) = 1 + 2k \sum_{i=0}^{n-1}(2k-1)^i \sim (2k-1)^n$（指数增长）

### 4.3 Gromov多项式增长定理

**定理（Gromov, 1981）**：

一个有限生成群具有多项式增长当且仅当它包含一个有限指数的**幂零子群**。

**历史意义**：

- 连接了群的几何性质（增长）与代数性质（幂零性）
- Gromov因此获得2009年阿贝尔奖
- 启发了几何群论的蓬勃发展

**应用**：

- 分类多项式增长群
- 研究大尺度几何性质
- 与遍历理论和微分几何的联系

---

## 五、在现代几何群论中的应用

### 5.1 字度量与几何性质

**字度量**（Word Metric）：

对于生成集$S$，定义$G$上的度量：

$$d_S(g, h) = |g^{-1}h|_S$$

**几何解释**：$d_S(g, h)$是Cayley图中从$g$到$h$的最短路径长度。

**拟等距**（Quasi-isometry）：

两个度量空间是**拟等距**的，如果它们的大尺度几何相似。

**定理**：有限生成群的不同生成集给出的字度量是拟等距的。

### 5.2 双曲群与负曲率

**双曲群**（Hyperbolic Groups）：

**Gromov**（1987）引入双曲群的概念。

**定义**：群$G$是**双曲的**，如果其Cayley图是Gromov双曲的（满足薄三角形条件）。

**几何意义**：Cayley图具有**负曲率**的大尺度几何性质。

**性质**：

- 双曲群具有可解的字问题
- 共轭问题可解
- 边界理论丰富

**例子**：

- 自由群是双曲的
- 有限群是双曲的
- $\mathbb{Z}^n$（$n \geq 2$）不是双曲的（平坦几何）

### 5.3 自动群与有限状态自动机

**自动群**（Automatic Groups）：

**定义**：群$G$是**自动的**，如果存在有限状态自动机来识别：

1. 群元素的正则语言表示
2. 乘法运算的自动机

**定理（Cannon, Thurston等，1980s）**：

- 双曲群是自动的
- Coxeter群是自动的
- braid群是自动的

**应用**：

- 高效计算群运算
- 解决字问题
- 与计算机科学的联系

---

## 六、与计算机科学的联系

### 6.1 算法群论

**计算问题**：

在算法群论中，Cayley图提供了群计算的**几何框架**。

**基本算法**：

1. **字问题算法**：判断$w =_G 1$
2. **成员资格问题**：判断$g \in H$（$H \leq G$）
3. **共轭问题算法**：判断$u \sim_G v$

**Cayley图方法**：

- 在Cayley图上进行**广度优先搜索**
- 使用**Schreier图**研究子群
- **自动机方法**处理正则语言

### 6.2 在编码理论中的应用

**Cayley图与编码**：

Cayley图可以用来构造**纠错码**。

**构造方法**：

1. 取群$G$和生成集$S$
2. 考虑Cayley图的**邻接矩阵**$A$
3. 利用$A$的特征值构造**图码**（graph codes）

**例子**：

- **Kerdock码**可以用Cayley图描述
- **Reed-Muller码**与Cayley图有关

### 6.3 网络拓扑设计

**互连网络**（Interconnection Networks）：

Cayley图在网络拓扑设计中有重要应用：

**优点**：

1. **对称性**：顶点传递，负载均衡
2. **可扩展性**：容易添加新节点
3. **容错性**：多条路径保证可靠性

**应用实例**：

- **环形网络**：$\text{Cay}(\mathbb{Z}_n, \{1, -1\})$
- **超立方体**：$\text{Cay}(\mathbb{Z}_2^d, \{e_1, \ldots, e_d\})$
- **星形图**：$\text{Cay}(S_n, \{(12), (13), \ldots, (1n)\})$

**性能指标**：

- **直径**：$\text{diam}(\Gamma) = \max_{u,v} d(u,v)$
- **度数**：与硬件成本相关
- **连通度**：与容错性相关

---

## 七、数学公式总结

### 核心公式

**1. 凯莱树计数公式**：
$$T_n = n^{n-2}$$

**2. 增长函数**：
$$\gamma_S(n) = |\{g \in G : |g|_S \leq n\}|$$

**3. 字度量**：
$$d_S(g, h) = |g^{-1}h|_S$$

**4. Cayley图的边数**：
$$|E| = \frac{1}{2}|G||S|$$

**5. 自由群的增长**：
$$\gamma_{F_k}(n) = 1 + 2k \frac{(2k-1)^n - 1}{2k-2}$$

**6. 幂零群的Growth**：
$$\gamma(n) \sim n^{d(G)}$$

其中$d(G)$是幂零群的**维数**。

---

## 八、参考文献

### 原始文献

1. **Cayley, A.** (1857). "On the Theory of the Analytical Forms Called Trees". *Philosophical Magazine*, 13: 172-176.

2. **Cayley, A.** (1878). "Desiderata and Suggestions: No. 1. The Theory of Groups". *American Journal of Mathematics*, 1: 50-52.

3. **Cayley, A.** (1889). "On the Theory of Groups". *American Journal of Mathematics*, 11: 139-157.

4. **Dehn, M.** (1911). "Über unendliche diskontinuierliche Gruppen". *Mathematische Annalen*, 71: 116-144.

### 几何群论经典

1. **Gromov, M.** (1981). "Groups of Polynomial Growth and Expanding Maps". *Publications Mathématiques de l'IHÉS*, 53: 53-73.

2. **Gromov, M.** (1987). "Hyperbolic Groups". In *Essays in Group Theory* (S. M. Gersten, ed.), MSRI Publications, 8: 75-263.

3. **de la Harpe, P.** (2000). *Topics in Geometric Group Theory*. University of Chicago Press.

### 现代教材

1. **Epstein, D. B. A., Cannon, J. W., Holt, D. F., et al.** (1992). *Word Processing in Groups*. Jones and Bartlett.

2. **Lyndon, R. C., & Schupp, P. E.** (2001). *Combinatorial Group Theory*. Springer.

3. **Magnus, W., Karrass, A., & Solitar, D.** (2004). *Combinatorial Group Theory* (2nd ed.). Dover.

### Cayley图与网络

1. **Heydemann, M. C.** (1997). "Cayley Graphs and Interconnection Networks". In *Graph Symmetry* (Hahn & Sabidussi, eds.), NATO ASI Series, 497: 167-224.

2. **Lakshmivarahan, S., Jwo, J. S., & Dhall, S. K.** (1993). "Symmetry in Interconnection Networks Based on Cayley Graphs of Permutation Groups: A Survey". *Parallel Computing*, 19: 361-407.

### 计算群论

1. **Sims, C. C.** (1994). *Computation with Finitely Presented Groups*. Cambridge University Press.

2. **Erickson, J.** (2020). *Computational Topology*. Course Notes, University of Illinois.

---

**文档状态**: ✅ 完成（教学级/研究级）
**字数**: 约4,200字
**数学公式数**: 15+
**完成度**: 100%
**最后更新**: 2026年4月3日
