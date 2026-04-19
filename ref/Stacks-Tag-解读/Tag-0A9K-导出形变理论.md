---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0A9K - 导出形变理论

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0A9K |
| **英文名称** | Derived Deformation Theory |
| **所属章节** | Deformation Theory |
| **主题分类** | 高阶代数几何 - 导出几何 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 导出形变理论的动机

传统形变理论研究对象的无穷小变形，但无法捕捉**高阶形变**（obstructions, higher homotopies）。**导出形变理论**（Derived Deformation Theory, DDT）通过引入**导出代数几何**（Derived Algebraic Geometry）的工具，提供了更完整的理论框架。

### 2.2 关键定义

**定义 2.2.1**（单纯交换环）
**单纯交换环**（Simplicial Commutative Ring）是一个函子：

$$A_\bullet: \Delta^{\text{op}} \to \text{CRing}$$

其中 $\Delta$ 是单纯范畴。

**定义 2.2.2**（导出环）
一个**导出环**（Derived Ring）$A$ 是单纯交换环的同伦等价类。其**底层普通环**为：

$$\pi_0(A) = H_0(A_\bullet)$$

**定义 2.2.3**（导出Artin环）
一个导出环 $A$ 是**Artin**的，如果：
- $\pi_0(A)$ 是Artin局部环
- 每个 $\pi_i(A)$ 是有限生成的 $\pi_0(A)$-模
- $\pi_i(A) = 0$ 对于 $i \gg 0$

**定义 2.2.4**（导出形变函子）
一个**导出形变函子**是一个保持拉回的正合∞-函子：

$$F: \text{dArt}_k^{\text{op}} \to \mathcal{S}$$

其中 $\mathcal{S}$ 是空间（space）的∞-范畴。

### 2.3 切复形

**定义 2.3.1**（导出切空间）
对于导出形变函子 $F$，其**切复形**定义为：

$$\mathbb{T}_F := F(k[\epsilon]/\epsilon^2)$$

其中 $k[\epsilon]/\epsilon^2$ 是双数环（视为离散导出环）。

更一般地，对于Artin环 $A$ 和 $M \in D^{\leq 0}(A)$，定义：

$$\mathbb{T}_F(A; M) := F(A \oplus M)$$

---

## 3. 主要结果与定理

### 3.1 导出形变理论的基本定理

**定理 3.1.1**（Tag 0A9K）
设 $F$ 是导出形变函子，则：

**(a) 切复形存在性**
存在**切复形** $\mathbb{T}_F \in D(k)$ 使得：

$$F(k \oplus M) \cong \text{Map}_{D(k)}(\mathbb{T}_F, M[1])$$

**(b) 阻碍理论**
对于扩张 $0 \to M \to \tilde{A} \to A \to 0$，存在**阻碍类**：

$$\omega \in \text{Ext}^2(\mathbb{L}_F, M) = \pi_0\text{Map}(\mathbb{T}_F, M[2])$$

使得 $\omega = 0$ 当且仅当形变存在。

**(c) 形变空间**
若阻碍消失，形变空间是torsor：

$$\text{Def}(\tilde{A}/A) \cong \text{Map}(\mathbb{T}_F, M[1])$$

### 3.2 Lurie-Pridham定理

**定理 3.2.1**（导出形变理论的等价性）
存在等价∞-范畴：

$$\{\text{导出形变函子}/k\} \cong \{\text{微分分次Lie代数}/k\}$$

具体地，对应关系为：

$$F \longleftrightarrow \mathfrak{g}_F = \mathbb{T}_F[-1]$$

其中Lie括号由形变环的交换性导出。

### 3.3 谱序列

**定理 3.3.1**（形变谱序列）
对于导出形变问题，存在谱序列：

$$E_2^{p,q} = H^p(\mathfrak{g}_F \otimes M) \Rightarrow \pi_{-p-q}F(A \oplus M)$$

这统一了传统形变理论中的切空间、阻碍空间和自同构群。

---

## 4. 证明思路

### 4.1 ∞-范畴的框架

**步骤1**：导出环的模
- 导出环 $A$ 的模形成稳定∞-范畴 $\text{Mod}_A$
- 这与微分分次模的∞-范畴等价

**步骤2**：形变函子的正合性
- 保持拉回 ⟹ 保持纤维积
- 这自动编码了同伦相干信息

### 4.2 切复形的构造

**核心观察**：
形变函子在 $k$ 处的切复形可通过**Goodwillie微积分**理解：

$$\mathbb{T}_F = \Omega^\infty \circ \partial F(k)$$

其中 $\partial F$ 是Goodwillie导数。

### 4.3 Lie代数结构的来源

**Deligne群胚的导出版本**：
对于dg Lie代数 $\mathfrak{g}$，其形变群胚为：

$$\text{Def}_{\mathfrak{g}}(A) = \text{MC}(\mathfrak{g} \otimes \mathfrak{m}_A) / \exp(\mathfrak{g}^0 \otimes \mathfrak{m}_A)$$

其中MC是Maurer-Cartan方程的解空间。

---

## 5. 应用与例子

### 5.1 导出形变的例子

**例子 5.1.1**（导出概形）
设 $X$ 是光滑真簇，考虑其**导出形变函子**：

$$\text{Def}_X^{\text{der}}(A) = \{\text{导出平坦态射 } \mathcal{X} \to \text{Spec}(A) \text{ 带有 } \mathcal{X} \times_A k \cong X\}$$

对于光滑簇，这与传统形变一致。但对于奇异簇，导出形变可能更丰富。

**例子 5.1.2**（导出向量丛）
向量丛的导出形变：

$$\text{Def}_E(A) = \text{BPerf}(X_A)^{\cong E}$$

这捕捉了复形的形变，不仅是单层的形变。

### 5.2 量子化中的应用

**应用 5.2.1**（形变量子化）
导出形变理论为形变量子化提供了自然框架：

- **经典数据**：Poisson流形 $(M, \pi)$
- **量子数据**：星积 $\star_\hbar$
- **导出视角**：$\text{Def}_{\text{Quant}} \leftrightarrow \text{Shifted Poisson结构}$

Kontsevich形式性定理的导出解释：

$$\mathfrak{g}_{\text{Poly}} \sim \mathfrak{g}_{\text{Poly}}^{(0)} = T_{\text{poly}}$$

### 5.3 镜像对称

**应用 5.3.1**（SYZ镜像对称）
在SYZ构造中，导出形变理论对应于：

| A-模型 | B-模型 |
|--------|--------|
| Fukaya范畴 $D^\pi\text{Fuk}(X)$ | 凝聚层 $D^b\text{Coh}(\check{X})$ |
| 导出形变（A-无穷结构） | 复结构形变 |

### 5.4 高阶模空间

**应用 5.4.1**（导出模空间）
传统模空间往往奇异。导出代数几何提供**导出模空间**（Derived Moduli Spaces）：

$$\mathcal{M}^{\text{der}} = \text{Map}(X, Y)^{\text{der}}$$

其切复形正是通常的Obstruction Theory所需的复形。

---

## 6. 与其他概念的关系

### 6.1 形变理论的演进

```
    经典形变理论 (Kodaira-Spencer)
              │
              │ 奇异/障碍情形
              ▼
    阻碍理论 (Mumford, Artin)
              │
              │ 高阶同伦
              ▼
    导出形变理论 (Lurie, Pridham)
              │
              │ 几何化
              ▼
    导出代数几何
```

### 6.2 与导出代数几何的关系

**导出概形**（Derived Schemes）：

- 局部模型：$\text{Spec}(A)$，$A$ 是单纯交换环
- 结构层：$\mathcal{O}_X$ 取值于导出环
- 截断：$t_0(X) = (X, \pi_0\mathcal{O}_X)$ 是通常概形

### 6.3 与拓扑场论的联系

**Batalin-Vilkovisky形式化**：
导出形变理论中的Lie代数结构与量子场论中的BV形式化密切相关：

$$\mathfrak{g}[1] \cong \text{Obs}^{\text{cl}} \leadsto \text{Obs}^q$$

---

## 7. 参考文献

### 7.1 奠基文献

1. **Lurie, J.** (2011). *Derived Algebraic Geometry X: Formal Moduli Problems*
   - 导出形变理论的系统发展
   - Lurie-Pridham定理

2. **Pridham, J.P.** (2013). *Unifying derived deformation theories*
   - Adv. Math. 224
   - 具体构造与证明

3. **Manetti, M.** (2009). *Differential graded Lie algebras and formal deformation theory*
   - 经典到导出的桥梁

### 7.2 应用文献

4. **Toën, B.** (2014). *Derived Algebraic Geometry*
   - EMS Surv. Math. Sci.
   - 全面概述

5. **Calaque, D. & Grivaux, J.** (2015). *Formal moduli problems and formal derived stacks*
   - 具体应用

6. **Pantev, T. et al.** (2013). *Shifted symplectic structures*
   - Publ. Math. IHÉS
   - 导出辛几何

### 7.3 相关领域

7. **Kontsevich, M.** (2003). *Deformation quantization of Poisson manifolds*
   - 形变量子化的导出视角

8. **Costello, K.** (2013). *Quantization of derived algebraic varieties*
   - 量子场论的联系

### 7.4 在线资源

9. **Stacks Project**: [Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
10. **Kerodon**: [Derived Deformation Theory](https://kerodon.net/)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0A9L](#tag-0a9l) | 导出Hilbert概形 | 具体应用 |
| [0G6Y](#tag-0g6y) | 形式形变理论 | 经典版本 |
| [0G6Z](#tag-0g6z) | 阻碍理论 | 技术基础 |

### 8.2 导出几何

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G70](#tag-0g70) | 导出概形 | 几何基础 |
| [0G71](#tag-0g71) | 导出叠 | 全局化 |
| [0G72](#tag-0g72) | 谱代数几何 | 非交换推广 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G73](#tag-0g73) | 导出辛几何 | 几何应用 |
| [0G74](#tag-0g74) | 形变量子化 | 物理应用 |
| [0G75](#tag-0g75) | 高阶模空间 | 具体构造 |

---

## 附录：技术要点

### dg Lie代数与形变

**Maurer-Cartan方程**：

$$dx + \frac{1}{2}[x, x] = 0, \quad x \in \mathfrak{g}^1 \otimes \mathfrak{m}_A$$

**Deligne群胚**：
- 对象：MC方程的解
- 态射：$\exp(\mathfrak{g}^0)$ 的规范作用

### 单纯Artin环的例子

**二阶导出延拓**：

$$A = k[\epsilon_1, \epsilon_2]/(\epsilon_1^2, \epsilon_2^2, \epsilon_1\epsilon_2 = \eta)$$

其中 $\deg(\epsilon_i) = 0$，$\deg(\eta) = -1$，$d\eta = 0$。

这编码了高阶形变信息。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
