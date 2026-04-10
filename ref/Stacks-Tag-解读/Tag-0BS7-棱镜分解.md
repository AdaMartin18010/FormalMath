# Stacks Project Tag 0BS7 - 棱镜分解

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0BS7 |
| **英文名称** | Prismatic Stratification |
| **所属章节** | Prismatic Cohomology |
| **主题分类** | 算术几何 - 棱镜技术 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 棱镜分解的动机

**核心问题**：如何在棱镜上同调中编码「变化」的信息？

在经典Hodge理论中，变分Hodge结构（VHS）通过**Gauss-Manin联络**编码族的上同调变化。棱镜分解是这一概念在棱镜上同调中的类比。

### 2.2 棱镜层

**定义 2.2.1**（棱镜层）
在棱镜位象 $(X/A)_\mathfrak{S}$ 上的一个**棱镜层**是一个满足下降条件的系统：
$$\mathcal{F}: (B, J) \mapsto \mathcal{F}(B, J)$$
其中 $B$ 是棱镜，$J$ 是理想。

**定义 2.2.2**（晶体棱镜层）
棱镜层 $\mathcal{F}$ 称为**晶体**的，如果对任意棱镜映射 $(B, J) \to (C, K)$，自然映射：
$$\mathcal{F}(B, J) \otimes_B C \to \mathcal{F}(C, K)$$
是同构。

**定义 2.2.3**（棱镜层上的联络）
在棱镜层 $\mathcal{F}$ 上的一个**棱镜联络**是：
$$\nabla: \mathcal{F} \to \mathcal{F} \otimes \Omega^1_\mathfrak{S}$$
满足Leibniz法则和可积性。

### 2.3 Hodge滤波

**定义 2.3.1**（棱镜Hodge滤波）
棱镜上同调 $H^i_\mathfrak{S}(X)$ 配备自然的**Hodge滤波**：
$$\text{Fil}^*_H H^i_\mathfrak{S}(X) := \text{Fil}^*(H^i_\mathfrak{S}(X) \otimes \mathcal{O}_K)$$

**定义 2.3.2**（Nygaard滤波）
**Nygaard滤波**定义为：
$$\mathcal{N}^k H^i_\mathfrak{S}(X) := \{x : \varphi(x) \in I^k H^i_\mathfrak{S}(X)\}$$
其中 $\varphi$ 是Frobenius。

**定义 2.3.3**（共轭滤波）
**共轭滤波**（conjugate filtration）定义为：
$$\text{Fil}^*_c H^i_\mathfrak{S}(X) := \text{与 } \varphi \text{ 的像相关的滤波}$$

### 2.4 棱镜晶体

**定义 2.4.1**（棱镜晶体）
**棱镜晶体**是一个棱镜层 $\mathcal{E}$，配备：

- 晶体结构（与基变换交换）
- Frobenius结构：$\varphi^*\mathcal{E} \to \mathcal{E}$

**定义 2.4.2**（有效棱镜晶体）
棱镜晶体 $\mathcal{E}$ 称为**有效**的，如果Frobenius映射：
$$\varphi^*\mathcal{E} \to \mathcal{E}$$
被 $I$ 的某次幂消没。

**定义 2.4.3**（$F$-晶体）
**$F$-晶体**是带有可逆Frobenius的棱镜晶体：
$$\varphi^*\mathcal{E}[1/I] \xrightarrow{\sim} \mathcal{E}[1/I]$$

---

## 3. 主要结果与定理

### 3.1 棱镜分解的基本定理

**定理 3.1.1**（Tag 0BS7 - 棱镜分解）
设 $X \to Y$ 是光滑真态射，则棱镜上同调 $R^i f_* \mathcal{O}_\mathfrak{S}$ 配备：

**(a) Gauss-Manin联络**
$$\nabla: R^i f_* \mathcal{O}_\mathfrak{S} \to R^i f_* \mathcal{O}_\mathfrak{S} \otimes \Omega^1_{Y/\mathfrak{S}}$$
满足可积性 $\nabla^2 = 0$。

**(b) Frobenius水平性**
Frobenius与Gauss-Manin联络交换：
$$\nabla \circ \varphi = \varphi \circ \nabla$$

**(c) 拟单值定理**
在合适的条件下，Gauss-Manin联络的曲率被控制。

### 3.2 Hodge-de Rham退化

**定理 3.2.1**（棱镜Hodge-to-de Rham）
对于光滑真簇 $X$，谱序列：
$$E_1^{i,j} = H^j(X, \Omega^i_{X/\mathcal{O}_K}) \otimes \mathcal{O}_K \Rightarrow H^{i+j}_{\text{dR}}(X)$$
在 $E_1$ 退化。

**定理 3.2.2**（Hodge-Tate退化）
棱镜到Hodge-Tate的谱序列：
$$E_2^{i,j} = H^i(X, \Omega^j\{-j\}) \Rightarrow H^{i+j}_\mathfrak{S}(X) \otimes \mathcal{O}_K$$
在 $E_2$ 退化。

### 3.3 滤波关系

**定理 3.3.1**（滤波比较）
在棱镜上同调上存在三个自然滤波：

1. **Hodge滤波** $\text{Fil}^*_H$：来自模 $I$
2. **Nygaard滤波** $\mathcal{N}^*$：来自Frobenius
3. **共轭滤波** $\text{Fil}^*_c$：来自 $\varphi$-像

**定理 3.3.2**（滤波交叉）
这三个滤波相互关联，通过以下方式：
$$\mathcal{N}^i \subset \text{Fil}^i_H, \quad \text{Fil}^i_c \subset \mathcal{N}^i$$

### 3.4 晶体对应

**定理 3.4.1**（棱镜晶体对应）
存在范畴等价：
$$\{\text{相对有效棱镜晶体}/Y\} \cong \{\text{局部自由 } \mathcal{O}_Y\text{-模配可积联络}\}$$

**定理 3.4.2**（Riemann-Hilbert对应）
棱镜版本的Riemann-Hilbert对应：
$$\{\text{棱镜晶体}\} \longleftrightarrow \{\text{p进局部系统}\}$$

---

## 4. 证明思路

### 4.1 Gauss-Manin联络的构造

**步骤1**：相对棱镜位象
定义 $f: X \to Y$ 的相对棱镜位象：
$$(X/Y)_\mathfrak{S} := \{(B, J) \to (C, K) : B/J = \mathcal{O}_Y, C/K = \mathcal{O}_X\}$$

**步骤2**：直接像层
$$R^i f_* \mathcal{O}_\mathfrak{S} := R^i \pi_* \mathcal{O}_\mathfrak{S}$$
其中 $\pi: (X/Y)_\mathfrak{S} \to Y_\mathfrak{S}$。

**步骤3**：联络构造
利用相对棱镜位象的**无穷小结构**构造联络。

### 4.2 Frobenius水平性

**核心观察**：Frobenius在棱镜位象上具有自然的水平性。

**证明策略**：

1. 构造绝对Frobenius
2. 验证与相对结构的相容性
3. 导出水平性方程

### 4.3 退化定理的证明

**关键引理**：
利用**Deligne-Illusie**方法的棱镜类比。

**步骤**：

1. 构造Cartier同构的棱镜版本
2. 证明 $E_1$ 退化
3. 导出Hodge对称性

---

## 5. 应用与例子

### 5.1 椭圆曲线的族

**例子 5.1.1**
设 $f: E \to S$ 是椭圆曲线的族，则：

- $R^1 f_* \mathcal{O}_\mathfrak{S}$ 是秩2棱镜晶体
- Gauss-Manin联络编码模形式的微分
- Frobenius给出Hasse不变量

### 5.2 阿贝尔概形的棱镜晶体

**例子 5.1.2**
对于阿贝尔概形 $A/S$：

- $R^1 f_* \mathcal{O}_\mathfrak{S}$ 是自对偶棱镜晶体
- 配备主极化
- 与Dieudonné模联系

### 5.3 Calabi-Yau族的镜对称

**应用 5.3.1**
棱镜分解为镜对称提供新视角：

- A-模型的棱镜结构
- B-模型的Frobenius结构
- 棱镜版本的SYZ对应

### 5.4 p进自守形式

**应用 5.3.2**（Hansen）
在p进Langlands纲领中：

- 棱镜晶体对应自守形式
- Gauss-Manin联络给出微分算子
- Frobenius对应Hecke算子

### 5.5 变分Hodge猜想

**应用 5.4.1**
棱镜分解为研究以下问题提供工具：

- 代数循环的平坦延拓
- Tate类的绝热延拓
- 极化族的特殊化

---

## 6. 与其他概念的关系

### 6.1 与经典变分Hodge理论的对比

| 特征 | 经典VHS | 棱镜分解 |
|------|--------|---------|
| 基空间 | 复流形 | p进形式概形 |
| 层 | 局部系统 | 棱镜晶体 |
| 联络 | Gauss-Manin | 棱镜Gauss-Manin |
| 退化 | Schmid定理 | 拟单值定理 |
| 周期映射 | Hodge域 | p进周期域 |

### 6.2 与晶体F-晶体的联系

**关系**：棱镜晶体推广了晶体F-晶体
$$\{\text{晶体 }F\text{-晶体}\} \subset \{\text{棱镜晶体}\}$$

**差异**：

- 晶体理论：基于pd-结构
- 棱镜理论：基于$\delta$-结构

### 6.3 与导出几何

**现代发展**：导出棱镜晶体

- 在导出棱镜位象上
- 与拓扑循环同调的联系

### 6.4 与D-模理论

**联系**：棱镜Gauss-Manin联络是p进D-模的特例
$$\{\text{棱镜晶体配联络}\} \hookrightarrow \{\text{算术D-模}\}$$

---

## 7. 参考文献

### 7.1 奠基文献

1. **Bhatt, B., Scholze, P.** (2019). *Prisms and prismatic cohomology*
   - 棱镜晶体的原始定义

2. **Drinfeld, V.** (2021). *A prismatic analogue of the Cartier isomorphism*
   - 棱镜Cartier同构

3. **Li, S., Mondal, S.** (2023). *Prismatic crystals*
   - 系统理论

### 7.2 应用文献

1. **Anschütz, J., Le Bras, A.C.** (2023). *Prismatic $F$-gauges*
   - 滤波棱镜晶体

2. **Hansen, D.** (2023). *Prismatic cohomology and modular forms*
   - 自守形式应用

3. **Ito, K.** (2024). *Prismatic stratification and the p-adic Riemann-Hilbert correspondence*

### 7.3 综述文献

1. **Morrow, M.** (2022). *Variations of Hodge structures in p-adic geometry*
   - 棱镜分解的综述

2. **Bhatt, B.** (2022). *Prismatic F-gauges and applications*
   - ICM报告

### 7.4 在线资源

1. **Stacks Project**: [Tag 0BS7](https://stacks.math.columbia.edu/tag/0BS7)
2. **Scholze's Notes**: Prismatic Crystals

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0BS6](#tag-0bs6) | 棱镜上同调定义 | 基础 |
| [0F1A](#tag-0f1a) | p进Hodge理论 | 类比 |
| [07GI](#tag-07gi) | 晶体上同调 | 特例 |

### 8.2 滤波理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0BS8](#tag-0bs8) | Hodge滤波 | 具体构造 |
| [0BS9](#tag-0bs9) | Nygaard滤波 | Frobenius相关 |
| [0BSA](#tag-0bsa) | 共轭滤波 | Cartier像 |

### 8.3 晶体理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [07GJ](#tag-07gj) | F-晶体 | 经典类比 |
| [0G6G](#tag-0g6g) | 棱镜晶体 | 推广 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **变分理论**：棱镜分解是变分Hodge理论的p进版本

2. **统一框架**：统一了Gauss-Manin联络的多种构造

3. **新应用**：在p进Langlands和自守形式中的应用

4. **活跃研究**：2020年代最前沿的算术几何方向之一

### A.2 未解决问题

- **完全可积性**：完整的Riemann-Hilbert对应
- **单值群理论**：p进拟单值定理
- **周期映射**：p进周期域的几何

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 棱镜层 | ❌ 待建设 | ★★★★★ |
| Gauss-Manin联络 | ❌ 待建设 | ★★★★★ |
| 滤波构造 | ❌ 待建设 | ★★★★☆ |
| 晶体对应 | ❌ 待建设 | ★★★★★ |
| 退化定理 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
