---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0B2C - 完美胚空间定义

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0B2C |
| **英文名称** | Definition of Perfectoid Spaces |
| **所属章节** | Perfectoid Spaces |
| **主题分类** | p进几何 - 完美胚空间 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 历史背景与革命性意义

**完美胚空间**（Perfectoid Spaces）由Peter Scholze于2011年博士论文中引入，是21世纪代数几何最具革命性的概念之一。它统一了p进几何中的多个领域，特别是解决了**权重单值化猜想**（Weight Monodromy Conjecture）等难题。

**核心洞察**：在p进几何中，特征 $p$ 和特征 $0$ 之间存在深刻的联系，通过**倾斜**（tilting）可以实现特征的转换。

### 2.2 完美胚环

**定义 2.2.1**（完美环）
特征 $p$ 环 $R$ 称为**完美**的，如果Frobenius映射 $\varphi: R \to R$，$x \mapsto x^p$ 是同构。

等价地：
$$R \cong \varprojlim_{\varphi} R$$

**定义 2.2.2**（完美胚环）
完备赋值环 $(R, |\cdot|)$ 称为**完美胚**的，如果：
- $R$ 是**一致**（uniform）的：$R^\circ$ 有界
- 存在伪一致化子 $\varpi \in R$ 使得 $\varpi^p \mid p$ 在 $R^\circ$ 中
- $R$ 是**完美**的（tilt后）

**定义 2.2.3**（tilt构造）
对于完备赋值环 $R$，其**tilt**定义为：
$$R^\flat := \varprojlim_{x \mapsto x^p} R$$
带有投影值：
$$x^\sharp := \lim_{n \to \infty} x_n^{p^n} \in R$$

### 2.3 完美胚空间

**定义 2.3.1**（完美胚代数簇）
**完美胚代数簇**（Perfectoid Affinoid）是
$$X = \text{Spa}(R, R^+)$$
其中 $(R, R^+)$ 是完美胚Huber对。

**定义 2.3.2**（完美胚空间）
**完美胚空间**是一个解析adic空间，局部同构于完美胚代数簇的有限并。

等价地：
- 被完美胚代数簇覆盖
- 结构层 $\mathcal{O}_X$ 的完美胚性质局部保持

**定义 2.3.3**（结构层）
对于完美胚空间 $X$，其结构层定义为：
$$\mathcal{O}_X(U) := \varprojlim_{V \subset U \text{ rational}} \mathcal{O}_X(V)$$
满足 $\mathcal{O}_X$ 的一致完备性。

### 2.4 倾斜等价

**定义 2.4.1**（倾斜空间）
完美胚空间 $X$ 的**倾斜** $X^\flat$ 定义为：
$$X^\flat := \text{Spa}(R^\flat, R^{+\flat})$$
带有诱导的拓扑和结构层。

**定义 2.4.2**（倾斜函子）
$$X \mapsto X^\flat$$
诱导范畴等价：
$$\{\text{完美胚空间}/\mathbb{Q}_p\} \cong \{\text{完美胚空间}/\mathbb{F}_p((t))\}$$

---

## 3. 主要结果与定理

### 3.1 基本定理

**定理 3.1.1**（Tag 0B2C - 完美胚空间定义）
完美胚空间范畴具有以下性质：

**(a) 倾斜等价**
倾斜函子 $(-)^\flat$ 诱导范畴等价：
$$\{\text{完美胚空间}/K\}^{\text{perf}} \xrightarrow{\sim} \{\text{完美胚空间}/K^\flat\}^{\text{perf}}$$

**(b) 上同调保持**
对于完美胚空间 $X$ 和有限阶étale层 $\mathcal{F}$：
$$H^i_{\text{ét}}(X, \mathcal{F}) \cong H^i_{\text{ét}}(X^\flat, \mathcal{F}^\flat)$$

**(c) 几乎纯性**
若 $X$ 是完美胚空间，$Y \to X$ 是有限étale覆盖，则 $Y$ 也是完美胚空间。

### 3.2 几乎数学

**定理 3.2.1**（几乎零模）
设 $\mathfrak{m} \subset R^\circ$ 是最大理想，模 $M$ 称为**几乎零**的，如果对任意 $\epsilon \in \mathfrak{m}$，$\epsilon M = 0$。

**定理 3.2.2**（几乎忠实平坦性）
倾斜映射诱导几乎忠实平坦性：
$$R^\circ \to (R^\flat)^\circ$$
在几乎意义下保持正合性。

### 3.3 基本群的倾斜

**定理 3.3.1**（étale基本群的倾斜）
对于连通完美胚空间 $X$：
$$\pi_1^{\text{ét}}(X) \cong \pi_1^{\text{ét}}(X^\flat)$$

### 3.4 完美胚空间的分类

**定理 3.4.1**（Scholze）
特征 $0$ 完美胚环 $R$ 由以下数据分类：
- 完美胚环 $R^\flat$（特征 $p$）
- 提升数据：$\theta: W(R^{\flat\circ}) \to R^\circ$

---

## 4. 证明思路

### 4.1 倾斜的构造

**步骤1**：多极限
$$R^\flat = \{(x^{(0)}, x^{(1)}, \ldots) \in R^{\mathbb{N}} : (x^{(i+1)})^p = x^{(i)}\}$$

**步骤2**：赋值扩展
$$|x|_{R^\flat} := |x^{(0)}|_R$$

**步骤3**：Frobenius同构
$$\varphi: R^\flat \to R^\flat, \quad (x^{(i)}) \mapsto ((x^{(i)})^p) = (x^{(i-1)})$$
显然是同构。

### 4.2 几乎纯性定理

**核心观察**：
在完美胚情形，几乎所有有限态射都是「几乎étale」的。

**步骤1**：约化到有限平坦情形

**步骤2**：使用判别式的几乎单位性

**步骤3**：通过倾斜传递到特征 $p$

### 4.3 上同调比较

**关键引理**：
对于有理子集 $U \subset X$：
$$\mathcal{O}_X(U)^\flat \cong \mathcal{O}_{X^\flat}(U^\flat)$$

**证明策略**：
1. 构造显式的Čech覆盖
2. 比较Čech复形
3. 取导出极限

---

## 5. 应用与例子

### 5.1 完美胚圆盘

**例子 5.1.1**
$p$进开单位圆盘：
$$\mathbb{B}_K := \text{Spa}(K\langle T^{1/p^\infty}\rangle, \mathcal{O}_K\langle T^{1/p^\infty}\rangle)$$
其中
$$K\langle T^{1/p^\infty}\rangle = \widehat{\bigcup_{n} K\langle T^{1/p^n}\rangle}$$

其倾斜为：
$$(\mathbb{B}_K)^\flat = \text{Spa}(K^\flat\langle t^{1/p^\infty}\rangle, \ldots)$$

### 5.2 Lubin-Tate空间

**例子 5.1.2**
Lubin-Tate形式模空间是完美胚空间：
$$\mathcal{M}_{\text{LT}} = \coprod_{\mathbb{Z}} \text{Spa}(\widehat{K}^{\text{nr}}, \ldots)$$
在倾斜后与Drinfeld上半空间相关。

### 5.3 权重单值化猜想

**应用 5.3.1**（Scholze, 2012）
完美胚空间方法证明了Deligne的**权重单值化猜想**：
$$\text{WM}(\text{Shimura簇}) = \checkmark$$

### 5.4 p进Langlands对应

**应用 5.3.2**
在p进Langlands纲领中，完美胚空间用于构造：
- 局部p进Galois表示
- 模p和p进自守形式

### 5.5 p进Hodge理论的革新

**应用 5.4.1**（Bhatt-Morrow-Scholze）
完美胚空间为p进Hodge理论提供新框架：
- $A_{\text{inf}}$-上同调
- 积分比较定理

---

## 6. 与其他概念的关系

### 6.1 与经典p进几何的对比

| 特征 | 经典刚性几何 | 完美胚空间 |
|------|------------|-----------|
| Frobenius | 非同构 | 同构（完美化）|
| 维数 | 离散 | 连续（$p^\infty$ 根）|
| 倾斜 | 不存在 | 核心工具 |
| 上同调 | 复杂 | 通过倾斜简化 |
| 覆盖 | 受限 | 几乎任意 |

### 6.2 理论演进

```
    Tate的刚性解析几何 (1962)
            │
            ▼
    Berkovich空间 (1990)
            │
            ▼
    Huber的Adic空间 (1993)
            │
            ▼
    完美胚空间 - Scholze (2011)
            │
            ▼
    棱镜上同调 - Bhatt-Scholze (2019)
```

### 6.3 与棱镜上同调的联系

**关系**：完美胚空间是棱镜上同调的解析基础

$$\text{Prism} = \text{Algebraic perfectoid} + \text{Additional structure}$$

### 6.4 与导出几何

**现代发展**：导出完美胚空间
- 允许「导出」结构层
- 与导出代数几何的结合

---

## 7. 参考文献

### 7.1 奠基文献

1. **Scholze, P.** (2012). *Perfectoid Spaces*
   - Publ. Math. IHÉS 116
   - 开创性论文

2. **Scholze, P.** (2015). *On torsion in the cohomology of locally symmetric varieties*
   - Ann. of Math.
   - 权重单值化猜想

3. **Kedlaya, K.S., Liu, R.** (2015). *Relative p-adic Hodge theory*
   - Astérisque 371
   - 基础理论

### 7.2 教科书与综述

4. **Weinstein, J.** (2017). *Semistable models for modular curves*
   - 应用导向

5. **Caraiani, A., Scholze, P.** (2017). *On the generic part of the cohomology of compact unitary Shimura varieties*
   - Ann. of Math.

6. **Bhatt, B., Morrow, M., Scholze, P.** (2018). *Integral p-adic Hodge theory*
   - 完美胚应用

### 7.3 相关领域

7. **Fargues, L., Fontaine, J.-M.** (2018). *Courbes et fibrés vectoriels en théorie de Hodge p-adique*
   - Astérisque 406

8. **Hansen, D., Kedlaya, K.S.** (2020). *Sheafiness of Witt vectors*

### 7.4 在线资源

9. **Stacks Project**: [Tag 0B2C](https://stacks.math.columbia.edu/tag/0B2C)
10. **Scholze's Notes**: Perfectoid Spaces (ArXiv:1111.4914)
11. **MSRI Videos**: Scholze的讲座系列

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0B2D](#tag-0b2d) | 完美胚与倾斜 | 核心操作 |
| [0F1A](#tag-0f1a) | p进Hodge理论 | 主要应用 |
| [0BS6](#tag-0bs6) | 棱镜上同调 | 代数化 |

### 8.2 基础理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G6A](#tag-0g6a) | Huber环 | 基础 |
| [0G6B](#tag-0g6b) | Adic空间 | 推广 |
| [0G6C](#tag-0g6c) | 一致空间 | 技术 |

### 8.3 应用方向

| Tag | 主题 | 说明 |
|-----|------|------|
| [0B2E](#tag-0b2e) | 权重单值化 | 重大应用 |
| [0B2F](#tag-0b2f) | p进周期域 | 理论应用 |
| [0F1F](#tag-0f1f) | p进Langlands | 表示论 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **2011年革命**：Scholze的引入完全改变了p进几何的面貌

2. **菲尔兹奖工作**：这是Scholze获得2018年菲尔兹奖的核心工作之一

3. **统一框架**：统一了p进几何的多个分支

4. **持续影响**：催生了棱镜上同调等后续突破

### A.2 未解决问题

- **完美胚空间的整体化**：全局完美胚概形理论
- **与复几何的更深联系**
- **算术应用的进一步拓展**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 完美胚环定义 | 🔄 进行中 | ★★★★☆ |
| 倾斜构造 | ❌ 待建设 | ★★★★★ |
| 完美胚空间 | ❌ 待建设 | ★★★★★ |
| 几乎纯性 | ❌ 待建设 | ★★★★★ |
| 上同调比较 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
