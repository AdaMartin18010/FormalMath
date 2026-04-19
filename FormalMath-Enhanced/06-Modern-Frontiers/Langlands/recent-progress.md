---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Langlands纲领：2020年代最新进展
---
# Langlands纲领：2020年代最新进展

> Gaitsgory的几何Langlands证明、Fargues-Fontaine曲线以及局部Langlands对应的最新突破

---

## 1. Gaitsgory的几何Langlands证明概述

### 1.1 历史背景

**几何Langlands纲领** (1980s-至今):

对于光滑射影曲线 $X$ 在代数闭域 $k$ 上，核心猜想是：
$$\text{D-mod}(\text{Bun}_G) \cong \text{QCoh}(\text{LocSys}_{G^\vee})$$

**2020年突破**: Dennis Gaitsgory及其合作者完成了函数域情形的完整证明。

### 1.2 证明策略概述

**核心定理** (Gaitsgory et al., 2020-2024):

$$\text{Whit}_G \cong \text{Spect}_G$$

其中：

- **Whit_G**: Whittaker范畴（"自守"一侧）
- **Spect_G**: 谱范畴（"伽罗瓦"一侧）

**证明步骤**:

```
步骤1: 建立Whittaker范畴的变形
   ↓
步骤2: 证明与Kac-Moody局部化的兼容性
   ↓
步骤3: 建立与仿射Grassmannian的联系
   ↓
步骤4: 证明与spectral side的等价
   ↓
步骤5: 验证与经典对应的兼容性
```

### 1.3 关键技术工具

**工具1: 导出∞-范畴**

几何Langlands的证明完全在导出∞-范畴框架下进行：

$$\mathcal{C} = \text{IndCoh}_{\mathcal{N}}(\text{LocSys}_G)$$

**工具2: 形变理论**

使用形变到法锥 (deformation to the normal cone) 技术处理奇异模空间。

**工具3: 量子化**

Whittaker范畴可以看作是Hecke范畴的"量子化"。

### 1.4 与经典Langlands的联系

**定理**: 几何Langlands对应的"经典极限"与函数域Langlands对应兼容。

具体地，对于 $\mathbb{F}_q$-点：
$$\text{Tr}(\text{Frob}_q, \mathcal{F}) \leftrightarrow \text{自守函数}$$

---

## 2. Fargues-Fontaine曲线的构造

### 2.1 基本构造

**设定**:

- $E$: 局部域（通常是 $\mathbb{Q}_p$）
- $F$: 完美oid空间（或完美oid代数）

**定义** (Fargues-Fontaine曲线):

对于完美oid对 $(F, F^+)$，定义**Fargues-Fontaine曲线** $X_{F,E}$：

$$X_{F,E} = \text{Proj}\left(\bigoplus_{n \geq 0} B^+_{\text{crys}}(F^+/p)^{\varphi = \pi^n}\right)$$

其中：

- $B^+_{\text{crys}}$: 晶体周期环
- $\varphi$: Frobenius自同态
- $\pi$: $E$ 的uniformizer

### 2.2 关键性质

**定理 2.2.1** (Fargues-Fontaine):

Fargues-Fontaine曲线 $X_{F,E}$ 满足：

1. **完备性**: 是完备的、正则的、一维的Noetherian概形
2. **几何单连通**: $\pi_1^{\text{geom}}(X_{F,E}) = 1$
3. **与完美oid的联系**: 点对应于untilts

**定理 2.2.2** (向量丛分类):

$X_{F,E}$ 上的向量丛有**Harder-Narasimhan分解**：

任何向量丛 $\mathcal{E}$ 唯一地分解为：
$$\mathcal{E} = \bigoplus_{\mu \in \mathbb{Q}} \mathcal{E}_\mu$$
其中 $\mathcal{E}_\mu$ 是斜率为 $\mu$ 的半稳定丛。

**定理 2.2.3** (与Galois表示的联系):

存在范畴等价：
$$\{\text{$E$-线性连续} \text{Gal}_F\text{-表示}\} \cong \{\text{$X_{F,E}$上的半稳定向量丛}\}$$

### 2.3 在p-adic Hodge理论中的应用

**定理 2.3.1** ($p$-adic Hodge理论的几何化):

对于 $p$-adic表示 $V$，可以构造 $X_{F, \mathbb{Q}_p}$ 上的向量丛 $\mathcal{E}(V)$ 使得：

- $V$ 是晶体表示 $\Leftrightarrow$ $\mathcal{E}(V)$ 来自晶体模
- $V$ 是de Rham表示 $\Leftrightarrow$ $\mathcal{E}(V)$ 在无穷远点有对数联络

**与完美oid理论的联系**:

$$\{\text{untilts of } F\} \cong \{\text{closed points of } X_{F, \mathbb{Q}_p}\}$$

### 2.4 具体计算示例

**例**: 计算 $\mathcal{O}(1)$ 的上同调

对于 $X = X_{F,E}$，线丛 $\mathcal{O}(1)$ 满足：
$$H^0(X, \mathcal{O}(n)) = B^{\varphi = \pi^n}$$

其中 $B$ 是Fontaine的环。

**维数公式**:
$$\dim_E H^0(X, \mathcal{O}(n)) = \begin{cases} n & n \geq 0 \\ 0 & n < 0 \end{cases}$$

这与 $\mathbb{P}^1$ 上的公式惊人地相似！

---

## 3. 局部Langlands对应

### 3.1 数域情形的最新进展

**定理 3.1.1** (Harris-Taylor, Henniart, Scholze):

对于 $GL_n(F)$，局部Langlands对应是完全建立的：

$$\{\text{不可约光滑表示 of } GL_n(F)\} \longleftrightarrow \{\text{n维 Weil-Deligne 表示}\}$$

**Scholze的新方法** (2013-2020):

使用完美oid空间和p-adic Hodge理论：

1. 构造模空间的完美oid版本
2. 使用p-adic比较同构
3. 推导出局部Langlands对应

### 3.2 p-adic Langlands纲领

**问题**: 如何将局部Langlands对应推广到 $p$-adic表示？

**当前状态**:

| 群 | 状态 | 关键人物 |
|---|------|---------|
| $GL_2(\mathbb{Q}_p)$ | ✅ 完整 | Colmez, Breuil, Paskunas |
| $GL_2(F)$ | 🔄 部分 | Breuil, Paskunas |
| $GL_n(\mathbb{Q}_p)$ | 🔄 进行中 | Emerton, Helm, Moss |
| 一般约化群 | 📋 计划中 | 多个研究团队 |

**关键技术**:

- $(\varphi, \Gamma)$-模
- 完备同调
- Emerton的特征标簇

### 3.3 几何化方法

**定理 3.3.1** (Fargues):

使用Fargues-Fontaine曲线，可以将局部Langlands对应几何化为：

$$\text{Bun}_G \times \text{Div}^1 \to \text{类特征标理论}$$

其中：

- $\text{Bun}_G$: $X_{F,E}$ 上 $G$-丛的模空间
- $\text{Div}^1$: Cartier除子的某种推广

---

## 4. 开放问题列表

### 4.1 核心开放问题

**问题1: 数域Langlands对应**

**描述**: 建立数域上的完整Langlands对应。

**难点**:

- 缺乏几何化工具
- 局部-整体原理的困难
- 无阿基米德位置的复杂性

**研究现状**:

- 模性提升定理有重大进展 (Calegari-Geraghty)
- potential自守性技术

---

**问题2: 函子性的证明**

**描述**: 证明Langlands函子性猜想。

**Langlands函子性猜想**:

对于 $G, H$ 的 $L$-同态 $\phi: {}^L H \to {}^L G$，存在转移映射：
$$\text{Aut}(H) \to \text{Aut}(G)$$

**进展**:

- 循环基变换 (Arthur-Clozel)
- 基本引理的证明 (Ngo)
- 稳定迹公式的发展

---

**问题3: $p$-adic Langlands完备性**

**描述**: 建立 $GL_n$ 的完整 $p$-adic Langlands对应。

**具体目标**:

1. 构造 $p$-adic局部Langlands对应
2. 证明与经典对应的兼容性
3. 建立局部-整体相容性

---

**问题4: 几何Langlands的数论应用**

**描述**: 将Gaitsgory的几何结果应用于数论问题。

**可能方向**:

- 几何方法在迹公式中的应用
- 与Iwasawa理论的联系
- 与算术几何的交叉

---

**问题5: Langlands纲领与物理学**

**描述**: 深化Langlands纲领与理论物理的联系。

**已有联系**:

- Kapustin-Witten: S-对偶与几何Langlands
- Witten: 扭曲张量场论与Langlands对偶

**开放方向**:

- 量子场论中的Langlands对偶
- 弦理论与自守形式
- 黑洞物理与L-函数

---

**问题6: 计算与自动化**

**描述**: 使用计算工具研究Langlands对应。

**研究方向**:

- L-函数的高精度计算
- Galois表示的显式构造
- 机器学习发现新的对应

---

### 4.2 技术性开放问题

| 问题 | 描述 | 难度 |
|-----|------|------|
| 基本引理推广 | 非驯顺情形的基本引理 | 高 |
| 稳定化 | 一般群的稳定迹公式 | 高 |
| $p$-adic Hodge理论 | 非阿基米德自守形式的Hodge理论 | 高 |
| 导出范畴版本 | 几何Langlands的导出/∞-版本 | 中 |
| 同伦版本 | 同伦Langlands纲领 | 中 |
| 算术D-模 | 完善算术D-模理论 | 中 |

---

## 5. 与相关领域的联系

### 5.1 与凝聚数学的联系

**联系点**:

- $p$-adic局部Langlands的凝聚描述
- 固体向量空间在表示论中的应用
- 局部-整体原理的凝聚视角

**定理 5.1.1** (凝聚表示论):

局部紧群的某些表示可以用凝聚阿贝尔群描述。

### 5.2 与∞-范畴论的联系

**联系点**:

- 几何Langlands使用导出∞-范畴
- 同伦Langlands纲领
- 高阶不变量

**研究方向**:
$$\text{几何Langlands} \times \text{∞-范畴论} \to \text{同伦Langlands}$$

### 5.3 与形式化证明的联系

**Mathlib4中的相关数学**:

| 概念 | 状态 | 优先级 |
|-----|------|-------|
| 代数数论基础 | 🔄 进行中 | 高 |
| 表示论 | 🔄 进行中 | 高 |
| 自守形式 | 📋 计划中 | 中 |
| L-函数 | 📋 计划中 | 中 |
| 代数几何 | 🔄 进行中 | 高 |

**长期目标**: 形式化Langlands纲领中的核心定理。

---

## 6. 学习资源与前沿动态

### 6.1 最新文献

**几何Langlands**:

1. Gaitsgory, D. "Proof of the geometric Langlands conjecture" (2024)
2. Arinkin, D., Gaitsgory, D. "Singular support of coherent sheaves"

**Fargues-Fontaine曲线**:

1. Fargues, L. "G-torseurs en théorie de Hodge p-adique"
2. Fargues, L., Fontaine, J-M. "Courbes et fibrés vectoriels"

**局部Langlands**:

1. Scholze, P. "p-adic Hodge theory for rigid-analytic varieties"
2. Emerton, M., Helm, D. "The local Langlands correspondence for GL_n"

### 6.2 会议与研讨会

- **MSRI Program**: "The Langlands Program" (定期)
- **Hausdorff Institute**: "The Arithmetic of the Langlands Program"
- **IHES Summer School**: 相关主题

### 6.3 在线资源

- **MathOverflow**: 标签 `langlands-conjectures`
- **nLab**: Langlands纲领相关内容
- **Glossary of Langlands**: https://www.math.ias.edu/glossary/[需更新]

---

## 7. 总结与展望

### 7.1 2020年代的突破

✅ **已完成**:

- 几何Langlands纲领的完整证明（函数域）
- Fargues-Fontaine曲线理论的成熟
- $p$-adic Langlands的重大进展
- 与完美oid理论的深度融合

### 7.2 未来十年的挑战

🔄 **进行中**:

- 数域Langlands对应
- 函子性的完整证明
- $p$-adic Langlands的完备化
- 几何结果的数论应用

### 7.3 长远愿景

📋 **期待中**:

- Langlands纲领的完全解决
- 与数学物理的深度融合
- 计算方法的应用
- 形式化验证的实现

---

*最后更新: 2026年4月 | FormalMath项目*
