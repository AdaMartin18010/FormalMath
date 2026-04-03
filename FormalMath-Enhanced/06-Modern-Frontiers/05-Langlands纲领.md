---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Langlands纲领最新进展 (2020-2025)

> **历史地位**: "数学的大统一理论"
> **2020年代突破**: 几何Langlands纲领的证明
> **核心人物**: Dennis Gaitsgory, Peter Scholze, Laurent Fargues
> **新兴方向**: 同伦Langlands纲领、Fargues-Fontaine曲线

---

## 背景与动机

### 什么是Langlands纲领？

**Robert Langlands** (1967年) 提出的一系列深刻猜想，建立了：

```
数论                表示论              几何
─────────────────────────────────────────────
伽罗瓦表示    ↔    自守表示      ↔   几何对象
L-函数            自守L-函数         几何L-函数
```

**核心思想**:
> 不同数学领域中的对象之间存在深刻的对应关系，这种对应可以通过L-函数来体现。

### 三大支柱

1. **数论Langlands纲领**
   - 局部与整体域的伽罗瓦表示
   - 自守形式与表示
   - L-函数的函数方程

2. **几何Langlands纲领**
   - 代数曲线的矢量丛
   - D-模或 perverse sheaves
   - 几何化的对应

3. **函数域Langlands纲领**
   - 介于数论和几何之间的情形
   - 使用代数几何工具

### 为什么重要？

**历史影响**:

- Andrew Wiles证明费马大定理 (1995) - 使用了Langlands纲领的思想
- 模性提升定理的发展
- L-函数特殊值的深刻结果

**数学统一性**:

- 连接了看似无关的数学分支
- 提供了研究困难问题的新视角
- 催生了大量新的数学理论

---

## 核心概念

### 1. 局部Langlands对应

**设置**: 局部域 $F$（如 $\mathbb{Q}_p$, $\mathbb{R}$, $\mathbb{C}$）

**对应**:

```
{G(F)的不可约表示}  ↔  {G^∨的Weil-Deligne群表示}
          ↓                          ↓
     自守表示                  伽罗瓦表示
```

其中 $G$ 是约化群，$G^∨$ 是其Langlands对偶群。

**$GL(n)$情形**:

**定理** (Harris-Taylor, Henniart, Scholze):
$GL_n(F)$ 的不可约光滑表示 ↔ $n$维Weil群表示

**意义**: 这是Langlands纲领中第一个被完全证明的情形。

### 2. 整体Langlands对应

**设置**: 整体域 $F$（如 $\mathbb{Q}$, 函数域）

**对应**:

```
{G(A_F)的自守表示}  ↔  {G^∨的伽罗瓦表示}
```

其中 $A_F$ 是 $F$ 的阿代尔环。

**关键对象**:

- **自守形式**: 满足特定对称性的函数
- **L-函数**: 编码算术信息的复函数
- **功能方程**: $L(s) = \epsilon(s)L(1-s)$

### 3. 几何Langlands纲领

**设置**: 光滑射影曲线 $X$ 在代数闭域 $k$ 上

**对应的核心**:

```
{G-矢量丛上的D-模}  ↔  {G^∨-局部系统}
         ↓                      ↓
    "自守"一侧            "伽罗瓦"一侧
```

**关键构造**:

- **Bun_G**: 曲线 $X$ 上 $G$-主丛的模空间
- **LocSys_{G^∨}**: $G^∨$-局部系统的模空间
- **Hecke算子**: 作用在自守形式上的算子

**几何Langlands猜想**:

存在一个范畴等价：

$$D\text{-mod}(\text{Bun}_G) \cong \text{QCoh}(\text{LocSys}_{G^∨})$$

或其变形版本。

### 4. Fargues-Fontaine曲线

**突破**: Laurent Fargues和Jean-Marc Fontaine (2012-2018)

**构造**: 对于完美oid空间 $S$，构造曲线 $X_S$：

$$X_S = \text{Proj}\left(\bigoplus_{n \geq 0} B^+_{\text{crys}}(S)^{\varphi = p^n}\right)$$

**关键性质**:

- 是完备的、正则的、一维的
- 类似于代数曲线的局部域
- 连接了完美oid空间和经典代数几何

**意义**: 为 $p$-adic Langlands纲领提供了几何框架。

### 5. 同伦Langlands纲领

**新兴方向**: 使用高阶结构（∞-范畴、导出代数几何）研究Langlands对应。

**核心思想**:

- 将范畴等价提升到导出/∞-层次
- 考虑高阶不变量
- 与拓扑循环同调的联系

---

## 关键结果

### 定理1: 局部类域论

**定理**: 局部域 $F$ 的阿贝尔扩张 ↔ $F^*$ 的连续特征标

这是Langlands纲领的交换版本，也是所有非交换推广的起点。

### 定理2: $GL(2)$的模性提升

**定理** (Wiles, Taylor-Wiles):

某些伽罗瓦表示来自模形式。

**应用**: 费马大定理的证明。

### 定理3: 几何Langlands的categorical形式

**定理** (Gaitsgory, 2020年代):

对于函数域，存在Whittaker范畴与spectral范畴的等价。

这是几何Langlands纲领的巨大突破。

### 定理4: Fargues-Fontaine曲线的几何化

**定理**: $p$-adic表示可以用Fargues-Fontaine曲线上的向量丛来分类。

**推论**: 新的 $p$-adic Hodge理论视角。

### 定理5: 完美oid空间的 diamonds

**定理** (Scholze):

将完美oid空间提升到diamonds（一种pro-étale层），建立了完美的对应理论。

---

## 现代发展 (2020-2025)

### 2020: 几何Langlands的突破

**Dennis Gaitsgory的工作**:

- 完成了几何Langlands纲领的categorical版本
- 使用导出代数几何和∞-范畴
- 证明了核心猜想的函数域版本

**技术工具**:

- Whittaker范畴
- 几何Eisenstein级数
- 量子化

### 2021: Fargues-Fontaine曲线的进一步发展

- **向量丛的分类**: 完整的分类定理
- **Harder-Narasimhan理论**: 在曲线上的推广
- **与Banach-Colmez空间的联系**

### 2022: 凝聚数学与Langlands

Peter Scholze的凝聚数学为Langlands纲领提供了新工具：

- 凝聚表示论
- 局部Langlands的几何化
- $p$-adic解析群的新视角

### 2023: 同伦Langlands的进展

- **导出Hecke代数**: 高阶结构的研究
- **拓扑循环同调的联系**: 与L-函数特殊值的联系
- **高阶Adams操作**

### 2024: 模性提升的新方法

- **potential 自守性**: 新的技术突破
- **Calegari-Geraghty方法**: 无自对偶假设的模性提升
- **与Perfectoid理论的交叉**

### 2025: 新兴方向

1. **算术几何中的高阶结构**: 使用∞-范畴方法
2. **量子Langlands纲领**: 与量子场论的联系
3. **算术D-模理论**: 新的p进方法
4. **自动化的Langlands对应**: 使用机器学习发现对应关系

---

## 与其他领域的联系

### 与代数几何的联系

```
代数几何              Langlands纲领
─────────────────────────────────────
模空间               →   自守形式的空间
 motive理论          →   L-函数的理论
 层理论              →   几何对应
导出范畴            →   范畴Langlands
```

### 与表示论的联系

**自守表示的分类**:

- Arthur-Selberg迹公式
- 局部表示的L-包(L-packets)
- 内窥理论(Endoscopy)

**几何表示论**:

- Kazhdan-Lusztig理论
- Springer理论
- Soergel双模

### 与数论的联系

**算术应用**:

- 费马大定理
- 同余数问题
- BSD猜想
- 主猜想(Iwasawa理论)

**L-函数的特殊值**:

- Beilinson猜想
- Bloch-Kato猜想
- 与代数K-理论的联系

### 与数学物理的联系

**电磁对偶**:

- Kapustin-Witten的工作
- S-对偶与几何Langlands
- 拓扑场论的视角

**量子场论**:

- 共形场论中的对应
- 弦理论中的对偶性

---

## 学习资源

### 经典文献

1. **"Automorphic Forms on GL(2)"** (Jacquet-Langlands, 1970)
   - Langlands纲领的开创性工作

2. **"The Correspondence Between Representations of Local and Global Fields"** (Langlands)
   - 原始提案

### 现代综述

1. **"An Introduction to the Langlands Program"** (Bernstein, Gelbart等)
   - 综述文集，适合入门

2. **"Geometric Langlands and Its Applications"** (Frenkel)
   - 几何Langlands的综述

3. **"The Stacks Project"** - Tag 0BD1
   - 代数几何基础

### 视频资源

1. **Gaitsgory的Harvard讲座**
   - 几何Langlands的系统性介绍

2. **Scholze的Bonn讲座**
   - 完美oid空间与Langlands

3. **MSRI研讨会** (2019)
   - 最新进展的综述

### 在线资源

1. **MathOverflow**
   - 标签: langlands-conjectures, automorphic-forms

2. **nLab**
   - Langlands纲领相关的概念

---

## 开放问题

### 问题1: 数域的Langlands对应

**问题**: 如何建立数域上的完整Langlands对应？

**现状**: 函数域情形已取得巨大进展，但数域情形更加困难。

### 问题2: 几何Langlands的数论版本

**问题**: 如何将几何Langlands的结果转化回数论？

**挑战**: 需要新的算术几何工具。

### 问题3: $p$-adic Langlands纲领

**问题**: $p$-adic自守形式与 $p$-adic伽罗瓦表示的精确对应是什么？

**现状**: Breuil, Colmez, Emerton等人有重要工作，但完整理论尚未建立。

### 问题4: 函子性的证明

**问题**: 如何证明Langlands函子性猜想？

**意义**: 这是Langlands纲领的核心。

### 问题5: 高阶L-函数

**问题**: 如何理解高阶L-函数的特殊值？

**联系**: 与代数K-理论、motives的关系。

### 问题6: 自动化Langlands对应

**问题**: 是否可以使用机器学习来发现新的Langlands对应？

**新兴方向**: 数学与AI的交叉。

---

## 形式化状态

### Mathlib4中的相关数学

Langlands纲领的形式化是一个长期目标，需要大量基础数学：

| 组件 | 状态 | 优先级 |
|------|------|--------|
| 代数数论 | 🔄 进行中 | 高 |
| 表示论 | 🔄 进行中 | 高 |
| 代数几何 | 🔄 进行中 | 高 |
| 自守形式 | 📋 计划中 | 中 |
| L-函数 | 📋 计划中 | 中 |

### 形式化挑战

1. **复杂性**: Langlands纲领涉及多个高深的数学领域
2. **抽象性**: 需要处理大量的范畴论和层论
3. **证明长度**: 关键定理的证明极其复杂

---

## 总结

Langlands纲领是20世纪数学最伟大的构想之一，而在2020年代，我们见证了这一纲领的重大突破。从几何Langlands的范畴化证明到Fargues-Fontaine曲线的深刻应用，这一领域正在经历前所未有的发展。

**核心贡献**:

1. ✅ 连接了数论、表示论和几何
2. ✅ 催生了新的数学理论和技术
3. ✅ 解决了历史性的数学难题
4. ✅ 推动了算术几何的发展

**未来展望**:

- 数域Langlands对应完全解决
- 与数学物理的深度融合
- 高阶结构的系统应用
- 自动化数学发现的工具

---

*最后更新: 2026年4月 | FormalMath项目*
