---
msc_primary: 14
title: 13-代数几何索引 / Algebraic Geometry Index
processed_at: '2026-04-08'
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 13-代数几何索引 / Algebraic Geometry Index

**多项式方程的几何 — 从古典代数几何到概形理论、层上同调与模空间**

---

## 📋 分支概览

代数几何是现代数学的核心分支，研究多项式方程组的解集的几何性质。本分支涵盖从古典代数簇理论到Grothendieck概形理论的完整发展，以及层论、上同调、相交理论等现代工具。

**难度等级**: ⭐⭐⭐⭐⭐（研究级）

---

## 📁 内容索引

### 1. 代数簇基础 (Algebraic Varieties)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-仿射簇与Zariski拓扑-深度版](./01-代数簇基础/01-仿射簇与Zariski拓扑-深度版.md) | 仿射代数集、Hilbert零点定理、Zariski拓扑 | ⭐⭐⭐⭐ | 14A10, 14A15 |
| [02-射影簇与齐次坐标-深度版](./01-代数簇基础/02-射影簇与齐次坐标-深度版.md) | 射影空间、齐次坐标、Bézout定理 | ⭐⭐⭐⭐⭐ | 14A15, 14N05 |
| [03-代数簇的态射-深度版](./01-代数簇基础/03-代数簇的态射-深度版.md) | 态射、有理映射、双有理等价 | ⭐⭐⭐⭐⭐ | 14A15, 14E05 |

**核心定理**:

- Hilbert零点定理（强形式与弱形式）
- 不可约分解定理
- Bézout定理
- 纤维维数定理

---

### 2. 层论与上同调 (Sheaves and Cohomology)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-层论基础-深度版](./02-层论与上同调/01-层论基础-深度版.md) | 层与预层、茎、层化 | ⭐⭐⭐⭐⭐ | 14F05, 18F20 |
| [02-结构层与凝聚层-深度版](./02-层论与上同调/02-结构层与凝聚层-深度版.md) | 环化空间、凝聚层、Serre有限性 | ⭐⭐⭐⭐⭐ | 14F05, 14A15 |
| [03-Čech上同调-深度版](./02-层论与上同调/03-Čech上同调-深度版.md) | Čech复形、Serre消没定理 | ⭐⭐⭐⭐⭐ | 14F25, 14F40 |

**核心定理**:

- 层序列正合性的茎判别
- Serre有限性定理
- Serre消没定理
- Čech上同调与导出上同调的同构

---

### 3. 概形理论 (Scheme Theory)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-仿射概形-深度版](./03-概形理论/01-仿射概形-深度版.md) | Spec构造、结构层、局部环化空间 | ⭐⭐⭐⭐⭐ | 14A15, 14A20 |
| [02-一般概形与态射-深度版](./03-概形理论/02-一般概形与态射-深度版.md) | 概形定义、态射、分离性、properness | ⭐⭐⭐⭐⭐ | 14A15, 14A20 |
| [03-纤维积与基变换-深度版](./03-概形理论/03-纤维积与基变换-深度版.md) | 纤维积、基变换、平坦性 | ⭐⭐⭐⭐⭐ | 14A15, 14E99 |

**核心定理**:

- 仿射概形的伴随等价
- 纤维积的存在性
- 赋值判别准则
- Zariski主定理

---

### 4. 除子与线丛 (Divisors and Line Bundles)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-Weil除子与Cartier除子-深度版](./04-除子与线丛/01-Weil除子与Cartier除子-深度版.md) | 两种除子、类群、Picard群 | ⭐⭐⭐⭐⭐ | 14C20, 14C22 |
| [02-线丛与Picard群-深度版](./04-除子与线丛/02-线丛与Picard群-深度版.md) | 可逆层、Picard群、丰富线丛 | ⭐⭐⭐⭐⭐ | 14C22, 32L05 |
| [03-Riemann-Roch定理-深度版](./04-除子与线丛/03-Riemann-Roch定理-深度版.md) | 曲线RR、Hirzebruch-RR、Grothendieck-RR | ⭐⭐⭐⭐⭐ | 14C40, 14H55 |

**核心定理**:

- 除子-线丛对应定理
- Riemann-Roch定理（各版本）
- Serre对偶
- Nakai-Moishezon判别准则

---

### 5. 相交理论 (Intersection Theory)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-Chow群-深度版](./05-相交理论/01-Chow群-深度版.md) | 代数循环、有理等价、Chow环 | ⭐⭐⭐⭐⭐ | 14C15, 14C25 |
| [02-相交积-深度版](./05-相交理论/02-相交积-深度版.md) | 相交积、陈类、Bézout定理 | ⭐⭐⭐⭐⭐ | 14C17, 14N10 |

**核心定理**:

- Chow环的结构
- 投射丛公式
- Blow-up公式
- 广义Bézout定理

---

### 6. 模空间 (Moduli Spaces)

| 文档 | 核心内容 | 难度 | MSC分类 |
|------|----------|------|---------|
| [01-曲线模空间-深度版](./06-模空间/01-曲线模空间-深度版.md) | M_g构造、稳定曲线、Deligne-Mumford紧化 | ⭐⭐⭐⭐⭐ | 14H10, 14D20 |
| [02-向量丛模空间-深度版](./06-模空间/02-向量丛模空间-深度版.md) | 稳定丛、Narasimhan-Seshadri定理、GIT构造 | ⭐⭐⭐⭐⭐ | 14D20, 14H60 |

**核心定理**:

- Deligne-Mumford定理（M_g的存在性）
- Narasimhan-Seshadri定理
- 维数公式（曲线/丛模空间）
- 紧化定理

---

## 🚀 学习路径推荐

### 入门路径（大三/研究生一年级）

```
1. 代数簇基础
   └── 仿射簇与Zariski拓扑
   └── 射影簇与齐次坐标

2. 除子与线丛
   └── Weil除子与Cartier除子
   └── 线丛与Picard群

3. 概形初步
   └── 仿射概形
   └── 一般概形与态射
```

### 进阶路径（研究生）

```
1. 层论与上同调
   └── 层论基础
   └── 结构层与凝聚层
   └── Čech上同调

2. 相交理论
   └── Chow群
   └── 相交积

3. Riemann-Roch理论
   └── 曲线上的RR
   └── Hirzebruch-Roch
```

### 高级路径（研究级）

```
1. 模空间理论
   └── 曲线模空间 M_g
   └── 向量丛模空间

2. 前沿主题
   └── 导出代数几何
   └── 动机理论
   └── p进Hodge理论
```

---

## 📊 项目统计

| 类别 | 文档数 | 核心定理 | Lean4形式化 |
|------|--------|----------|-------------|
| 代数簇基础 | 3篇 | 6个 | 部分 |
| 层论与上同调 | 3篇 | 5个 | 部分 |
| 概形理论 | 3篇 | 6个 | 部分 |
| 除子与线丛 | 3篇 | 8个 | 部分 |
| 相交理论 | 2篇 | 5个 | 部分 |
| 模空间 | 2篇 | 4个 | 部分 |
| **总计** | **16篇** | **34个** | **进行中** |

---

## 🔗 国际课程对齐

### MIT

- 18.725 Algebraic Geometry I → 代数簇基础、层论
- 18.726 Algebraic Geometry II → 概形理论、上同调

### Harvard

- Math 221 Algebra and Geometry → 代数簇、概形
- Math 232br The Geometry of Schemes → 概形理论深度

### Stanford

- Math 245A/B Algebraic Geometry → 全面覆盖

### Princeton

- MAT 416/417 Introduction to Algebraic Geometry → 入门到进阶

---

## 📚 参考文献

### 经典教材

1. Hartshorne, R. *Algebraic Geometry*. Springer, 1977.
2. Shafarevich, I.R. *Basic Algebraic Geometry* I & II. Springer, 2013.
3. Griffiths, P., Harris, J. *Principles of Algebraic Geometry*. Wiley, 1994.

### 现代专著

4. Liu, Q. *Algebraic Geometry and Arithmetic Curves*. Oxford, 2002.
2. Görtz, U., Wedhorn, T. *Algebraic Geometry I*. Vieweg, 2010.
3. Vakil, R. *The Rising Sea: Foundations of Algebraic Geometry*.

### 专题著作

7. Eisenbud, D., Harris, J. *The Geometry of Schemes*. Springer, 2000.
2. Miranda, R. *Algebraic Curves and Riemann Surfaces*. AMS, 1995.
3. Huybrechts, D., Lehn, M. *The Geometry of Moduli Spaces of Sheaves*.

---

## 💻 Lean4形式化实现

| 主题 | 状态 | 文档位置 |
|------|------|----------|
| 仿射簇基础 | 🟡 进行中 | 各文档内嵌 |
| 层论基础 | 🟡 进行中 | 各文档内嵌 |
| 概形理论 | 🟡 进行中 | 各文档内嵌 |
| 除子理论 | 🟡 进行中 | 各文档内嵌 |
| Riemann-Roch | 🔴 待完善 | 各文档内嵌 |

---

## 🔗 关联分支

| 分支 | 关联内容 |
|------|----------|
| [02-代数结构](../02-代数结构/) | 交换代数、同调代数 |
| [04-几何与拓扑](../04-几何与拓扑/) | 代数拓扑、微分几何 |
| [15-同调代数](../15-同调代数/) | 导出范畴、谱序列 |
| [05-数论](../05-数论/) | 算术几何、椭圆曲线 |

---

## 📈 学习进度追踪

- [x] 代数簇基础
- [x] 层论与上同调
- [x] 概形理论
- [x] 除子与线丛
- [x] 相交理论
- [x] 模空间理论
- [ ] 高级专题（动机理论、导出几何）

---

## 📝 修订历史

| 日期 | 版本 | 更新内容 |
|------|------|----------|
| 2026-04-08 | v1.0 | 初始创建，16篇核心文档 |

---

**维护者**: FormalMath项目组
**最后更新**: 2026年4月8日
**版本**: v1.0
