---
title: 拓扑学
msc_primary: 54

  - 54A99
  - 55A99
  - 57A99
processed_at: '2026-04-05'
references:
  textbooks:
    - id: munkres_top
      type: textbook
      title: Topology
      authors:
      - James R. Munkres
      publisher: Pearson
      edition: 2nd
      year: 2000
      isbn: 978-0131816299
      msc: 54-01
      chapters: 
      url: ~
    - id: lee_ism
      type: textbook
      title: Introduction to Smooth Manifolds
      authors:
      - John M. Lee
      publisher: Springer
      edition: 2nd
      year: 2012
      isbn: 978-1441999818
      msc: 58-01
      chapters: 
      url: ~
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
# 拓扑学 / Topology

**最后更新**: 2026年4月5日

---

## 📋 目录概述

拓扑学是研究空间在连续变形下不变性质的数学分支，被誉为"橡皮几何学"。本目录系统涵盖拓扑学的核心领域：**点集拓扑**奠定拓扑空间的基础理论；**代数拓扑**运用同伦、同调等代数工具研究拓扑不变量；**微分拓扑**探讨光滑流形及其映射；**几何拓扑**聚焦低维流形（纽结、三维流形）；**纤维丛与示性类**为现代几何与物理提供统一语言。

---

## 📊 深度版与增强版覆盖状态

| 主题 | 基础文档 | 深度版/增强版 | 状态 | MSC编码 |
|------|----------|---------------|------|---------|
| 点集拓扑 | 01-点集拓扑.md | **01-点集拓扑-深度版.md** | ✅ 深度版 (6500+字节) | 54A05 |
| 代数拓扑 | 02-代数拓扑.md | **02-代数拓扑-深度版.md** | ✅ 深度版 (7200+字节) | @ |
| 微分拓扑 | 03-微分拓扑.md | **03-微分拓扑-深度版.md** | ✅ 深度版 (6800+字节) | @ |
| 几何拓扑 | 05-几何拓扑-增强版.md | **04-几何拓扑-深度版.md** | ✅ 深度版 (6900+字节) | @ |
| 同伦论 | 04-同伦论.md | 同伦论-深度扩展版.md | ✅ 已有深度版 | @ |
| 同调论 | 05-同调论.md | 同调论基础-深度扩展版.md | ✅ 已有深度版 | @ |
| 纤维丛理论 | 06-纤维丛理论.md | **07-纤维丛理论-增强版.md** | ✅ 增强版 (5800+字节) | 55R10 |
| 示性类 | 07-向量丛与示性类.md | **08-示性类-增强版.md** | ✅ 增强版 (6200+字节) | 57R20 |

**深度版占比**: 5/8 = **62.5%** (目标: 45%+)

---

## 📁 文档索引

### 深度版文档 (≥5000字节，完整证明)

| 文档 | 主题 | 核心内容 | 交叉引用 |
|------|------|----------|----------|
| [01-点集拓扑-深度版](01-点集拓扑-深度版.md) | 点集拓扑 | Urysohn引理、Tychonoff定理、Tietze扩张定理完整证明 | 康托尔、豪斯多夫 |
| [02-代数拓扑-深度版](02-代数拓扑-深度版.md) | 代数拓扑 | 基本群函子性、van Kampen定理、Hurewicz定理 | 庞加莱、Hopf |
| [03-微分拓扑-深度版](03-微分拓扑-深度版.md) | 微分拓扑 | Sard定理、横截性、Whitney嵌入定理 | 惠特尼、米尔诺 |
| [04-几何拓扑-深度版](04-几何拓扑-深度版.md) | 几何拓扑 | Wirtinger表示、Thurston几何化、Perelman证明思路 | 庞加莱、Thurston |

### 增强版文档 (≥4000字节，详细示例)

| 文档 | 主题 | 核心内容 | 交叉引用 |
|------|------|----------|----------|
| [07-纤维丛理论-增强版](07-纤维丛理论-增强版.md) | 纤维丛 | Hopf纤维化、主丛、示性类计算、规范场论应用 | Hopf、陈省身 |
| [08-示性类-增强版](08-示性类-增强版.md) | 示性类 | Stiefel-Whitney类、Chern类、Pontryagin类、指标定理 | Chern、Thom |

### 已有深度版文档

| 文档 | 主题 | 说明 |
|------|------|------|
| [04-同伦论-深度扩展版](04-同伦论-深度扩展版.md) | 同伦论 | 已完成，检查完善 |
| [同调论基础-深度扩展版](同调论基础-深度扩展版.md) | 同调论 | 已完成，检查完善 |

---

## 🗺️ 学习路径

### 入门阶段（建议时长：6-8周）

**推荐学习顺序**:

1. **起点**: [01-点集拓扑-深度版](01-点集拓扑-深度版.md)
   - 拓扑空间、连续映射、紧致性、连通性
   - 分离公理、度量空间、可数性

2. **深化**: [02-代数拓扑-深度版](02-代数拓扑-深度版.md)
   - 基本群、覆盖空间
   - 同调群、上同调

### 进阶方向

#### 方向A：微分拓扑（需先修微分流形）

**学习序列**:
1. [03-微分拓扑-深度版](03-微分拓扑-深度版.md)
2. [07-纤维丛理论-增强版](07-纤维丛理论-增强版.md)
3. [08-示性类-增强版](08-示性类-增强版.md)

#### 方向B：低维拓扑（需先修代数拓扑）

**学习序列**:
1. [04-几何拓扑-深度版](04-几何拓扑-深度版.md)
2. [16-纽结理论](16-纽结理论.md)

---

## 🔗 与数学家理念体系的交叉引用

| 数学家 | 相关文档 | 贡献领域 |
|--------|----------|----------|
| 康托尔 | 01-点集拓扑-深度版 | 集合论基础 |
| 庞加莱 | 02-代数拓扑-深度版、04-几何拓扑-深度版 | 同伦论、Poincaré猜想 |
| 惠特尼 | 03-微分拓扑-深度版 | 嵌入定理、浸入定理 |
| Hopf | 07-纤维丛理论-增强版 | Hopf纤维化 |
| 陈省身 | 08-示性类-增强版 | Chern类、纤维丛 |

---

## 📚 参考文献

### 经典教材
1. Munkres, J.R. *Topology*. 2nd ed. Pearson, 2000.
2. Hatcher, A. *Algebraic Topology*. Cambridge, 2002.
3. Milnor, J.W. *Topology from the Differentiable Viewpoint*. Princeton, 1965.
4. Thurston, W.P. *Three-Dimensional Geometry and Topology*. Princeton, 1997.

### 现代教材
1. Riemannian Geometry and Topology
2. Characteristic Classes and Fiber Bundles

---

**最后更新**: 2026年4月5日
