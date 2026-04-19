---
title: Harvard Math 232br 代数几何与上同调讲义逐章拆解索引
msc_primary: 00A99
course_code: Harvard Math 232br
course_name: Algebraic Geometry II (Cohomology)
instructor: Aaron Landesman / Man-Wai Cheung / Joe Harris tradition
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
processed_at: '2026-04-17'
---

# Harvard Math 232br 代数几何与上同调讲义逐章拆解索引

> **任务编号**：P2-T1
> **课程代码**：Harvard Math 232br
> **课程名称**：Algebraic Geometry II — Curves, Surfaces, Cohomology（研究生核心）
> **授课传统**：Joe Harris / Phillip Griffiths / Aaron Landesman
> **主教材**：Robin Hartshorne, *Algebraic Geometry* (Graduate Texts in Mathematics 52, Springer 1977)
> **参考教材**：Eisenbud & Harris, *Geometry of Schemes*；Akhil Mathew 笔记
> **Harvard 课程页**：https://www.math.harvard.edu/course/mathematics-232br/

---

## 1. 课程基本信息

| 项目 | 内容 |
|------|------|
| **学分** | 4 Credits（研究生一学期课程） |
| **课时** | MW 2×1.25h / week（参考 2026 Spring 课表） |
| **先修要求** | Math 232ar（或 equivalent 的古典代数几何基础） |
| **主教材** | Hartshorne, *Algebraic Geometry* (GTM 52) |
| **作业形式** | Weekly Problem Set（约 5–8 道/周，多来自 Hartshorne 习题） |
| **核心主题** | Coherent sheaves, cohomology, and their applications to curves and surfaces；偶尔涉及 Hodge structures、Lefschetz theorems、deformations |

---

## 2. 逐章结构表（Module → Hartshorne 章映射）

课程以 Hartshorne 教材为 backbone，通常划分为 5 大模块（含 232ar 复习）。以下按教材章节组织。

| 章号 | 章标题 | 对应周次 | 核心定义列表 | 核心定理列表 | 核心习题数量 | 项目现有文档映射 | 缺失标记 |
|:----:|--------|:--------:|--------------|--------------|:------------:|------------------|:--------:|
| **Module 0** | Review of 232ar (Classical Varieties) | Week 1 | 仿射簇、射影簇、态射、有理映射、维数、非奇异簇 | Bezout 定理、Noether 正规化 | ~15 | `Harvard-232br-L3-定义对齐表.md` | ⚠️ 古典簇的层化定义薄弱 |
| **Ch II** | Schemes | Week 2–5 | 层、预层、结构层 O_X、概形、态射、纤维积、闭浸入、可分/正常态射、拟凝聚层 | 环与仿射概形的范畴等价、Chevalley 定理、Nakayama 引理、Affine Communication Lemma | ~25 | `Harvard-232br-L3-定义对齐表.md` | ⚠️ stalk 泛化定义缺失 |
| **Ch III** | Cohomology | Week 6–10 | 导出函子、层上同调、Čech 上同调、Ext 群与层、Serre 对偶、高次直像 | 仿射概形上同调消没、射影空间上同调计算、Serre 对偶定理、Grothendieck 消没定理 | ~20 | `Harvard-232br-L4-定理对齐表.md` | 🔴 **L5 习题对齐覆盖率仅 ~4.5%** |
| **Ch IV** | Curves | Week 11–14 | Riemann-Roch 定理、Hurwitz 定理、嵌入、椭圆曲线、典则嵌入、曲线分类 | Riemann-Roch 定理、Serre 对偶（曲线版）、Hurwitz 公式、Clifford 定理 | ~15 | `Harvard-232br-L4-定理对齐表.md` | ⚠️ 椭圆曲线群结构证明缺失 |
| **Ch V** | Surfaces | Week 15+ | 曲面上的相交理论、直纹面、单值变换、三次曲面、曲面双有理分类 | Noether 公式、Riemann-Roch 曲面版、Castelnuovo 判别法则 | ~5 | `Harvard-232br-L6-思想方法提炼.md` | 🔴 曲面分类深层证明缺失 |

**说明**：

- 上表“核心习题数量”统计的是 Hartshorne 各章中课程通常选取的习题数（参考 `Harvard-232br-L5-习题对齐表.md` 及历年 Problem Set 惯例）。
- **🔴 严重缺失区**：根据 P1-T3 审计结果，**Harvard 232br L5（习题级对齐表）覆盖率仅约 4.5%**（课程核心习题库中仅有极少数有项目对应文档），标记为银层最高优先级修复目标。

---

## 3. 核心定理列表（L4 级）

| 定理名 | 当前状态 | 对应项目文档路径 | 计划修复动作 |
|--------|----------|------------------|--------------|
| 环与仿射概形的范畴等价 | ⏳ 仅有陈述 | `docs/13-代数几何/01-代数几何基础-深度扩展版.md` | 补充 Spec 函子与全局截面函子互为拟逆证明 |
| Nakayama 引理 | ⏳ 仅有陈述 | `docs/13-代数几何/01-代数几何基础-深度扩展版.md` | 补充有限生成模版本的完整证明 |
| Chevalley 定理（态射的像可构造） | ⏳ 仅有陈述 | `project/Harvard-232br-L4-定理对齐表.md` | 补充 Noetherian 归纳证明 |
| 仿射概形上的层上同调消没 | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充准凝聚层的消没证明 |
| 射影空间 Pⁿ 的上同调计算 | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充 Koszul 复形或 Čech 计算 |
| Serre 对偶定理（概形版） | ⏳ 仅有陈述 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md` | 补充 Ext 层与对偶层构造 |
| Riemann-Roch 定理（光滑射影曲线） | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充由上同调导出的标准证明 |
| Hurwitz 定理（分歧覆盖） | ⏳ 仅有陈述 | `project/Harvard-232br-L4-定理对齐表.md` | 补充微分形式的拉回与次数计算 |
| 椭圆曲线的群结构定理 | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充 Riemann-Roch 构造加法法则 |
| Castelnuovo 判别法则（收缩 (-1)-曲线） | 🔴 完全缺失 | — | 新建定理文档 |
| Noether 公式（代数曲面） | 🔴 完全缺失 | — | 新建定理文档 |

---

## 4. 核心习题列表（L5 级）

| 题号/主题 | 来源（教材/Problem Set） | 当前状态 | 计划修复动作 |
|-----------|------------------------|----------|--------------|
| I-1.6: 仿射簇的闭包 | Hartshorne Ch I + PS | ✅ 已对齐 | `docs/13-代数几何/习题/AG-EX-001-仿射簇的闭包.md` |
| I-3.4: 投影空间中的曲线 | Hartshorne Ch I + PS | ✅ 已对齐 | `docs/13-代数几何/习题/AG-EX-002-投影空间中的曲线.md` |
| II-2.1: Spec 的泛性质 | Hartshorne Ch II + PS | 🔴 缺失 | 新建习题文档 |
| II-2.5: 结构层的茎 | Hartshorne Ch II + PS | 🔴 缺失 | 新建习题文档 |
| II-5.1: 模层的构造 | Hartshorne Ch II + PS | 🔴 缺失 | 新建习题文档 |
| II-5.4: 拟凝聚层的判定 | Hartshorne Ch II + PS | 🔴 缺失 | 新建习题文档 |
| III-2.1: 导出函子的长正合列 | Hartshorne Ch III + PS | 🔴 缺失 | 新建习题文档 |
| III-3.1: 松弛层的上同调 | Hartshorne Ch III + PS | 🔴 缺失 | 新建习题文档 |
| III-4.1: Čech 上同调计算 | Hartshorne Ch III + PS | 🔴 缺失 | 新建 P¹ 与 Pⁿ 的 Čech 计算题 |
| III-5.1: 射影空间上同调 | Hartshorne Ch III + PS | 🔴 缺失 | 新建显式计算题 |
| IV-1.1: Riemann-Roch 应用（亏格 g 曲线） | Hartshorne Ch IV + PS | 🔴 缺失 | 新建应用题 |
| IV-4.1: 椭圆曲线的 Weierstrass 方程 | Hartshorne Ch IV + PS | 🔴 缺失 | 新建习题文档 |
| V-1.1: 曲面上的相交数 | Hartshorne Ch V + PS | 🔴 缺失 | 新建习题文档 |

---

## 5. P1-T3 严重缺失区特别标注

根据前置任务 P1-T3 的审计结果，以下区域被标记为**银层攻坚重点**：

1. **Harvard 232br L5 习题对齐覆盖率仅 ~4.5%**
   - 文件：`project/Harvard-232br-L5-习题对齐表.md`
   - 统计：课程以 Hartshorne Ch II–V 习题为核心，共约 80+ 道精选习题，但项目文档中仅有 **AG-EX-001** 与 **AG-EX-002** 等极少数有完整对应解答。
   - 修复优先级：**最高**。需系统性地为 Hartshorne II–V 各章核心习题建立解答文档。

2. **Ch V (Surfaces) 深层证明缺失**
   - 曲面分类、Castelnuovo 判别、Noether 公式等高级定理在项目文档中多为“提及”或“历史叙述”，缺乏完整证明。
   - 修复动作：优先补充 Castelnuovo 判别的完整证明与 27 条直线的计算示例。

---

## 6. 数据来源 URL

| 来源名称 | URL |
|----------|-----|
| Harvard Math 232br 课程页面 | https://www.math.harvard.edu/course/mathematics-232br/ |
| Harvard Math 232ar (Mandy Cheung) | https://people.math.harvard.edu/~mwcheung/AG1.html |
| Hartshorne, *Algebraic Geometry* (GTM 52) 目录 | https://www.math.stonybrook.edu/~kamenova/homepage_files/Hartshorne_engl.pdf |
| Akhil Mathew 287y 笔记 (Joe Harris) | https://math.uchicago.edu/~amathew/287y.pdf |
| UCI Math 233A-B-C 建议大纲 | https://www.math.uci.edu/syllabus/math233ABC.pdf |
| FormalMath L5 习题对齐表（内部） | `project/Harvard-232br-L5-习题对齐表.md` |
