---
title: Stanford FOAG (Ravi Vakil) 代数几何基础讲义逐章拆解索引
msc_primary: 00A99
course_code: Stanford FOAG
course_name: Foundations of Algebraic Geometry
instructor: Ravi Vakil (Stanford Math 216)
textbook: "Ravi Vakil, The Rising Sea: Foundations of Algebraic Geometry"
processed_at: '2026-04-17'
---

# Stanford FOAG (Ravi Vakil) 代数几何基础讲义逐章拆解索引

> **任务编号**：P2-T1
> **课程代码**：Stanford FOAG / Math 216
> **课程名称**：Foundations of Algebraic Geometry（代数几何基础，研究生核心）
> **作者/主讲**：Ravi Vakil
> **主教材**：Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (Princeton University Press, 2024)
> **在线版主页**：https://math.stanford.edu/~vakil/216blog/
> **最新公开草稿**（2025-10-21 版）PDF 链接见教材主页

---

## 1. 课程基本信息

| 项目 | 内容 |
|------|------|
| **学分** | Stanford 研究生标准三学期序列（Math 216A/B/C） |
| **课时** | 通常 3×1h / week（参考 Stanford Math 216 安排） |
| **先修要求** | 交换代数（Atiyah-Macdonald 水平）、基础拓扑与流形、部分同调代数 |
| **主教材** | Vakil, *The Rising Sea*（俗称 FOAG） |
| **作业形式** | 每周 Problem Set，题目几乎全部取自书中 “Important Exercise” 与星号题 |
| **公开资源** | 29 章完整 PDF（约 800+ 道习题）+ 2007–2008 课堂笔记 |

---

## 2. 逐章结构表（Part → Chapter 映射）

FOAG 全书共 29 章，分为 6 个 Part。以下按 Part/Chapter 组织拆解索引。

| Part/章号 | 章标题 | 核心定义列表 | 核心定理列表 | 核心习题数量 | 项目现有文档映射 | 缺失标记 |
|:----------|--------|--------------|--------------|:------------:|------------------|:--------:|
| **Part I** | Preliminaries | | | | | |
| Ch 1 | Just enough category theory | 范畴、函子、Yoneda、极限/余极限、伴随函子、Abel 范畴、谱序列 | Yoneda 引理 | ~10 | `Stanford-FOAG-L3-定义对齐表.md` | ⚠️ 谱序列细节薄弱 |
| Ch 2 | Sheaves | 预层、层、茎 (stalk)、层化 (sheafification)、逆像层、O_X-模 | 层化定理、茎判定正合性 | ~12 | `Stanford-FOAG-L3-定义对齐表.md` | ⚠️ stalk 泛化定义缺失 |
| **Part II** | Schemes | | | | | |
| Ch 3 | Toward affine schemes | Spec A、Zariski 拓扑、结构层、仿射概形 | 环 ⇔ 仿射概形范畴等价 | ~10 | `Stanford-FOAG-L4-定理对齐表.md` | ⚠️ 结构层构造细节待补 |
| Ch 4 | The structure sheaf | 局部化、Distinguished open、O_X 作为层 | 仿射局部性质传递 | ~8 | `Stanford-FOAG-L4-定理对齐表.md` | 🟡 部分有证明骨架 |
| Ch 5 | Some properties of schemes | 可约、整、正规、因子分解、关联点 | 关联点与模糊图像 | ~8 | `Stanford-FOAG-L4-定理对齐表.md` | 🟡 部分有定义 |
| Ch 6 | Morphisms of schemes | 概形态射、有限型、仿射态射、闭浸入、Proj 构造 | Proj 的泛性质 | ~10 | `Stanford-FOAG-L4-定理对齐表.md` | ⚠️ Proj 细节待补 |
| **Part III** | Morphisms | | | | | |
| Ch 7–9 | Finiteness, separated, proper | 纤维积、分离态射、正常态射、泛闭性、Valuative criterion | 既约到分离定理、Chevalley 定理 | ~12 | `Stanford-FOAG-L4-定理对齐表.md` | ⚠️ valuative criterion 证明缺失 |
| Ch 10–11 | Varieties, quasicoherent sheaves | 簇、拟凝聚层、向量丛 | 拟凝聚层的等价刻画 | ~10 | `Stanford-FOAG-L4-定理对齐表.md` | ⚠️ 向量丛与局部自由层对应 |
| **Part IV** | Geometric Properties | | | | | |
| Ch 12 | Dimension | Krull 维数、超越度、Noether 正规化 | Krull 主理想定理、Noether 正规化引理 | ~8 | `Stanford-FOAG-L4-定理对齐表.md` | ⚠️ 维数理论证明薄弱 |
| Ch 13 | Regularity & smoothness | 正则局部环、光滑态射、Zariski 切空间、Bertini 定理 | 光滑 ⇔ 正则 + 相对维数条件 | ~8 | `Stanford-FOAG-L4-定理对齐表.md` | 🔴 深层证明缺失 |
| **Part V** | Quasicoherent Sheaves | | | | | |
| Ch 14–16 | Line bundles, maps to Pⁿ, divisors | 线丛、Cartier/Weil 除子、线性系、丰沛除子 | 除子与线丛的对应 | ~10 | `Stanford-FOAG-L5-习题对齐表.md` | 🟡 部分有计算示例 |
| Ch 17–22 | Cohomology, curves, differentials, blow-ups | Čech 上同调、Riemann-Roch、Serre 消失、交截理论、微分形式 | Riemann-Roch、Serre 消失、Grothendieck 凝聚定理 | ~14 | `Stanford-FOAG-L5-习题对齐表.md` | ⚠️ 上同调计算题不足 |
| **Part VI** | More Cohomological Tools | | | | | |
| Ch 23–25 | Derived functors, flatness, base change | Tor、导出函子、平坦性、上同调与基变换 | 上同调与基变化定理、局部平坦判别 | ~10 | `Stanford-FOAG-L6-思想方法提炼.md` | 🔴 证明极度稀缺 |
| Ch 26 | Depth & Cohen-Macaulayness | 深度、Cohen-Macaulay 环、Serre R1+S2 判别 | 正规性判别 | ~6 | `Stanford-FOAG-L6-思想方法提炼.md` | 🔴 缺失 |
| Ch 27 | 27 lines on a cubic surface | 三次曲面上的 27 条直线 | 27 条直线的存在与双有理结构 | ~4 | `Stanford-FOAG-L6-思想方法提炼.md` | 🔴 缺失 |
| Ch 28–29 | Formal functions, Serre duality | 形式函数定理、Zariski 主定理、Serre 对偶 | 形式函数定理、Serre 对偶的完整证明 | ~8 | `Stanford-FOAG-L6-思想方法提炼.md` | 🔴 缺失 |

**说明**：

- 上表“核心习题数量”为每章精选的 “Important Exercise” 与星号题数量（参考 `Stanford-FOAG-L5-习题对齐表.md` 及 2022 草稿标记）。全书约 800+ 习题，课程通常每学期覆盖 80–120 道。
- **🔴 严重缺失区**：Part VI（Ch 23–29）在项目文档中证明极度稀缺，多为历史/哲学叙述或仅列陈述，需优先补充。

---

## 3. 核心定理列表（L4 级）

| 定理名 | 当前状态 | 对应项目文档路径 | 计划修复动作 |
|--------|----------|------------------|--------------|
| Yoneda 引理 | ✅ 已有完整证明 | `docs/13-代数几何/01-代数几何基础-深度扩展版.md` | 保持 |
| 层化定理 (Sheafification) | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充显式构造与泛性质证明 |
| 环 ⇔ 仿射概形范畴等价 | ⏳ 仅有陈述 | `docs/13-代数几何/01-代数几何基础-深度扩展版.md` | 补充 Spec–Γ 伴随等价证明 |
| Affine Communication Lemma | ⏳ 仅有陈述 | `project/Stanford-FOAG-L4-定理对齐表.md` | 补充局部到整体传递证明 |
| Chevalley 定理 | ⏳ 仅有陈述 | `project/Stanford-FOAG-L4-定理对齐表.md` | 补充可构造集归纳证明 |
| Nakayama 引理 | ⏳ 仅有陈述 | `docs/13-代数几何/01-代数几何基础-深度扩展版.md` | 补充有限生成模版本证明 |
| Krull 主理想定理 | ⏳ 仅有陈述 | `project/Stanford-FOAG-L4-定理对齐表.md` | 补充 Noether 正规化证明路径 |
| Noether 正规化引理 | ⏳ 仅有陈述 | `project/Stanford-FOAG-L4-定理对齐表.md` | 补充整性扩张构造证明 |
| Serre 消失定理 | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充 Čech 计算证明 |
| Grothendieck 凝聚定理 | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充 proper + 有限型推导 |
| Riemann-Roch（曲线） | ⏳ 仅有陈述 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 补充上同调版本完整证明 |
| Serre 对偶定理 | ⏳ 仅有陈述 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md` | 补充 Ext 层与对偶层构造 |
| 上同调与基变化定理 | 🔴 完全缺失 | — | 新建定理文档 |
| 形式函数定理 (Theorem on Formal Functions) | 🔴 完全缺失 | — | 新建定理文档 |
| Zariski 主定理 | 🔴 完全缺失 | — | 新建定理文档 |
| Castelnuovo 判别法则 | 🔴 完全缺失 | — | 新建定理文档 |

---

## 4. 核心习题列表（L5 级）

| 题号/主题 | 来源（教材/Problem Set） | 当前状态 | 计划修复动作 |
|-----------|------------------------|----------|--------------|
| Ex 1.3.Y: Yoneda 引理的显式证明 | FOAG Ch 1 | 🟡 部分有解答 | 补充自然同构的完整验证 |
| Ex 2.4.B: 层在基上的恢复 | FOAG Ch 2 | 🔴 缺失 | 新建习题文档 |
| Ex 2.5.D: 逆像层的泛性质 | FOAG Ch 2 | 🔴 缺失 | 新建习题文档 |
| Ex 3.7.E: Spec A 的不可约闭子集与素理想一一对应 | FOAG Ch 3 | 🟡 部分有解答 | 补充双射的完整验证 |
| Ex 4.7.E: 不可约闭子集与素理想 | FOAG Ch 4 | 🟡 部分有解答 | 保持 |
| Ex 6.3.M: Proj 的泛性质 | FOAG Ch 6 | 🔴 缺失 | 新建习题文档 |
| Ex 7.3.D: Chevalley 定理的证明 | FOAG Ch 7 | 🔴 缺失 | 新建习题文档 |
| Ex 8.3.E: 概形式像的构造 | FOAG Ch 8 | 🔴 缺失 | 新建习题文档 |
| Ex 11.3.B: 拟凝聚层的等价条件 | FOAG Ch 11 | 🔴 缺失 | 新建习题文档 |
| Ex 15.3.F: 到 Pⁿ 的映射与线丛 | FOAG Ch 15 | 🔴 缺失 | 新建习题文档 |
| Ex 18.3.A: Čech 上同调 = 导出函子上同调 | FOAG Ch 18 | 🔴 缺失 | 新建证明习题 |
| Ex 19.2.B: Riemann-Roch 的显式计算 | FOAG Ch 19 | 🔴 缺失 | 新建计算题 |
| Ex 24.5.J/K: 平坦性的拓扑含义 | FOAG Ch 24 | 🔴 缺失 | 新建习题文档 |
| Ex 25.2.E: 上同调与基变化的应用 | FOAG Ch 25 | 🔴 缺失 | 新建习题文档 |

---

## 5. P1-T3 严重缺失区特别标注

根据 P1-T3 审计与现有对齐表分析，FOAG 的以下区域需要银层生产重点关注：

1. **Part VI (Ch 23–29) 证明极度稀缺**
   - `Stanford-FOAG-L6-思想方法提炼.md` 对导出函子、平坦性、深度、Cohen-Macaulayness、形式函数定理、Serre 对偶等主题仅有“哲学/历史叙述”，缺少手写数学证明。
   - 修复优先级：**高**。这部分是研究生代数几何资格考试的必考内容。

2. **stalk 的泛化定义缺失**
   - `D020-stanford-foag-definition-alignment.md` 明确指出：项目文档在 `08-预层与层化.md` 中**完全缺失 stalk 的一般定义**，仅在结构层特例中出现。这直接影响 “exactness can be checked at stalks” 等后续定理的教学。
   - 修复动作：在 L3 定义对齐表中优先补充 stalk 的独立定义文档。

---

## 6. 数据来源 URL

| 来源名称 | URL |
|----------|-----|
| FOAG 官方主页（含最新 PDF） | https://math.stanford.edu/~vakil/216blog/ |
| FOAG HTML 目录（第三方镜像） | https://wanminliu.github.io/Ravi_AG/Ravi_AG.html |
| FOAG 2022 公开草稿 PDF | https://math.stanford.edu/~vakil/216blog/FOAGaug2922public.pdf |
| Stanford Math 216 2007–2008 课堂笔记 | https://math.stanford.edu/~vakil/0708-216/ |
| Berkeley Math 256A-B (Mark Haiman) | https://math.berkeley.edu/~mhaiman/math256-fall18-spring19/ |
| FormalMath L4 定理对齐表（内部） | `project/Stanford-FOAG-L4-定理对齐表.md` |
| FormalMath L3 定义对齐表（内部） | `project/Stanford-FOAG-L3-定义对齐表.md` |
