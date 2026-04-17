---
title: MIT 18.100A 实分析讲义逐章拆解索引
course_code: MIT 18.100A
course_name: Real Analysis
instructor: Dr. Casey Rodriguez (MIT OCW Fall 2020)
textbook: "Jiri Lebl, Basic Analysis I: Introduction to Real Analysis, Volume 1"
processed_at: '2026-04-17'
---

# MIT 18.100A 实分析讲义逐章拆解索引

> **任务编号**：P2-T1
> **课程代码**：MIT 18.100A
> **课程名称**：Real Analysis（实分析，本科基础）
> **主讲教师**：Dr. Casey Rodriguez（Fall 2020）
> **主教材**：Jiri Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume 1* (CreateSpace, 2018)
> **OCW 主页**：https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/

---

## 1. 课程基本信息

| 项目 | 内容 |
|------|------|
| **学分** | 12 units（MIT 本科标准一学期课程） |
| **课时** | Lectures 2×1h / week；Recitations 1×1h / week |
| **先修要求** | 18.02 Multivariable Calculus；具备基本证明书写能力 |
| **主教材** | Lebl, *Basic Analysis I*（可免费阅读 PDF） |
| **作业占比** | Assignments 1–12 占 50%；Midterm 占 25%；Final Assignment 占 25% |
| **公开资源** | 25 讲预录视频 + 12 份 Problem Set + Recitation Handouts |

---

## 2. 逐章结构表（Lecture → 教材章映射）

课程按 Lebl 教材章节组织，共分为 6 大章（含前置集合论）。以下表格将 25 讲视频映射到教材章节，并列出核心定义、定理、习题数量及项目现有文档映射。

| 章号 | 章标题 | 对应 Lecture | 核心定义列表 | 核心定理列表 | 核心习题数量 | 项目现有文档映射 | 缺失标记 |
|:----:|--------|:------------:|--------------|--------------|:------------:|------------------|:--------:|
| **Ch 0** | Basic Set Theory（前置） | L1 | 集合运算、数学归纳法、有理数构造、等价类 | 归纳原理 | ~8 | `MIT-18.100A-L3-定义对齐表.md` | ⚠️ 基数/可数集定义缺失 |
| **Ch 1** | Real Numbers | L2–L6 | 实数完备性、LUB、Archimedean 性质、绝对值、稠密性、不可数性 | Cantor 定理、实数刻画定理 | ~12 | `MIT-18.100A-L3-定义对齐表.md` | 🔴 **L4 定理覆盖仅 16.7%**（2/12 完整） |
| **Ch 2** | Sequences and Series | L7–L12 | 序列极限、子列、limsup/liminf、Cauchy 序列、级数收敛 | 单调收敛定理、BW 定理、Cauchy 准则、比较/比值/根值/交错判别法 | ~18 | `MIT-18.100A-L4-定理对齐表.md` | ⚠️ 大量证明待补充 |
| **Ch 3** | Continuous Functions | L13–L16 | 函数极限、连续性、一致连续性、Dirichlet 函数 | 夹逼定理、极值定理、介值定理、一致连续性与紧性 | ~10 | `MIT-18.100A-L5-习题对齐表.md` | ⚠️ 一致连续性证明缺失 |
| **Ch 4** | The Derivative | L17–L20 | 导数定义、Rolle/MVT、Taylor 多项式、Weierstrass 反例 | 求导法则、Rolle 定理、MVT、Taylor 定理 | ~10 | `MIT-18.100A-L5-习题对齐表.md` | ⚠️ Rolle 定理证明待补充 |
| **Ch 5** | The Riemann Integral | L21–L22 | Riemann 和、可积性、FTC、换元/分部积分 | FTC（第一、第二形式）、积分中值定理 | ~8 | `MIT-18.100A-L6-思想方法提炼.md` | ⚠️ 可积准则证明缺失 |
| **Ch 6** | Sequences of Functions | L23–L25 | 点态收敛、一致收敛、Weierstrass M-判别法、幂级数 | 一致收敛保持连续性/积分、Weierstrass 逼近定理 | ~10 | `MIT-18.100A-L6-思想方法提炼.md` | ⚠️ 极限交换定理证明缺失 |

**说明**：

- 上表“核心习题数量”统计的是课程 Assignments 1–12 + Final Assignment 中各章对应的题目数，不含 Recitation。
- **🔴 严重缺失区**：根据 P1-T3 审计结果，**MIT 18.100A L4（定理级对齐表）仅 16.7% 完整**（12 道核心定理中仅 2 道有完整证明），标记为关键修复目标。

---

## 3. 核心定理列表（L4 级）

| 定理名 | 当前状态 | 对应项目文档路径 | 计划修复动作 |
|--------|----------|------------------|--------------|
| 单调收敛定理 (Monotone Convergence Theorem) | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/单调收敛定理-证明.md` | 补充 ε-N 完整证明 |
| Bolzano-Weierstrass 定理 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/Bolzano-Weierstrass定理-证明.md` | 补充二分法构造性证明 |
| Cauchy 收敛准则 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/柯西收敛准则-证明.md` | 补充完备性等价证明 |
| 中间值定理 (IVT) | ✅ 已有完整证明 | `docs/03-分析学/01-实分析/中间值定理-证明.md` | 保持 |
| 极值定理 (Extreme Value Theorem) | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/极值定理-证明.md` | 补充紧集上连续函数证明 |
| Heine-Borel 定理 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/Heine-Borel定理-证明.md` | 补充 ℝⁿ 版本证明 |
| Rolle 定理 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/Rolle定理-证明.md` | 补充辅助函数构造证明 |
| 中值定理 (MVT) | ✅ 已有完整证明 | `docs/03-分析学/01-实分析/中值定理-证明.md` | 保持 |
| Taylor 定理 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/Taylor定理-证明.md` | 补充 Lagrange 余项证明 |
| 微积分基本定理 (FTC) | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/微积分基本定理-证明.md` | 补充两部分互推证明 |
| 一致收敛保持连续性 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/一致收敛连续性定理-证明.md` | 补充极限交换证明 |
| Weierstrass M-判别法 | ⏳ 仅有陈述 | `docs/03-分析学/01-实分析/Weierstrass-M判别法-证明.md` | 补充 Cauchy 一致收敛证明 |

**状态图例**：

- ✅ 已有完整证明（含详细推导）
- ⏳ 仅有陈述 / 证明骨架 / 完全缺失

---

## 4. 核心习题列表（L5 级）

| 题号/主题 | 来源（教材/Problem Set） | 当前状态 | 计划修复动作 |
|-----------|------------------------|----------|--------------|
| PS1-Q1: 集合运算与归纳法 | Assignment 1 (Lebl §0.3) | 🟡 部分有解答 | 补全归纳步骤细节 |
| PS2-Q3: 实数完备性与 Archimedean 性质 | Assignment 2 (Lebl §1.2–1.3) | 🔴 缺失 | 新建习题文档 |
| PS3-Q2: 子列构造与聚点 | Assignment 3 (Lebl §2.1–2.2) | 🟡 部分有解答 | 补充三聚点构造示例 |
| PS4-Q5: 有界性 vs 收敛子列辨析 | Assignment 4 (Lebl §2.3) | ✅ 已对齐 | 保持（见 `docs/analysis/sequential-compactness.md`） |
| PS5-Q1: 级数收敛判别综合 | Assignment 5 (Lebl §2.5–2.6) | 🔴 缺失 | 新建习题文档 |
| PS6-Q2: 一致连续性证明 | Assignment 6 (Lebl §3.4) | 🔴 缺失 | 新建习题文档 |
| PS7-Q3: Rolle/MVT 应用 | Assignment 7 (Lebl §4.2) | 🟡 部分有解答 | 补充中值不等式应用 |
| PS8-Q4: Taylor 展开与误差估计 | Assignment 8 (Lebl §4.3) | 🔴 缺失 | 新建习题文档 |
| PS9-Q2: FTC 与积分计算 | Assignment 9 (Lebl §5.3) | 🔴 缺失 | 新建习题文档 |
| PS10-Q1: 一致收敛与极限交换 | Assignment 10 (Lebl §6.1–6.2) | 🔴 缺失 | 新建习题文档 |
| PS11-Q3: 幂级数收敛半径 | Assignment 11 (Lebl §6.1–6.2) | 🔴 缺失 | 新建习题文档 |
| PS12-Q2: Weierstrass 逼近定理应用 | Assignment 12 (Lebl §6.3) | 🔴 缺失 | 新建习题文档 |
| Final: 实分析综合证明 | Final Assignment | 🔴 缺失 | 设计综合压轴题 |

**状态图例**：

- ✅ 已有完整解答对齐
- 🟡 部分有解答 / 变体对应
- 🔴 完全缺失

---

## 5. P1-T3 严重缺失区特别标注

根据前置任务 P1-T3（内容审计与对齐）的发现，以下区域被标记为**银层攻坚重点**：

1. **MIT 18.100A L4（定理级对齐表）完整性仅 16.7%**
   - 文件：`project/MIT-18.100A-L4-定理对齐表.md`
   - 统计：12 道核心定理中，仅 **中间值定理** 与 **中值定理** 标记为“完整”(✅)，其余 10 道均为“待补充”(⏳)。
   - 修复优先级：**最高**（影响后续微积分与函数序列章节）。

2. **L3 定义对齐表缺失率 56.8%**
   - 大量基础概念（可数集、绝对值、子列、limsup/liminf、一致连续、Lipschitz 连续、点态/一致收敛等）在项目文档中完全缺失。
   - 修复动作：优先补充 Ch 1–Ch 3 的基础定义文档。

---

## 6. 数据来源 URL

| 来源名称 | URL |
|----------|-----|
| MIT OCW 18.100A Syllabus (Fall 2020) | https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/pages/syllabus/ |
| MIT OCW 18.100A Calendar | https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/pages/calendar/ |
| MIT OCW 18.100A Problem Sets | https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/resources/problem-sets/ |
| Lebl, *Basic Analysis I* (免费 PDF) | https://www.jirka.org/ra/realanal.pdf |
| FormalMath L4 定理对齐表（内部） | `project/MIT-18.100A-L4-定理对齐表.md` |
