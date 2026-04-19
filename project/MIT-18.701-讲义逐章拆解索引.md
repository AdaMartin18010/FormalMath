---
title: MIT 18.701 抽象代数 I 讲义逐章拆解索引
msc_primary: 00A99
course_code: MIT 18.701
course_name: Algebra I
instructor: MIT OCW Fall 2010 / Prof. Michael Artin tradition
textbook: "Michael Artin, Algebra, 2nd Edition"
processed_at: '2026-04-17'
---

# MIT 18.701 抽象代数 I 讲义逐章拆解索引

> **任务编号**：P2-T1
> **课程代码**：MIT 18.701
> **课程名称**：Algebra I（抽象代数 I，本科核心）
> **教材**：Michael Artin, *Algebra*, 2nd Edition (Addison Wesley, 2010)
> **OCW 主页**：https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/

---

## 1. 课程基本信息

| 项目 | 内容 |
|------|------|
| **学分** | 12 units（一学期本科荣誉课程） |
| **课时** | Lectures 2×1.5h / week |
| **先修要求** | Linear Algebra (18.700) 或 Analysis I (18.100)；熟悉矩阵运算与基本证明 |
| **主教材** | Artin, *Algebra* (2nd Edition) |
| **作业占比** | Homework 25%；Three Quizzes 75%（每Quiz 25%） |
| **公开资源** | OCW Fall 2010 38 讲 Calendar + 11 份 Problem Set |

---

## 2. 逐章结构表（Session → Artin 教材章映射）

课程主要覆盖 Artin 教材第 1–9 章（学生需自学第 1 章 Matrices）。以下按教材章节组织。

| 章号 | 章标题 | 对应 Session | 核心定义列表 | 核心定理列表 | 核心习题数量 | 项目现有文档映射 | 缺失标记 |
|:----:|--------|:------------:|--------------|--------------|:------------:|------------------|:--------:|
| **Ch 1** | Matrices（自学） | — | 矩阵运算、行列式、逆矩阵、初等矩阵 | 行列式乘法公式、Cramer 法则 | ~10 | `MIT-18.701-L3-定义对齐表.md` | ⚠️ 未系统讲授，仅作复习 |
| **Ch 2** | Groups | Ses 1–7 | 群、子群、同态、同构、陪集、商群、循环群、对称群 Sₙ | Lagrange 定理、对应定理、第一同构定理 | ~18 | `MIT-18.701-L3-定义对齐表.md` | ⚠️ 群作用定义薄弱 |
| **Ch 3** | Vector Spaces | Ses 8–12 | 域、向量空间、基、维数、坐标变换、维数公式 | 维数公式、基的扩张定理 | ~12 | `MIT-18.701-L4-定理对齐表.md` | ⚠️ 直和定义缺失 |
| **Ch 4** | Linear Operators | Ses 13–16 | 特征向量、特征多项式、Jordan 标准型、Cayley-Hamilton | 特征多项式存在性、Jordan 分解定理、Cayley-Hamilton | ~14 | `MIT-18.701-L4-定理对齐表.md` | ⚠️ Jordan 型计算示例不足 |
| **Ch 5** | Applications of Linear Operators | Ses 14–16 | 旋转矩阵、迷向子空间、正交矩阵 | 旋转与反射分类定理 | ~8 | `MIT-18.701-L4-定理对齐表.md` | ⚠️ 旋转矩阵定义缺失 |
| **Ch 6** | Symmetry | Ses 17–23 | 等距变换 (Isometry)、离散群、点群、格、 wallpaper groups | 等距变换分类定理、晶体限制定理 | ~10 | `MIT-18.701-L5-习题对齐表.md` | 🟡 部分有几何直觉文档 |
| **Ch 7** | More Group Theory | Ses 21–26 | 共轭类、类方程、Sylow 定理（选讲）、单群、p-群 | 类方程、Burnside 引理、Aₙ 单性 | ~12 | `MIT-18.701-L5-习题对齐表.md` | ⚠️ Sylow 定理未覆盖 |
| **Ch 8** | Bilinear Forms | Ses 27–31 | 对称型、Hermitian 型、正交性、谱定理、二次曲面 | 谱定理（实/复）、Sylvester 惯性定律 | ~14 | `MIT-18.701-L5-习题对齐表.md` | 🔴 **双线性型定义完全缺失** |
| **Ch 9** | Linear Groups | Ses 32–38 | 典型群 (GLₙ, Oₙ, SU₂, SO₃)、一参数子群、Lie 代数 | SU₂ ≅ 单位四元数、SO₃ 的覆盖 | ~10 | `MIT-18.701-L6-思想方法提炼.md` | ⚠️ Lie 代数仅提及表层 |

**说明**：

- 上表“核心习题数量”统计自 OCW Fall 2010 的 Problem Set 1–11。
- Artin 教材第 10 章 Group Representations 及之后章节（Rings, Fields, Galois Theory）属于 18.702 内容，不在 18.701 范围内。

---

## 3. 核心定理列表（L4 级）

| 定理名 | 当前状态 | 对应项目文档路径 | 计划修复动作 |
|--------|----------|------------------|--------------|
| Lagrange 定理 | ✅ 已有完整证明 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 保持 |
| 群同态基本定理 (First Isomorphism Theorem) | ✅ 已有完整证明 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 保持 |
| 对应定理 (Correspondence Theorem) | ⏳ 仅有陈述 | `project/MIT-18.701-L4-定理对齐表.md` | 补充子群与商群对应证明 |
| 维数公式 (Dimension Formula) | ⏳ 仅有陈述 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | 补充 dim(U+V) 公式证明 |
| Cayley-Hamilton 定理 | ⏳ 仅有陈述 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | 补充特征多项式零化证明 |
| Jordan 标准型存在唯一性 | ⏳ 仅有陈述 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | 补充 Jordan 块分解证明 |
| 谱定理（实对称矩阵） | ⏳ 仅有陈述 | `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml` | 补充正交对角化完整证明 |
| 谱定理（Hermitian 矩阵） | ⏳ 仅有陈述 | `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml` | 补充酉对角化完整证明 |
| 等距变换分类定理 | ⏳ 仅有陈述 | `project/MIT-18.701-L4-定理对齐表.md` | 补充 f(x)=Ax+b 形式证明 |
| 晶体限制定理 (Crystallographic Restriction) | 🔴 完全缺失 | — | 新建定理文档 |
| SU₂ 与 SO₃ 的覆盖同态 | ⏳ 仅有陈述 | `project/MIT-18.701-L6-思想方法提炼.md` | 补充四元数表示证明 |

---

## 4. 核心习题列表（L5 级）

| 题号/主题 | 来源（教材/Problem Set） | 当前状态 | 计划修复动作 |
|-----------|------------------------|----------|--------------|
| PS1-Q2: GLₙ 与 Sₙ 的基本性质 | Artin Ch 2 + PS1 | 🟡 部分有解答 | 补充 S₃ 乘法表完整推导 |
| PS2-Q4: 陪集与 Lagrange 定理应用 | Artin Ch 2 + PS2 | 🟡 部分有解答 | 补充指数计算示例 |
| PS3-Q3: 同态与商群构造 | Artin Ch 2 + PS3 | 🔴 缺失 | 新建习题文档 |
| PS4-Q2: 向量空间基与维数 | Artin Ch 3 + PS4 | 🟡 部分有解答 | 补充直和分解习题 |
| PS5-Q1: 特征多项式与 Jordan 型 | Artin Ch 4 + PS5 | 🔴 缺失 | 新建 3×3 Jordan 型计算题 |
| PS6-Q3: 等距变换与正交矩阵 | Artin Ch 5–6 + PS6 | 🔴 缺失 | 新建平面等距变换分类题 |
| PS7-Q2: 离散群与点群 | Artin Ch 6 + PS7 | 🔴 缺失 | 新建点群分类习题 |
| PS8-Q4: 类方程与 p-群 | Artin Ch 7 + PS8 | 🔴 缺失 | 新建类方程应用题 |
| PS9-Q1: 对称型与正交基 | Artin Ch 8 + PS9 | 🔴 缺失 | 新建 Gram-Schmidt 正交化习题 |
| PS10-Q3: 谱定理与二次曲面 | Artin Ch 8 + PS10 | 🔴 缺失 | 新建二次曲面标准型习题 |
| PS11-Q2: SU₂ / SO₃ 的几何 | Artin Ch 9 + PS11 | 🔴 缺失 | 新建四元数旋转习题 |

---

## 5. P1-T3 严重缺失区特别标注

根据 P1-T3 审计结果，以下区域需要银层生产重点关注：

1. **Ch 8 Bilinear Forms 定义完全缺失**
   - 项目文档中缺少对称双线性型 (Symmetric Form)、Hermitian 型、斜对称型 (Skew-Symmetric Form) 的独立定义文档。
   - 影响：谱定理与二次曲面章节无法建立完整概念链。
   - 修复动作：优先创建 `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/双线性型-定义.md`。

2. **Ch 9 Linear Groups 中 Lie 代数与一参数子群仅表层覆盖**
   - 现有 `MIT-18.701-L6-思想方法提炼.md` 仅作哲学/历史叙述，缺少矩阵指数与 Lie 括号的具体计算。
   - 修复动作：补充矩阵指数定义、su₂ / so₃ 的 Lie 代数同构证明。

---

## 6. 数据来源 URL

| 来源名称 | URL |
|----------|-----|
| MIT OCW 18.701 Syllabus (Fall 2010) | https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/pages/syllabus/ |
| MIT OCW 18.701 Calendar | https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/pages/calendar/ |
| RES.18-011 Algebra I Student Notes (Fall 2021) | https://ocw.mit.edu/courses/res-18-011-algebra-i-student-notes-fall-2021/ |
| Artin, *Algebra* (2nd Ed) Chapter List | https://ccommans.github.io/artin |
| FormalMath L4 定理对齐表（内部） | `project/MIT-18.701-L4-定理对齐表.md` |
