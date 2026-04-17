---
title: MIT 18.06 线性代数讲义逐章拆解索引
course_code: MIT 18.06
course_name: Linear Algebra
instructor: Prof. Gilbert Strang (MIT OCW Spring 2010)
textbook: "Gilbert Strang, Introduction to Linear Algebra, 4th Edition"
processed_at: '2026-04-17'
---

# MIT 18.06 线性代数讲义逐章拆解索引

> **任务编号**：P2-T1
> **课程代码**：MIT 18.06
> **课程名称**：Linear Algebra（线性代数，本科核心）
> **主讲教师**：Prof. Gilbert Strang（Spring 2010）
> **主教材**：Gilbert Strang, *Introduction to Linear Algebra*, 4th Edition (Wellesley-Cambridge Press, 2009)
> **OCW 主页**：https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/

---

## 1. 课程基本信息

| 项目 | 内容 |
|------|------|
| **学分** | 12 units（MIT 本科标准一学期课程） |
| **课时** | Lectures 3×1h / week；Recitations 1×1h / week |
| **先修要求** | 18.02 Multivariable Calculus |
| **主教材** | Strang, *Introduction to Linear Algebra*, 4th Edition |
| **作业占比** | Problem Sets 15%；Three one-hour exams 45%；Final exam 40% |
| **公开资源** | 34 讲完整视频 + PS1–PS10 + Exam 1/2/3 + Final |

---

## 2. 逐章结构表（Lecture → Strang 教材章映射）

| 章号 | 章标题 | 对应 Lecture | 核心定义列表 | 核心定理列表 | 核心习题数量 | 项目现有文档映射 | 缺失标记 |
|:----:|--------|:------------:|--------------|--------------|:------------:|------------------|:--------:|
| **Ch 1** | Introduction | L1 | 向量、点积、线性组合、列图像/行图像 | — | ~4 | `v2-quality-rewrite/deliverables/D018-mit-18-06-definition-alignment.md` | ⚠️ 基础定义尚可 |
| **Ch 2** | Solving Linear Equations | L2–L4 | 消元法、初等矩阵、置换矩阵、LU 分解、逆矩阵 | A=LU 存在性、(AB)⁻¹ 公式 | ~8 | `v2-quality-rewrite/deliverables/D018-mit-18-06-definition-alignment.md` | ⚠️ 置换矩阵证明薄弱 |
| **Ch 3** | Vector Spaces and Subspaces | L5–L10 | 子空间、列空间 C(A)、零空间 N(A)、秩、RREF、基、维数、四大子空间 | Rank-Nullity 定理、解的结构定理 x=xₚ+xₙ | ~14 | `v2-quality-rewrite/deliverables/D018-mit-18-06-definition-alignment.md` | ⚠️ 左零空间直觉不足 |
| **Ch 8§1–2** | Applications: Graphs & Networks, Markov Matrices | L11–L12 | 关联矩阵 (Incidence Matrix)、稳定/不稳定子空间、Markov 矩阵、稳态分布 | 基尔霍夫定律的矩阵形式 | ~6 | `v2-quality-rewrite/deliverables/D018-mit-18-06-definition-alignment.md` | 🔴 **关联矩阵与网络视角完全缺失** |
| **Ch 4** | Orthogonality | L14–L17 | 正交子空间、投影矩阵、最小二乘、Gram-Schmidt、QR 分解 | 投影矩阵公式 P=A(AᵀA)⁻¹Aᵀ、正交补维数公式 | ~10 | — | 🔴 **L4 定理对齐表完全缺失** |
| **Ch 5** | Determinants | L18–L20 | 行列式 10 条性质、余子式展开、Cramer 法则、行列式=有向体积 | det(AB)=det(A)det(B)、逆矩阵公式 | ~8 | — | 🔴 **L4 定理对齐表完全缺失** |
| **Ch 6** | Eigenvalues and Eigenvectors | L21–L25 | 特征值/特征向量、对角化、矩阵指数 e^(At)、对称矩阵、正定矩阵、Markov 矩阵 | 谱定理（实对称）、正定矩阵判别 | ~12 | — | 🔴 **L4-L6 完全缺失** |
| **Ch 7** | Linear Transformations | L26, L30–L31 | 线性变换矩阵、基变换、SVD、伪逆 | SVD 存在性定理、Jordan 型 | ~8 | — | 🔴 **L4-L6 完全缺失** |
| **Ch 10** | Complex Vectors and Complex Matrices | L26 | 复数、Hermitian 矩阵、酉矩阵、快速傅里叶变换 (FFT) | FFT 算法复杂度 O(n log n) | ~4 | `v2-quality-rewrite/deliverables/D018-mit-18-06-definition-alignment.md` | 🔴 **傅里叶矩阵定义完全缺失** |
| **Ch 8§3–5** | Applications: Linear Programming, Computer Graphics, FFT | L24, L29, L33 | 线性规划、计算机图形学、伪逆 | — | ~4 | — | 🔴 **L4-L6 完全缺失** |

**说明**：

- 上表“核心习题数量”统计自 MIT OCW Spring 2010 的 PS1–PS10。
- **🔴 严重缺失区**：根据 P1-T3 审计结果，**MIT 18.06 L4（定理级）、L5（习题级）、L6（思想方法级）文档在项目根目录 `project/` 下完全缺失**。目前仅在 `project/v2-quality-rewrite/deliverables/D008-mit-18-06-syllabus.yaml` 中有 syllabus 级拆解，尚未生成 L3–L6 的对齐表。

---

## 3. 核心定理列表（L4 级）

| 定理名 | 当前状态 | 对应项目文档路径 | 计划修复动作 |
|--------|----------|------------------|--------------|
| A = LU 分解定理（带行置换） | 🔴 完全缺失 | — | **新建** `MIT-18.06-L4-定理对齐表.md`，补充 PLU 存在唯一性证明 |
| Rank-Nullity 定理 | 🟡 仅有 Mathlib 路径 | `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/linear-map.yaml` | 提取为独立定理文档并补充 Strang 视角证明 |
| 投影矩阵公式 P = A(AᵀA)⁻¹Aᵀ | 🔴 完全缺失 | — | 新建最小二乘几何证明文档 |
| QR 分解存在性定理 | 🔴 完全缺失 | — | 新建 Gram-Schmidt 构造证明 |
| det(AB) = det(A)det(B) | 🔴 完全缺失 | — | 新建行列式乘积性质证明 |
| 实对称矩阵谱定理 | 🟡 仅有骨架 | `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml` | 补充 18.06 版本的几何解释与完整证明 |
| 正定矩阵等价判别（5 条件） | 🔴 完全缺失 | — | 新建正定矩阵判定定理文档 |
| SVD 存在性定理 | 🔴 完全缺失 | — | 新建 SVD 存在性证明文档 |
| Cayley-Hamilton 定理 | 🔴 完全缺失 | — | 新建特征多项式零化证明 |
| Jordan 标准型存在唯一性 | 🔴 完全缺失 | — | 新建 Jordan 型计算与证明文档 |

---

## 4. 核心习题列表（L5 级）

| 题号/主题 | 来源（教材/Problem Set） | 当前状态 | 计划修复动作 |
|-----------|------------------------|----------|--------------|
| PS1-Q1: 向量的几何解释与线性组合 | Strang §1.2–1.3 + PS1 | 🟡 部分有解答 | 补充列图像与行图像对比 |
| PS2-Q3: LU 分解与置换矩阵 | Strang §2.5–2.6 + PS2 | 🔴 缺失 | 新建计算题 + 证明题 |
| PS3-Q2: 零空间与特解的结构 | Strang §3.2–3.4 + PS3 | 🔴 缺失 | 新建 Ax=0 通解构造习题 |
| PS4-Q4: 基、维数与四大子空间 | Strang §3.5–3.6 + PS4 | 🔴 缺失 | 新建秩-零化度应用题 |
| PS5-Q1: 最小二乘与投影矩阵 | Strang §4.1–4.2 + PS5 | 🔴 缺失 | 新建拟合直线计算题 |
| PS6-Q2: 行列式性质与体积解释 | Strang §5.1–5.3 + PS6 | 🔴 缺失 | 新建 3×3 行列式几何题 |
| PS7-Q3: 特征值、特征向量与对角化 | Strang §6.1–6.2 + PS7 | 🔴 缺失 | 新建特征系统计算题 |
| PS8-Q2: 对称矩阵与正定矩阵 | Strang §6.4–6.5 + PS8 | 🔴 缺失 | 新建谱定理应用题 |
| PS9-Q1: SVD 与图像压缩 | Strang §6.7 + PS9 | 🔴 缺失 | 新建低秩逼近计算题 |
| PS10-Q2: 线性变换与基变换 | Strang §7.1–7.3 + PS10 | 🔴 缺失 | 新建相似矩阵与坐标变换题 |

---

## 5. P1-T3 严重缺失区特别标注

根据前置任务 P1-T3 的发现，MIT 18.06 是五门银层课程中**对齐文档缺失最严重**的一门：

1. **L4–L6 文档完全缺失**
   - 在项目 `project/` 目录下，不存在 `MIT-18.06-L4-定理对齐表.md`、`MIT-18.06-L5-习题对齐表.md`、`MIT-18.06-L6-思想方法提炼.md`。
   - 目前仅有 syllabus 级拆解（`D008-mit-18-06-syllabus.yaml`）和 L3 定义对齐初稿（`D018-mit-18-06-definition-alignment.md`）。
   - 修复优先级：**最高**。必须先完成 L4–L6 对齐表，才能进入银层文档生产。

2. **定义层缺失**
   - `D018-mit-18-06-definition-alignment.md` 指出：关联矩阵 (Incidence Matrix)、稳定/不稳定/中心子空间、傅里叶矩阵等 Strang 课程特色定义在项目文档中**完全缺失**。
   - 修复动作：在生成 L3 对齐表时优先补全上述定义。

---

## 6. 数据来源 URL

| 来源名称 | URL |
|----------|-----|
| MIT OCW 18.06 Syllabus (Spring 2010) | https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/pages/syllabus/ |
| MIT OCW 18.06 Video Lectures (34 lectures) | https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/video_galleries/video-lectures/ |
| MIT OCW 18.06 Assignments (PS1–PS10) | https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/pages/assignments/ |
| Strang, *Introduction to Linear Algebra* (4th Ed TOC) | http://www-math.mit.edu/~gs/books/ila2_toc.html |
| MIT 18.06 Spring 2010 课程主页 | https://web.mit.edu/18.06/www/Spring10/index.html |
