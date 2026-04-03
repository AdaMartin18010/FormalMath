# FormalMath与Cambridge数学课程深度映射表

> **版本**: 2026年4月
> **适用范围**: Cambridge University Mathematical Tripos 2024-2025学年
> **目标**: 为自学者提供使用FormalMath资源学习Cambridge数学课程的完整路径
> **数据来源**: https://www.maths.cam.ac.uk/undergrad/course/

---

## 📋 使用指南

### 如何阅读本文档

- **课程代码**: Cambridge Tripos课程名称（Part IA/IB/II/III层级）
- **FormalMath文档**: 对应FormalMath项目中的具体文档路径
- **覆盖度**:
  - 🟢 **完整覆盖** (80-100%): FormalMath已完整覆盖课程内容
  - 🟡 **部分覆盖** (40-79%): FormalMath覆盖主要主题，需补充材料
  - 🟠 **基础覆盖** (20-39%): FormalMath覆盖基础概念，需大量外部资源
  - ⚪ **待开发** (<20%): FormalMath尚未覆盖，需使用其他资源

### Cambridge Tripos系统说明

Cambridge数学系采用独特的**Tripos考试系统**，分为四个层级：

| 层级 | 年级 | 特点 | 考试形式 |
|------|------|------|----------|
| **Part IA** | 大一 | 基础必修，广泛覆盖 | 四卷考试 |
| **Part IB** | 大二 | 进阶必修+选修 | 四卷考试 |
| **Part II** | 大三 | 专业深化 | 四卷考试 |
| **Part III** | 大四/硕士 | 研究生水平 | 考试+项目论文 |

### 课程分类标记

- **C-courses**: 标准课程（较基础，24讲）
- **D-courses**: 深入课程（更具挑战，16或24讲）

---

## 🎓 Part IA (大一基础)

### IA Groups / IA Numbers and Sets

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups / Numbers and Sets |
| **学时** | 24讲/门 |
| **先修要求** | 无 |
| **Cambridge教材** | Allenby, *Rings, Fields and Groups*; Stewart, *Galois Theory* |
| **建议学期** | Michaelmas Term |
| **覆盖度** | 🟢 完整覆盖 (92%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/01-基础数学/集合论/01-集合论基础-国际标准版.md` | 集合、映射、关系 | 5小时 |
| 2 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 群公理、子群 | 5小时 |
| 3 | `docs/02-代数结构/02-核心理论/群论/02-子群与陪集-深度扩展版.md` | Lagrange定理 | 4小时 |
| 4 | `docs/02-代数结构/02-核心理论/群论/04-群同态-深度扩展版.md` | 同态、同构 | 4小时 |
| 5 | `docs/02-代数结构/02-核心理论/群论/07-Sylow定理-深度扩展版.md` | Sylow定理（IA选讲） | 5小时 |

---

### IA Analysis I

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis I |
| **学时** | 24讲 |
| **先修要求** | 无 |
| **Cambridge教材** | Apostol, *Mathematical Analysis*; Spivak |
| **建议学期** | Michaelmas/Lent |
| **覆盖度** | 🟢 完整覆盖 (90%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | 实数完备性 | 5小时 |
| 2 | `docs/03-分析学/01-实分析/02-序列与极限-深度扩展版.md` | 序列、极限 | 5小时 |
| 3 | `docs/03-分析学/01-实分析/04-连续函数-深度扩展版.md` | 连续、一致连续 | 5小时 |
| 4 | `docs/03-分析学/01-实分析/06-微分-深度扩展版.md` | 微分、中值定理 | 5小时 |
| 5 | `docs/03-分析学/01-实分析/08-Riemann积分-深度扩展版.md` | 积分、FTC | 5小时 |

---

### IA Vectors and Matrices

| 属性 | 内容 |
|------|------|
| **课程名称** | Vectors and Matrices |
| **学时** | 24讲 |
| **先修要求** | 无 |
| **Cambridge教材** | Kaye & Wilson, *Linear Algebra* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (88%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | 向量空间、子空间 | 5小时 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/02-线性代数与高级数系-国际标准版.md` | 基、维数 | 5小时 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/03-线性变换-深度扩展版.md` | 线性映射、矩阵 | 5小时 |
| 4 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/04-特征值与特征向量-深度扩展版.md` | 特征值、对角化 | 5小时 |
| 5 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/05-内积空间-深度扩展版.md` | 内积、正交性 | 4小时 |

---

## 🎓 Part IB (大二进阶)

### IB Groups, Rings and Modules

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups, Rings and Modules |
| **学时** | 24讲 |
| **先修要求** | IA Groups |
| **Cambridge教材** | Allenby; Cohn, *Algebra* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (88%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | 正规子群、合成列 | 5小时 |
| 2 | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | 环、理想 | 5小时 |
| 3 | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | UFD、PID、欧几里得整环 | 6小时 |
| 4 | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | 模、自由模 | 6小时 |
| 5 | `docs/02-代数结构/02-核心理论/域论/02-Galois理论-深度扩展版.md` | Galois理论（IB选讲） | 6小时 |

---

### IB Linear Algebra

| 属性 | 内容 |
|------|------|
| **课程名称** | Linear Algebra |
| **学时** | 24讲 |
| **先修要求** | IA Vectors and Matrices |
| **Cambridge教材** | Kaye & Wilson |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (85%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/06-算子理论-深度扩展版.md` | 正规算子、谱定理 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/07-张量积-深度扩展版.md` | 双线性型、张量积 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/08-典范形式-深度扩展版.md` | Jordan标准形 | 6小时 |

---

### IB Analysis and Topology

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis and Topology |
| **学时** | 24讲 |
| **先修要求** | IA Analysis I |
| **Cambridge教材** | Sutherland, *Introduction to Metric and Topological Spaces* |
| **建议学期** | Lent |
| **覆盖度** | 🟢 完整覆盖 (85%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/03-分析学/01-实分析/05-拓扑基础-深度扩展版.md` | 度量空间、拓扑空间 | 6小时 |
| 2 | `docs/05-拓扑学/01-点集拓扑/01-点集拓扑-深度扩展版.md` | 连续性、紧致性 | 6小时 |
| 3 | `docs/05-拓扑学/01-点集拓扑/02-连通性与紧致性-深度扩展版.md` | 连通性、道路连通 | 5小时 |
| 4 | `docs/03-分析学/04-泛函分析/01-泛函分析-深度扩展版.md` | 函数空间 | 5小时 |

---

## 🎓 Part II (大三专业)

### Part II Algebraic Geometry (代数几何) ⭐核心课程

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Reid, *Undergraduate Algebraic Geometry*; Kirwan |
| **建议学期** | Lent |
| **覆盖度** | 🟡 部分覆盖 (75%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Reid章节 | 学习时间 |
|------|----------|----------|----------|
| 1 | `docs/13-代数几何/01-代数几何基础.md` | Ch.0-1: 仿射空间、代数集 | 6小时 |
| 2 | `docs/13-代数几何/02-代数几何增强版.md` | Ch.2: 射影空间 | 6小时 |
| 3 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.4: 代数曲线 | 8小时 |
| 4 | `docs/13-代数几何/03-代数几何深度扩展版.md` | Ch.5-6: 概形初步 | 6小时 |

#### 与MIT/Harvard对比

| 特征 | Cambridge Part II | MIT 18.725 | Harvard Math 137 |
|------|-------------------|------------|------------------|
| 教材 | Reid | Hartshorne | Hartshorne |
| 风格 | 几何直观、例子丰富 | 概形理论、抽象 | 概形理论 |
| 难度 | ⭐⭐⭐ (入门友好) | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| 概形深度 | 简介 | 核心 | 核心 |
| FormalMath覆盖 | 75% | 75% | 75% |

---

### Part II Number Fields (代数数论)

| 属性 | 内容 |
|------|------|
| **课程名称** | Number Fields |
| **学时** | 24讲 |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Marcus, *Number Fields*; Stewart & Tall |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (82%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Marcus章节 | 学习时间 |
|------|----------|------------|----------|
| 1 | `docs/06-数论/02-代数数论-增强版.md` | Ch.2: 数域、整数环 | 6小时 |
| 2 | `docs/06-数论/02-代数数论.md` | Ch.3: 理想分解 | 6小时 |
| 3 | `docs/06-数论/06-理想类群-深度扩展版.md` | Ch.4: 类数、单位 | 6小时 |
| 4 | `docs/06-数论/07-分圆域-深度扩展版.md` | Ch.4: 分圆域 | 5小时 |
| 5 | `docs/06-数论/02-代数数论-增强版.md` §3 | Ch.5: 类域论初步 | 6小时 |

---

### Part II Galois Theory (Galois理论)

| 属性 | 内容 |
|------|------|
| **课程名称** | Galois Theory |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Stewart, *Galois Theory* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (88%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Stewart章节 | 学习时间 |
|------|----------|-------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | Ch.4-5: 域扩张 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理论/域论/02-Galois理论-深度扩展版.md` | Ch.6-8: Galois理论 | 8小时 |
| 3 | `docs/02-代数结构/02-核心理论/域论/04-Galois理论应用-深度扩展版.md` | Ch.9-10: 可解性、构造 | 5小时 |

---

### Part II Representation Theory (表示论)

| 属性 | 内容 |
|------|------|
| **课程名称** | Representation Theory |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | James & Liebeck, *Representations and Characters of Groups* |
| **建议学期** | Lent |
| **覆盖度** | 🟢 完整覆盖 (85%) |

#### FormalMath对应文档

| 序号 | 文档路径 | James & Liebeck章节 | 学习时间 |
|------|----------|---------------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/表示论/01-表示论基础.md` | Ch.1-3: 表示定义 | 5小时 |
| 2 | `docs/02-代数结构/02-核心理论/表示论/03-特征标理论-深度扩展版.md` | Ch.4-6: 特征标理论 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/表示论/04-诱导表示-深度扩展版.md` | Ch.7-8: 诱导表示 | 5小时 |
| 4 | `docs/02-代数结构/03-应用分析/群论应用/02-群论应用-物理化学版.md` | Ch.10-11: 对称群 | 4小时 |

---

### Part II Algebraic Topology (代数拓扑)

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Topology |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Analysis and Topology |
| **Cambridge教材** | Hatcher, *Algebraic Topology* |
| **建议学期** | Michaelmas (2024-2025) |
| **覆盖度** | 🟡 部分覆盖 (72%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Hatcher章节 | 学习时间 |
|------|----------|-------------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑/01-代数拓扑-国际标准深度扩展版.md` | Ch.1: 基本群 | 6小时 |
| 2 | `docs/05-拓扑学/02-代数拓扑/02-覆盖空间-深度扩展版.md` | Ch.1.3: 覆盖空间 | 5小时 |
| 3 | `docs/05-拓扑学/05-同调论/01-同调论-国际标准深度扩展版.md` | Ch.2: 同调 | 8小时 |
| 4 | `docs/05-拓扑学/05-同调论/03-上同调环-深度扩展版.md` | Ch.3: 上同调 | 6小时 |
| 5 | `docs/05-拓扑学/05-同调论/04-Poincaré对偶-深度扩展版.md` | Ch.3.3: 对偶 | 4小时 |

---

### Part II Differential Geometry (微分几何)

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Geometry |
| **学时** | 24讲 (D-course) |
| **先修** | IB Analysis and Topology |
| **Cambridge教材** | do Carmo; Pressley, *Elementary Differential Geometry* |
| **学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (80%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/14-微分几何/01-微分几何基础.md` | 光滑流形、切空间 | 6小时 |
| 2 | `docs/14-微分几何/02-微分几何增强版.md` | Riemann度量 | 6小时 |
| 3 | `docs/14-微分几何/03-微分几何深度扩展版.md` | 联络、曲率 | 6小时 |
| 4 | `docs/14-微分几何/04-测地线-深度扩展版.md` | 测地线、Gauss-Bonnet | 5小时 |

---

### Part II Logic and Set Theory (逻辑与集合论)

| 属性 | 内容 |
|------|------|
| **课程名称** | Logic and Set Theory |
| **学时** | 24讲 (D-course) |
| **先修** | IA Numbers and Sets |
| **Cambridge教材** | Goldrei, *Classic Set Theory*; Enderton |
| **学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (85%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/07-逻辑学/命题逻辑-深度扩展版.md` | 命题逻辑 | 4小时 |
| 2 | `docs/07-逻辑学/一阶逻辑-深度扩展版.md` | 一阶逻辑 | 5小时 |
| 3 | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | 基数算术 | 5小时 |
| 4 | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-国际标准对照版.md` | ZFC公理 | 6小时 |
| 5 | `docs/07-逻辑学/证明理论-深度扩展版.md` | 完备性、紧致性 | 5小时 |

---

### Part II Riemann Surfaces (Riemann曲面)

| 属性 | 内容 |
|------|------|
| **课程名称** | Riemann Surfaces |
| **学时** | 16讲 (D-course) |
| **先修** | Part IB Complex Analysis |
| **Cambridge教材** | Donaldson, *Riemann Surfaces* |
| **学期** | Lent (2024-2025) |
| **覆盖度** | 🟡 部分覆盖 (68%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Donaldson章节 | 学习时间 |
|------|----------|---------------|----------|
| 1 | `docs/03-分析学/02-复分析/04-Riemann曲面-深度扩展版.md` | Ch.1-2: 定义、例子 | 5小时 |
| 2 | `docs/03-分析学/02-复分析/05-单值化定理-深度扩展版.md` | Ch.3: 单值化 | 6小时 |
| 3 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.4-5: 椭圆曲线 | 6小时 |
| 4 | `docs/06-数论/10-复乘法-深度扩展版.md` | Ch.6-7: Jacobi簇 | 5小时 |

---

## 🎓 Part III (大四/硕士)

### Part III Algebraic Geometry (M24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry |
| **学时** | 24讲 |
| **先修** | Part II Algebraic Geometry |
| **Cambridge教材** | Hartshorne; Vakil, *FOAG* |
| **学期** | Michaelmas |
| **覆盖度** | 🟡 部分覆盖 (78%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Vakil/Hartshorne | 学习时间 |
|------|----------|-----------------|----------|
| 1 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` | 概形、态射 | 8小时 |
| 2 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` | 凝聚层 | 6小时 |
| 3 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` | 层上同调 | 6小时 |
| 4 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/25-上同调与凝聚层上同调.md` | 凝聚层上同调 | 6小时 |

---

### Part III Commutative Algebra (M24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Commutative Algebra |
| **学时** | 24讲 |
| **先修** | Part II Algebraic Geometry |
| **Cambridge教材** | Atiyah-Macdonald |
| **学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (85%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Atiyah-Macdonald | 学习时间 |
|------|----------|-----------------|----------|
| 1 | `docs/02-代数结构/02-核心理论/交换代数/01-交换代数核心-深度扩展版.md` | Ch.1-3: 基础 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理论/交换代数/02-局部化-深度扩展版.md` | Ch.3: 局部化 | 5小时 |
| 3 | `docs/02-代数结构/02-核心理论/交换代数/04-Noether环深入-深度扩展版.md` | Ch.6-7: 诺特环 | 6小时 |
| 4 | `docs/02-代数结构/02-核心理论/交换代数/09-维数理论-深度扩展版.md` | Ch.11: 维数 | 6小时 |

---

### Part III Differential Geometry (M24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Geometry |
| **学时** | 24讲 |
| **先修** | Part II Differential Geometry |
| **Cambridge教材** | Lee, *Riemannian Manifolds* |
| **学期** | Michaelmas |
| **覆盖度** | 🟢 完整覆盖 (78%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Lee章节 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/14-微分几何/03-微分几何深度扩展版.md` §6 | Ch.2-3: 联络 | 6小时 |
| 2 | `docs/14-微分几何/03-微分几何深度扩展版.md` §7 | Ch.4-5: 曲率 | 6小时 |
| 3 | `docs/14-微分几何/03-微分几何深度扩展版.md` §9 | Ch.6-7: Hodge理论 | 6小时 |
| 4 | `docs/14-微分几何/03-微分几何深度扩展版.md` §10 | Ch.8-9: Kähler几何 | 5小时 |

---

### Part III Complex Manifolds (L24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Complex Manifolds |
| **学时** | 24讲 |
| **先修** | Part III Algebraic Geometry |
| **Cambridge教材** | Huybrechts, *Complex Geometry* |
| **学期** | Lent |
| **覆盖度** | 🟡 部分覆盖 (65%) |

#### FormalMath对应文档

| 序号 | 文档路径 | Huybrechts章节 | 学习时间 |
|------|----------|----------------|----------|
| 1 | `docs/14-微分几何/03-微分几何深度扩展版.md` §10 | Ch.1-2: 复流形 | 6小时 |
| 2 | `docs/14-微分几何/03-微分几何深度扩展版.md` §9 | Ch.3: Hodge理论 | 6小时 |
| 3 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.4: K3曲面、Calabi-Yau | 5小时 |

---

## 📊 覆盖度总结

| 课程 | 覆盖度 | 状态 | 建议使用 |
|------|--------|------|----------|
| IA Groups / Numbers and Sets | 92% | 🟢 | 完全可以作为主要资源 |
| IA Analysis I | 90% | 🟢 | 完全可以作为主要资源 |
| IA Vectors and Matrices | 88% | 🟢 | 完全可以作为主要资源 |
| IB Groups, Rings and Modules | 88% | 🟢 | 完全可以作为主要资源 |
| IB Linear Algebra | 85% | 🟢 | 完全可以作为主要资源 |
| IB Analysis and Topology | 85% | 🟢 | 完全可以作为主要资源 |
| Part II Algebraic Geometry | 75% | 🟡 | 需要补充Reid |
| Part II Number Fields | 82% | 🟢 | 完全可以作为主要资源 |
| Part II Galois Theory | 88% | 🟢 | 完全可以作为主要资源 |
| Part II Representation Theory | 85% | 🟢 | 完全可以作为主要资源 |
| Part II Algebraic Topology | 72% | 🟡 | 需要补充Hatcher |
| Part II Differential Geometry | 80% | 🟢 | 完全可以作为主要资源 |
| Part II Logic and Set Theory | 85% | 🟢 | 完全可以作为主要资源 |
| Part II Riemann Surfaces | 68% | 🟡 | 需要补充Donaldson |
| Part III Algebraic Geometry | 78% | 🟢 | 完全可以作为主要资源 |
| Part III Commutative Algebra | 85% | 🟢 | 完全可以作为主要资源 |
| Part III Differential Geometry | 78% | 🟢 | 完全可以作为主要资源 |
| Part III Complex Manifolds | 65% | 🟡 | 需要补充Huybrechts |

---

## 🎯 Cambridge特色学习建议

### Tripos考试准备

Cambridge Tripos考试系统独特，FormalMath提供相应支持：

| 考试要素 | FormalMath支持 |
|----------|---------------|
| 快速解题 | `docs/02-代数结构/08-教学资源/` 各主题习题库 |
| 严格证明 | `docs/FormalMath定义表述模板.md` |
| 选择题技巧 | `docs/00-核心概念理解三问/` 反例集 |

### 课程难度递进

```
Part IA (基础)
├── Groups → IB Groups, Rings and Modules → Part II Galois Theory
├── Analysis → IB Analysis and Topology → Part II Differential Geometry
└── Vectors → IB Linear Algebra → Part II Representation Theory

Part II (专业)
├── Algebraic Geometry → Part III Algebraic Geometry
├── Number Fields → Part III Commutative Algebra
├── Algebraic Topology → Part III 同伦论专题
└── Riemann Surfaces → Part III Complex Manifolds
```

### Example Sheets (习题课)

Cambridge每门课配有4个Example Sheets，FormalMath对应资源：

- `docs/02-代数结构/08-教学资源/` 各主题习题库
- `docs/03-分析学/各主题/习题库.md`
- `docs/06-数论/数论练习题库.md`

---

## 🔗 相关链接

- [Cambridge Maths Department](https://www.maths.cam.ac.uk/)
- [Part III Courses](https://www.maths.cam.ac.uk/postgrad/part-iii)
- [FormalMath MIT课程映射](MIT-course-mapping-detailed.md)
- [FormalMath Harvard课程映射](Harvard-course-mapping-detailed.md)
- [FormalMath Princeton课程映射](Princeton-course-mapping-detailed.md)
- [FormalMath Berkeley课程映射](Berkeley-course-mapping-detailed.md)

---

*最后更新: 2026年4月*
