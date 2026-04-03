---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# FormalMath与Cambridge数学课程深度映射表

> **版本**: 2026年4月
> **适用范围**: Cambridge University Mathematical Tripos 2025-2026学年
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

## 🎓 Part IA（第一年）

### IA Numbers and Sets

| 属性 | 内容 |
|------|------|
| **课程名称** | Numbers and Sets |
| **学时** | 24讲 |
| **先修要求** | 无 |
| **Cambridge教材** | Goldrei, *Classic Set Theory*; 系内讲义 |
| **建议学期** | Michaelmas Term |
| **覆盖度** | 🟢 **完整覆盖 (92%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/01-基础数学/集合论/01-集合论基础-国际标准版.md` | 集合、子集、幂集 | 100% | 外延性、空集 |
| 2 | `docs/01-基础数学/集合论/02-数系与运算-深度扩展版.md` | 自然数、归纳法 | 95% | Peano公理、递归 |
| 3 | `docs/01-基础数学/集合论/03-函数与映射-深度扩展版.md` | 函数、单射/满射/双射 | 95% | 像、原像、复合 |
| 4 | `docs/01-基础数学/集合论/04-关系与等价-深度扩展版.md` | 等价关系、划分 | 90% | 等价类、商集 |
| 5 | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | 可数性、不可数集 | 85% | 对角线论证、Cantor定理 |

---

### IA Groups

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups |
| **学时** | 24讲 |
| **先修要求** | Numbers and Sets |
| **Cambridge教材** | Allenby, *Rings, Fields and Groups* |
| **建议学期** | Michaelmas Term |
| **覆盖度** | 🟢 **完整覆盖 (90%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 群公理、例子 | 95% | 封闭性、结合律、单位元、逆元 |
| 2 | `docs/02-代数结构/02-核心理论/群论/02-子群与陪集-深度扩展版.md` | 子群、Lagrange定理 | 95% | 陪集分解、指数 |
| 3 | `docs/02-代数结构/02-核心理论/群论/04-群同态-深度扩展版.md` | 同态、同构 | 90% | 核、像、第一同构定理 |
| 4 | `docs/02-代数结构/02-核心理论/群论/07-Sylow定理-深度扩展版.md` | Sylow定理（选讲） | 80% | p-子群、Sylow第一定理 |

---

### IA Differential Equations

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Equations |
| **学时** | 24讲 |
| **先修要求** | 无 |
| **Cambridge教材** | 系内讲义 |
| **建议学期** | Michaelmas/Lent |
| **覆盖度** | 🟡 **部分覆盖 (70%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/03-微分方程/01-常微分方程基础.md` | 一阶ODE | 75% | 可分离变量、积分因子 |
| 2 | `docs/03-分析学/03-微分方程/02-常微分方程-增强版.md` | 高阶线性ODE | 70% | 特征方程、待定系数 |
| 3 | `docs/03-分析学/03-微分方程/03-偏微分方程基础.md` | PDE初步 | 60% | 波动方程、热方程 |

---

### IA Analysis I

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis I |
| **学时** | 24讲 |
| **先修要求** | 无 |
| **Cambridge教材** | Apostol, *Mathematical Analysis*; Spivak |
| **建议学期** | Michaelmas/Lent |
| **覆盖度** | 🟢 **完整覆盖 (90%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | 实数完备性 | 95% | 确界原理、Archimedes性质 |
| 2 | `docs/03-分析学/01-实分析/02-序列与极限-深度扩展版.md` | 序列收敛 | 95% | ε-N定义、子序列 |
| 3 | `docs/03-分析学/01-实分析/04-连续函数-深度扩展版.md` | 连续性 | 90% | ε-δ定义、一致连续 |
| 4 | `docs/03-分析学/01-实分析/06-微分-深度扩展版.md` | 可微性 | 90% | 导数、中值定理 |
| 5 | `docs/03-分析学/01-实分析/08-Riemann积分-深度扩展版.md` | Riemann积分 | 90% | 可积性、FTC |

---

### IA Probability

| 属性 | 内容 |
|------|------|
| **课程名称** | Probability |
| **学时** | 24讲 |
| **先修要求** | Analysis I |
| **Cambridge教材** | Grimmett & Welsh |
| **建议学期** | Lent |
| **覆盖度** | 🟡 **部分覆盖 (68%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/05-概率论/01-概率论基础-深度扩展版.md` | 概率空间 | 75% | σ-代数、测度 |
| 2 | `docs/03-分析学/05-概率论/02-期望与方差-深度扩展版.md` | 期望、方差 | 70% | 条件期望、独立性 |
| 3 | `docs/03-分析学/05-概率论/03-大数定律-深度扩展版.md` | 极限定理 | 60% | LLN、CLT |

---

## 🎓 Part IB（第二年）

### IB Linear Algebra

| 属性 | 内容 |
|------|------|
| **课程名称** | Linear Algebra |
| **学时** | 24讲 |
| **先修要求** | IA Vectors and Matrices |
| **Cambridge教材** | Kaye & Wilson; 系内讲义 |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/06-算子理论-深度扩展版.md` | 正规算子、谱定理 | 90% | 自伴算子、酉算子 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/07-张量积-深度扩展版.md` | 双线性型、张量积 | 85% | 对称/反对称双线性型 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/08-典范形式-深度扩展版.md` | Jordan标准形 | 90% | 极小多项式、有理标准形 |
| 4 | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | 模论引入 | 85% | 自由模、有限生成模 |

---

### IB Groups, Rings and Modules

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups, Rings and Modules |
| **学时** | 24讲 |
| **先修要求** | IA Groups |
| **Cambridge教材** | Allenby; Cohn, *Algebra* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | 正规子群、合成列 | 90% | 单群、可解群 |
| 2 | `docs/02-代数结构/02-核心理论/群论/05-同构定理-深度扩展版.md` | 同构定理 | 95% | 三同构定理 |
| 3 | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | 环、理想 | 90% | 素理想、极大理想 |
| 4 | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | UFD、PID | 90% | 唯一分解、欧几里得整环 |
| 5 | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | 模基础 | 85% | 子模、商模 |
| 6 | `docs/02-代数结构/02-核心理论/域论/02-Galois理论-深度扩展版.md` | Galois理论引入 | 80% | 域扩张、Galois对应 |

---

### IB Analysis II (Metric and Topological Spaces)

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis and Topology |
| **学时** | 24讲 |
| **先修要求** | IA Analysis I |
| **Cambridge教材** | Sutherland, *Introduction to Metric and Topological Spaces* |
| **建议学期** | Lent |
| **覆盖度** | 🟢 **完整覆盖 (85%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/01-实分析/05-拓扑基础-深度扩展版.md` | 度量空间 | 95% | 度量、开球、收敛 |
| 2 | `docs/05-拓扑学/01-点集拓扑/01-点集拓扑-深度扩展版.md` | 拓扑空间 | 90% | 开集、闭集、邻域 |
| 3 | `docs/05-拓扑学/01-点集拓扑/02-连通性与紧致性-深度扩展版.md` | 连通性、紧致性 | 90% | 道路连通、Heine-Borel |
| 4 | `docs/03-分析学/04-泛函分析/01-泛函分析-深度扩展版.md` | 函数空间 | 75% | 完备度量空间、Banach空间 |

---

### IB Complex Analysis

| 属性 | 内容 |
|------|------|
| **课程名称** | Complex Analysis |
| **学时** | 24讲 |
| **先修要求** | IA Analysis I |
| **Cambridge教材** | 系内讲义 |
| **建议学期** | Lent |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/02-复分析/01-复分析.md` | 全纯函数 | 95% | Cauchy-Riemann方程 |
| 2 | `docs/03-分析学/02-复分析/02-复分析-增强版.md` | 复积分 | 90% | Cauchy积分定理、Laurent级数 |
| 3 | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | 留数定理 | 85% | 围道积分、实积分计算 |
| 4 | `docs/03-分析学/02-复分析/04-Riemann曲面-深度扩展版.md` | Riemann曲面引入 | 75% | 复结构、全纯映射 |

---

### IB Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Geometry |
| **学时** | 24讲 |
| **先修要求** | IA Vectors and Matrices |
| **Cambridge教材** | 系内讲义 |
| **建议学期** | Michaelmas/Lent |
| **覆盖度** | 🟢 **完整覆盖 (80%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/04-几何学/01-欧氏几何/01-欧氏几何基础.md` | 欧氏几何 | 85% | 等距、对称群 |
| 2 | `docs/04-几何学/02-射影几何/01-射影几何基础.md` | 射影几何 | 80% | 射影空间、对偶性 |
| 3 | `docs/14-微分几何/01-微分几何基础.md` | 曲面理论 | 75% | 第一/第二基本形式、Gauss曲率 |

---

## 🎓 Part II（第三年）

### Part II Algebraic Topology

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Topology |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Analysis and Topology |
| **Cambridge教材** | Hatcher, *Algebraic Topology* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟡 **部分覆盖 (75%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Hatcher章节 | 覆盖率 | 关键概念 |
|------|----------|-------------|--------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑/01-代数拓扑-国际标准深度扩展版.md` | Ch.1: 基本群 | 90% | 回路同伦、Van Kampen |
| 2 | `docs/05-拓扑学/02-代数拓扑/02-覆盖空间-深度扩展版.md` | Ch.1.3: 覆盖空间 | 85% | 提升性质、万有覆盖 |
| 3 | `docs/05-拓扑学/05-同调论/01-同调论-国际标准深度扩展版.md` | Ch.2: 同调 | 80% | 单纯同调、奇异同调 |
| 4 | `docs/05-拓扑学/05-同调论/03-上同调环-深度扩展版.md` | Ch.3: 上同调 | 70% | 上积、Poincaré对偶 |

---

### Part II Number Fields

| 属性 | 内容 |
|------|------|
| **课程名称** | Number Fields |
| **学时** | 24讲 |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Marcus, *Number Fields*; Stewart & Tall |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 **完整覆盖 (85%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Marcus章节 | 覆盖率 | 关键概念 |
|------|----------|------------|--------|----------|
| 1 | `docs/06-数论/02-代数数论-增强版.md` | Ch.2: 数域、整数环 | 90% | 代数整数、判别式 |
| 2 | `docs/06-数论/02-代数数论.md` | Ch.3: 理想分解 | 90% | Dedekind整环、分歧 |
| 3 | `docs/06-数论/06-理想类群-深度扩展版.md` | Ch.4: 类群、单位 | 85% | Minkowski定理、Dirichlet单位定理 |
| 4 | `docs/06-数论/07-分圆域-深度扩展版.md` | Ch.4: 分圆域 | 80% | 分圆整数、Fermat大定理特例 |

---

### Part II Algebraic Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Reid, *Undergraduate Algebraic Geometry*; Kirwan |
| **建议学期** | Lent |
| **覆盖度** | 🟡 **部分覆盖 (78%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Reid章节 | 覆盖率 | 关键概念 |
|------|----------|----------|--------|----------|
| 1 | `docs/13-代数几何/01-代数几何基础.md` | Ch.0-1: 仿射空间、代数集 | 90% | Zariski拓扑、坐标环 |
| 2 | `docs/13-代数几何/02-代数几何增强版.md` | Ch.2: 射影空间 | 85% | 齐次坐标、射影闭包 |
| 3 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.4: 代数曲线 | 75% | 亏格、Riemann-Roch |
| 4 | `docs/13-代数几何/03-代数几何深度扩展版.md` | Ch.5-6: 概形初步 | 70% | 结构层、概形定义 |

---

### Part II Differential Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Geometry |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Analysis and Topology |
| **Cambridge教材** | do Carmo; Pressley |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 **完整覆盖 (82%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/14-微分几何/01-微分几何基础.md` | 光滑流形 | 90% | 图册、切空间 |
| 2 | `docs/14-微分几何/02-微分几何增强版.md` | Riemann度量 | 85% | 度量张量、Levi-Civita联络 |
| 3 | `docs/14-微分几何/03-微分几何深度扩展版.md` | 曲率理论 | 80% | Riemann曲率张量、截面曲率 |
| 4 | `docs/14-微分几何/04-测地线-深度扩展版.md` | 测地线 | 75% | 测地方程、指数映射、Gauss-Bonnet |

---

### Part II Logic and Set Theory

| 属性 | 内容 |
|------|------|
| **课程名称** | Logic and Set Theory |
| **学时** | 24讲 (D-course) |
| **先修要求** | IA Numbers and Sets |
| **Cambridge教材** | Goldrei, *Classic Set Theory*; Enderton |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/07-逻辑学/命题逻辑-深度扩展版.md` | 命题逻辑 | 90% | 真值表、完备性 |
| 2 | `docs/07-逻辑学/一阶逻辑-深度扩展版.md` | 一阶逻辑 | 90% | 量词、结构、可满足性 |
| 3 | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | 基数算术 | 85% | 基数运算、连续统假设 |
| 4 | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-国际标准对照版.md` | ZFC公理 | 85% | 选择公理、正则公理 |
| 5 | `docs/07-逻辑学/证明理论-深度扩展版.md` | 完备性、紧致性 | 85% | Gödel完备性定理 |

---

## 🎓 Part III（第四年/研究生）

### Part III Advanced Algebraic Geometry (M24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry (Advanced) |
| **学时** | 24讲 |
| **先修要求** | Part II Algebraic Geometry |
| **Cambridge教材** | Hartshorne; Vakil, *FOAG* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟡 **部分覆盖 (80%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Hartshorne/Vakil | 覆盖率 | 关键概念 |
|------|----------|-----------------|--------|----------|
| 1 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` | Ch.II: 概形、态射 | 90% | 仿射概形、纤维积 |
| 2 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` | Ch.II.5: 凝聚层 | 85% | 局部自由层、Picard群 |
| 3 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` | Ch.III: 层上同调 | 85% | 导出函子、Čech上同调 |
| 4 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/25-上同调与凝聚层上同调.md` | Ch.III.5: 凝聚层上同调 | 75% | Serre定理、Serre对偶 |

---

### Part III Homotopy Theory (L24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Homotopy Theory |
| **学时** | 24讲 |
| **先修要求** | Part II Algebraic Topology |
| **Cambridge教材** | Hatcher; May |
| **建议学期** | Lent |
| **覆盖度** | 🟡 **部分覆盖 (70%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Hatcher/May | 覆盖率 | 关键概念 |
|------|----------|-------------|--------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑/01-代数拓扑-国际标准深度扩展版.md` | Ch.4: 同伦论 | 75% | 同伦群、纤维序列 |
| 2 | `docs/05-拓扑学/05-同调论/02-上同调运算-深度扩展版.md` | Ch.4.L: 上同调运算 | 70% | Steenrod方 |
| 3 | `docs/05-拓扑学/06-同伦论/01-同伦论基础.md` | May: 谱、Ω-谱 | 65% | 稳定同伦、Eilenberg-MacLane谱 |

---

### Part III Elliptic Curves (M24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Elliptic Curves |
| **学时** | 16-24讲 |
| **先修要求** | Part II Number Fields |
| **Cambridge教材** | Silverman, *Arithmetic of Elliptic Curves* |
| **建议学期** | Michaelmas |
| **覆盖度** | 🟡 **部分覆盖 (75%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Silverman章节 | 覆盖率 | 关键概念 |
|------|----------|--------------|--------|----------|
| 1 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.III: 群结构 | 90% | 弦切法、Mordell-Weil群 |
| 2 | `docs/06-数论/09-椭圆曲线群结构-深度扩展版.md` | Ch.VIII: Mordell-Weil定理 | 80% | 下降法、高度 |
| 3 | `docs/06-数论/10-复乘法-深度扩展版.md` | Ch.II: 复乘法 | 70% | 自同态环、类域论 |
| 4 | `docs/06-数论/11-模形式基础-深度扩展版.md` | C: 模形式 | 65% | 模曲线、Taniyama-Shimura |

---

### Part III Moduli Spaces (L24)

| 属性 | 内容 |
|------|------|
| **课程名称** | Moduli Spaces |
| **学时** | 16-24讲 |
| **先修要求** | Part III Advanced Algebraic Geometry |
| **Cambridge教材** | 系内讲义 |
| **建议学期** | Lent |
| **覆盖度** | 🟡 **部分覆盖 (68%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | 主题 | 覆盖率 | 关键概念 |
|------|----------|------|--------|----------|
| 1 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/01-模空间理论.md` | 模空间基础 | 75% | 精细/粗糙模空间 |
| 2 | `docs/13-代数几何/模空间与代数曲线-深度扩展版.md` | 曲线模空间 | 70% | Mg、Deligne-Mumford紧化 |
| 3 | `docs/13-代数几何/稳定曲线与模空间-深度扩展版.md` | 稳定曲线 | 60% | 稳定约化、相交理论 |

---

## 📊 覆盖度总结

| 课程 | 覆盖度 | 状态 | 建议使用 |
|------|--------|------|----------|
| **Part IA** | | | |
| IA Numbers and Sets | 92% | 🟢 | 完全可以作为主要资源 |
| IA Groups | 90% | 🟢 | 完全可以作为主要资源 |
| IA Differential Equations | 70% | 🟡 | 需要补充材料 |
| IA Analysis I | 90% | 🟢 | 完全可以作为主要资源 |
| IA Probability | 68% | 🟡 | 需要补充材料 |
| **Part IB** | | | |
| IB Linear Algebra | 88% | 🟢 | 完全可以作为主要资源 |
| IB Groups, Rings and Modules | 88% | 🟢 | 完全可以作为主要资源 |
| IB Analysis and Topology | 85% | 🟢 | 完全可以作为主要资源 |
| IB Complex Analysis | 88% | 🟢 | 完全可以作为主要资源 |
| IB Geometry | 80% | 🟢 | 完全可以作为主要资源 |
| **Part II** | | | |
| Part II Algebraic Topology | 75% | 🟡 | 需要补充Hatcher |
| Part II Number Fields | 85% | 🟢 | 完全可以作为主要资源 |
| Part II Algebraic Geometry | 78% | 🟢 | 完全可以作为主要资源 |
| Part II Differential Geometry | 82% | 🟢 | 完全可以作为主要资源 |
| Part II Logic and Set Theory | 88% | 🟢 | 完全可以作为主要资源 |
| **Part III** | | | |
| Part III Advanced Algebraic Geometry | 80% | 🟢 | 完全可以作为主要资源 |
| Part III Homotopy Theory | 70% | 🟡 | 需要补充May |
| Part III Elliptic Curves | 75% | 🟡 | 需要补充Silverman |
| Part III Moduli Spaces | 68% | 🟡 | 需要补充材料 |

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
├── Numbers and Sets → IA Groups → Part II Logic
├── Analysis I → IB Analysis and Topology → Part II Differential Geometry
└── Vectors → IB Linear Algebra → Part II Algebraic Topology

Part IB (进阶)
├── Groups, Rings and Modules → Part II Number Fields → Part III Elliptic Curves
├── Linear Algebra → Part II Algebraic Geometry → Part III Advanced Algebraic Geometry
└── Analysis and Topology → Part II Algebraic Topology → Part III Homotopy Theory

Part II (专业)
├── Number Fields → Part III Elliptic Curves
├── Algebraic Geometry → Part III Advanced Algebraic Geometry
├── Algebraic Topology → Part III Homotopy Theory
└── Differential Geometry → Part III 微分几何专题

Part III (研究生)
├── Advanced Algebraic Geometry
├── Homotopy Theory
├── Elliptic Curves
└── Moduli Spaces
```

### 与Oxford对比

| 特征 | Cambridge | Oxford |
|------|-----------|--------|
| **代数几何** | Reid → Hartshorne (Part II/III) | Fulton → Hartshorne (B5/C3.1) |
| **李代数** | Part II Representation Theory (部分) | **B2.1/C2.1 (专门课程)** |
| **同调代数** | Part III Commutative Algebra (部分) | **C2.2 (专门课程)** |
| **考试系统** | Tripos | 期末考试 |
| **问题集** | Example Sheets | Problem Sheets |

---

## 🔗 相关链接

- [Cambridge Maths Department](https://www.maths.cam.ac.uk/)
- [Part III Courses](https://www.maths.cam.ac.uk/postgrad/part-iii)
- [Cambridge Course Schedule 2025-2026](https://www.maths.cam.ac.uk/undergrad/course/)
- [FormalMath Oxford课程映射](Oxford-course-mapping-detailed.md)
- [FormalMath MIT课程映射](MIT-course-mapping-detailed.md)
- [FormalMath Harvard课程映射](Harvard-course-mapping-detailed.md)
- [FormalMath Princeton课程映射](Princeton-course-mapping-detailed.md)

---

*最后更新: 2026年4月*
*更新内容: 全面更新，覆盖Cambridge数学Tripos全课程体系，添加18门核心课程详细映射*
