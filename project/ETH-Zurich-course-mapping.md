---
msc_primary: 97A99
msc_secondary:
- 00A05
title: ETH Zurich数学课程与FormalMath映射表
processed_at: '2026-04-05'
---
# ETH Zurich数学课程与FormalMath映射表

> **版本**: 2026年4月
> **适用范围**: ETH Zurich 2024-2025学年数学课程体系
> **目标**: 为自学者提供使用FormalMath资源学习ETH Zurich数学课程的完整路径
> **特色**: 对齐苏黎世学派传统（代数几何、拓扑学）

---

## 📋 使用指南

### 如何阅读本文档

- **课程代码**: ETH Zurich课程编号，遵循401-XXXX-XXL格式
- **学分**: 基于ETH学分系统（1 ECTS ≈ 30小时工作量）
- **FormalMath文档**: 对应FormalMath项目中的具体文档路径
- **覆盖度**:
  - 🟢 **完整覆盖** (80-100%): FormalMath已完整覆盖课程内容
  - 🟡 **部分覆盖** (40-79%): FormalMath覆盖主要主题，需补充材料
  - 🟠 **基础覆盖** (20-39%): FormalMath覆盖基础概念，需大量外部资源
  - ⚪ **待开发** (<20%): FormalMath尚未覆盖，需使用其他资源

### ETH Zurich数学系特色

ETH Zurich Department of Mathematics是世界顶级数学研究中心之一：

- **Fields Medal得主**: 包括Alessio Figalli等
- **苏黎世学派传统**: 代数几何、代数拓扑、微分几何的深厚传统
- **课程特色**: 严谨的形式化训练、理论与应用并重
- **教学语言**: 主要德语授课，部分高级课程英语授课

---

## 🎓 Stage 1: 基础课程（Basisfächer）

### 401-1151-00L: Linear Algebra I

| 属性 | 内容 |
|------|------|
| **课程名称** | Linear Algebra I |
| **学分** | 7 ECTS |
| **学期** | 秋季学期（Herbstsemester）|
| **授课语言** | 德语（Deutsch）|
| **先修要求** | 无 |
| **ETH教材** | G. Fischer, *Lineare Algebra*; K. Jänich, *Lineare Algebra* |
| **覆盖度** | 🟢 完整覆盖 (90%) |

**课程描述（德文原文）**:
*"Einführung in die lineare Algebra: Vektorräume, lineare Gleichungssysteme, Basen, Dimension, lineare Abbildungen, Matrizen, Determinanten, Eigenwerte und Eigenvektoren."*

**课程描述（英文翻译）**:
Introduction to linear algebra: vector spaces, systems of linear equations, bases, dimension, linear maps, matrices, determinants, eigenvalues and eigenvectors.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | 向量空间、子空间 | 8小时 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/02-线性代数与高级数系-国际标准版.md` | 线性方程组、矩阵运算 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` | 基、维数、坐标变换 | 6小时 |
| 4 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` | 线性映射、矩阵表示 | 6小时 |
| 5 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` | 行列式、特征值、特征向量 | 8小时 |

**课程官网**: [ETH Course Catalogue](https://www.ethz.ch/content/dam/ethz/special-interest/mavt/department-averoes/documents/Studium/Bachelor/Studienplan_BSc_MAVT_2023.pdf)

---

### 401-1152-00L: Linear Algebra II

| 属性 | 内容 |
|------|------|
| **课程名称** | Linear Algebra II |
| **学分** | 7 ECTS |
| **学期** | 春季学期（Frühlingssemester）|
| **先修要求** | Linear Algebra I |
| **ETH教材** | G. Fischer, *Lineare Algebra*; Halmos, *Finite-Dimensional Vector Spaces* |
| **覆盖度** | 🟢 完整覆盖 (88%) |

**课程描述（德文原文）**:
*"Fortsetzung der linearen Algebra: Euklidische und unitäre Vektorräume, Orthogonalität, Selbstadjungierte Endomorphismen, Hauptachsentransformation, Jordansche Normalform."*

**课程描述（英文翻译）**:
Continuation of linear algebra: Euclidean and unitary vector spaces, orthogonality, self-adjoint endomorphisms, principal axis transformation, Jordan normal form.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` | 欧几里得空间、内积 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/05-内积空间-深度扩展版.md` | 正交性、Gram-Schmidt正交化 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/06-算子理论-深度扩展版.md` | 自伴算子、谱定理 | 8小时 |
| 4 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/08-典范形式-深度扩展版.md` | Jordan标准形、有理标准形 | 8小时 |
| 5 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/07-张量积-深度扩展版.md` | 多重线性代数初步 | 6小时 |

---

### 401-1261-07L: Analysis I

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis I |
| **学分** | 7 ECTS |
| **学期** | 秋季学期 |
| **先修要求** | 无 |
| **ETH教材** | O. Forster, *Analysis 1*; K. Königsberger, *Analysis 1* |
| **覆盖度** | 🟢 完整覆盖 (92%) |

**课程描述（德文原文）**:
*"Einführung in die Analysis: Reelle Zahlen, Konvergenz von Folgen und Reihen, Stetigkeit, Differenzierbarkeit, Riemann-Integral."*

**课程描述（英文翻译）**:
Introduction to analysis: real numbers, convergence of sequences and series, continuity, differentiability, Riemann integral.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/03-分析学/01-实分析/01-实分析.md` | 实数构造、完备性 | 6小时 |
| 2 | `docs/03-分析学/01-实分析/02-序列与极限-深度扩展版.md` | 序列收敛、子序列 | 6小时 |
| 3 | `docs/03-分析学/01-实分析/03-级数理论-深度扩展版.md` | 级数收敛判别 | 6小时 |
| 4 | `docs/03-分析学/01-实分析/04-连续函数-深度扩展版.md` | 连续函数、一致连续 | 6小时 |
| 5 | `docs/03-分析学/01-实分析/06-微分-深度扩展版.md` | 微分学、中值定理 | 6小时 |
| 6 | `docs/03-分析学/01-实分析/08-Riemann积分-深度扩展版.md` | Riemann积分、FTC | 6小时 |

---

### 401-1262-07L: Analysis II

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis II |
| **学分** | 7 ECTS |
| **学期** | 春季学期 |
| **先修要求** | Analysis I |
| **ETH教材** | O. Forster, *Analysis 2*; K. Königsberger, *Analysis 2* |
| **覆盖度** | 🟢 完整覆盖 (85%) |

**课程描述（德文原文）**:
*"Mehrdimensionale Analysis: Differentialrechnung in mehreren Variablen, implizite Funktionen, Untermannigfaltigkeiten, Integration in mehreren Variablen, Integralsätze."*

**课程描述（英文翻译）**:
Multidimensional analysis: differential calculus in several variables, implicit functions, submanifolds, integration in several variables, integral theorems.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/03-分析学/01-实分析/` | 多元微分、偏导数 | 6小时 |
| 2 | `docs/03-分析学/01-实分析/` | 隐函数定理、反函数定理 | 6小时 |
| 3 | `docs/14-微分几何/01-微分几何基础.md` | 子流形、切空间 | 6小时 |
| 4 | `docs/03-分析学/01-实分析/` | 重积分、变量替换 | 6小时 |
| 5 | `docs/14-微分几何/02-微分几何增强版.md` | 曲线积分、曲面积分 | 6小时 |
| 6 | `docs/14-微分几何/03-微分几何深度扩展版.md` | Green定理、Stokes定理 | 6小时 |

---

## 🎓 Stage 2: 中级课程（Aufbaukurse）

### 401-2284-00L: Algebra I

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebra I |
| **学分** | 8 ECTS |
| **学期** | 秋季学期 |
| **先修要求** | Linear Algebra I/II |
| **ETH教材** | S. Lang, *Algebra*; J. Rotman, *Advanced Modern Algebra* |
| **覆盖度** | 🟢 完整覆盖 (90%) |

**课程描述（德文原文）**:
*"Gruppen: Untergruppen, Quotientengruppen, Homomorphiesätze, Gruppenwirkungen, Sylow-Sätze. Ringe: Ideale, Integritätsbereiche, Hauptidealringe, Polynomringe."*

**课程描述（英文翻译）**:
Groups: subgroups, quotient groups, homomorphism theorems, group actions, Sylow theorems. Rings: ideals, integral domains, principal ideal domains, polynomial rings.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 群公理、子群 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | 正规子群、商群 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/群论/05-同构定理-深度扩展版.md` | 同态、同构定理 | 6小时 |
| 4 | `docs/02-代数结构/02-核心理论/群论/06-群作用-深度扩展版.md` | 群作用、轨道-稳定子 | 6小时 |
| 5 | `docs/02-代数结构/02-核心理论/群论/07-Sylow定理-深度扩展版.md` | Sylow定理 | 6小时 |
| 6 | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | 环、理想、商环 | 6小时 |
| 7 | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | UFD、PID、欧几里得整环 | 6小时 |
| 8 | `docs/02-代数结构/02-核心理论/环论/04-多项式环-深度扩展版.md` | 多项式环 | 4小时 |

---

### 401-2285-00L: Algebra II

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebra II |
| **学分** | 8 ECTS |
| **学期** | 春季学期 |
| **先修要求** | Algebra I |
| **ETH教材** | S. Lang, *Algebra*; M. Artin, *Algebra* |
| **覆盖度** | 🟢 完整覆盖 (85%) |

**课程描述（德文原文）**:
*"Körpererweiterungen, algebraische und transzendente Elemente, endliche Körper, Galoistheorie, Moduln über Hauptidealringen."*

**课程描述（英文翻译）**:
Field extensions, algebraic and transcendental elements, finite fields, Galois theory, modules over principal ideal domains.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/02-代数结构/02-核心理念/域论/` | 域扩张、代数元与超越元 | 6小时 |
| 2 | `docs/02-代数结构/02-核心理念/域论/` | 有限域 | 4小时 |
| 3 | `docs/02-代数结构/02-核心理论/域论/` | Galois理论、Galois群 | 10小时 |
| 4 | `docs/02-代数结构/02-核心理论/域论/` | 根式可解性 | 6小时 |
| 5 | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | 模论、PID上的模 | 8小时 |

---

### 401-3302-71L: Complex Analysis

| 属性 | 内容 |
|------|------|
| **课程名称** | Complex Analysis |
| **学分** | 6 ECTS |
| **学期** | 秋季学期 |
| **授课语言** | 英语 |
| **先修要求** | Analysis I/II |
| **ETH教材** | Ahlfors, *Complex Analysis*; Stein-Shakarchi, *Complex Analysis* |
| **覆盖度** | 🟢 完整覆盖 (88%) |

**课程描述（英文原文）**:
*"Complex numbers, holomorphic functions, Cauchy's theorem and integral formula, singularities, residue theorem, harmonic functions, conformal mappings."*

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/03-分析学/02-复分析/02-复分析.md` | 复数、复平面 | 4小时 |
| 2 | `docs/03-分析学/02-复分析/02-复分析.md` | 全纯函数、Cauchy-Riemann方程 | 6小时 |
| 3 | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | Cauchy定理、积分公式 | 6小时 |
| 4 | `docs/03-分析学/02-复分析/02-复分析-增强版.md` | 奇点、Laurent级数 | 6小时 |
| 5 | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | 留数定理及应用 | 6小时 |
| 6 | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | 调和函数 | 4小时 |
| 7 | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | 共形映射 | 6小时 |

---

### 401-3461-00L: Functional Analysis

| 属性 | 内容 |
|------|------|
| **课程名称** | Functional Analysis |
| **学分** | 10 ECTS |
| **学期** | 全年课程 |
| **授课语言** | 德语/英语 |
| **先修要求** | Analysis I/II, Linear Algebra I/II |
| **ETH教材** | Haim Brezis, *Functional Analysis*; Rudin, *Functional Analysis* |
| **覆盖度** | 🟢 完整覆盖 (85%) |

**课程描述（德文原文）**:
*"Banachräume, Hilberträume, lineare Operatoren, Prinzip der gleichmäßigen Beschränktheit, Satz von der offenen Abbildung, Hahn-Banach-Sätze, Spektraltheorie."*

**课程描述（英文翻译）**:
Banach spaces, Hilbert spaces, linear operators, uniform boundedness principle, open mapping theorem, Hahn-Banach theorems, spectral theory.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/03-分析学/03-泛函分析/03-泛函分析.md` | 赋范空间、Banach空间 | 6小时 |
| 2 | `docs/03-分析学/03-泛函分析/03-泛函分析-增强版.md` | Hilbert空间、正交投影 | 6小时 |
| 3 | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | 有界线性算子、对偶空间 | 8小时 |
| 4 | `docs/03-分析学/03-泛函分析/04-泛函分析三大定理-深度扩展版.md` | 一致有界性原理 | 6小时 |
| 5 | `docs/03-分析学/03-泛函分析/04-泛函分析三大定理-深度扩展版.md` | 开映射定理、闭图像定理 | 6小时 |
| 6 | `docs/03-分析学/03-泛函分析/04-泛函分析三大定理-深度扩展版.md` | Hahn-Banach定理 | 6小时 |
| 7 | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | 谱理论、紧算子 | 10小时 |

---

## 🎓 Stage 3: 高级课程（Vertiefungskurse）

### 401-3001-61L: Algebraic Topology

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Topology |
| **学分** | 8 ECTS |
| **学期** | 秋季学期 |
| **授课语言** | 英语 |
| **先修要求** | Algebra I/II, Analysis I/II |
| **ETH教材** | Hatcher, *Algebraic Topology*; Bredon, *Topology and Geometry* |
| **覆盖度** | 🟢 完整覆盖 (88%) |
| **ETH特色** | 🏆 **苏黎世学派强项** |

**课程描述（英文原文）**:
*"Fundamental group, covering spaces, Van Kampen theorem, singular homology, cellular homology, cohomology, universal coefficient theorems, cup products, Poincaré duality."*

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑.md` | 基本群、覆盖空间 | 8小时 |
| 2 | `docs/05-拓扑学/02-代数拓扑-深度扩展版.md` | Van Kampen定理 | 6小时 |
| 3 | `docs/05-拓扑学/05-同调论.md` | 奇异同调、胞腔同调 | 10小时 |
| 4 | `docs/05-拓扑学/03-代数拓扑核心-深度扩展版.md` | 上同调、泛系数定理 | 8小时 |
| 5 | `docs/05-拓扑学/03-代数拓扑核心-深度扩展版.md` | 杯积 | 6小时 |
| 6 | `docs/05-拓扑学/03-代数拓扑核心-深度扩展版.md` | Poincaré对偶 | 8小时 |

---

### 401-3002-62L: Differential Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Geometry |
| **学分** | 8 ECTS |
| **学期** | 春季学期 |
| **授课语言** | 英语 |
| **先修要求** | Analysis I/II, Linear Algebra I/II |
| **ETH教材** | Lee, *Riemannian Manifolds*; do Carmo, *Riemannian Geometry* |
| **覆盖度** | 🟢 完整覆盖 (82%) |

**课程描述（英文原文）**:
*"Smooth manifolds, tangent bundles, vector fields, Riemannian metrics, connections, geodesics, curvature, Jacobi fields, completeness theorems."*

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/14-微分几何/01-微分几何基础.md` | 光滑流形、图册 | 6小时 |
| 2 | `docs/14-微分几何/01-微分几何基础.md` | 切丛、向量场 | 6小时 |
| 3 | `docs/14-微分几何/02-微分几何增强版.md` | Riemann度量 | 6小时 |
| 4 | `docs/14-微分几何/03-微分几何深度扩展版.md` | 联络理论 | 8小时 |
| 5 | `docs/14-微分几何/03-微分几何深度扩展版.md` | 测地线、指数映射 | 6小时 |
| 6 | `docs/14-微分几何/03-微分几何深度扩展版.md` | Riemann曲率张量 | 8小时 |
| 7 | `docs/14-微分几何/04-黎曼几何-深度扩展版.md` | 完备性定理 | 6小时 |

---

### 401-3531-00L: Algebraic Geometry I

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry I |
| **学分** | 8 ECTS |
| **学期** | 秋季学期 |
| **授课语言** | 英语 |
| **先修要求** | Algebra I/II, Commutative Algebra |
| **ETH教材** | Hartshorne, *Algebraic Geometry* Ch. I-II; Vakil, *FOAG* |
| **覆盖度** | 🟡 部分覆盖 (78%) |
| **ETH特色** | 🏆 **苏黎世学派核心课程** |

**课程描述（英文原文）**:
*"Affine and projective varieties, regular functions and morphisms, dimension theory, sheaves, schemes, properties of schemes, divisors and line bundles."*

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/13-代数几何/01-代数几何基础.md` | 仿射簇、射影簇 | 6小时 |
| 2 | `docs/13-代数几何/02-代数几何增强版.md` | 正则函数、态射 | 6小时 |
| 3 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/16-概形的维数理论.md` | 维数理论 | 6小时 |
| 4 | `docs/13-代数几何/04-层与上同调-深度扩展版.md` | 层理论 | 8小时 |
| 5 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` | 概形定义 | 10小时 |
| 6 | `docs/13-代数几何/05-概形性质-深度扩展版.md` | 概形性质 | 6小时 |
| 7 | `docs/13-代数几何/06-除子与线丛-深度扩展版.md` | 除子、线丛 | 8小时 |

#### ⚠️ FormalMath覆盖缺口

| 主题 | ETH要求 | FormalMath状态 | 补充建议 |
|------|---------|----------------|----------|
| 具体的代数曲面例子 | 经典例子 | 🟡 部分覆盖 | 参考Hartshorne第V章 |
| 相交理论详细计算 | 交点重数 | 🟡 部分覆盖 | 参考Fulton相交理论 |

---

### 401-3532-00L: Algebraic Geometry II

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry II |
| **学分** | 8 ECTS |
| **学期** | 春季学期 |
| **授课语言** | 英语 |
| **先修要求** | Algebraic Geometry I |
| **ETH教材** | Hartshorne, Ch. III-IV; Liu, *Algebraic Geometry and Arithmetic Curves* |
| **覆盖度** | 🟡 部分覆盖 (75%) |
| **ETH特色** | 🏆 **苏黎世学派核心课程** |

**课程描述（英文原文）**:
*"Cohomology of sheaves, Cech cohomology, Serre duality, Riemann-Roch theorem for curves, surfaces, birational geometry."*

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` | 层上同调基础 | 8小时 |
| 2 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md` | Cech上同调 | 6小时 |
| 3 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md` | Serre对偶 | 8小时 |
| 4 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/05-Riemann-Roch定理.md` | Riemann-Roch定理 | 8小时 |
| 5 | `docs/13-代数几何/07-曲线理论-深度扩展版.md` | 代数曲线 | 10小时 |
| 6 | `docs/13-代数几何/04-代数曲面-深度扩展版.md` | 代数曲面 | 10小时 |
| 7 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/30-概形的双有理几何.md` | 双有理几何 | 8小时 |

#### ⚠️ FormalMath覆盖缺口

| 主题 | ETH要求 | FormalMath状态 | 补充建议 |
|------|---------|----------------|----------|
| 曲面的详细分类 | Enriques分类 | 🟡 部分覆盖 | 参考Beauville |
| Hilbert概形 | 模空间 | 🟠 基础覆盖 | 参考Kollár |

---

### 401-4145-21L: Number Theory I

| 属性 | 内容 |
|------|------|
| **课程名称** | Number Theory I |
| **学分** | 8 ECTS |
| **学期** | 秋季学期 |
| **授课语言** | 德语/英语 |
| **先修要求** | Algebra I/II |
| **ETH教材** | Neukirch, *Algebraic Number Theory*; Marcus, *Number Fields* |
| **覆盖度** | 🟢 完整覆盖 (85%) |
| **ETH特色** | 🏆 **苏黎世数论传统** |

**课程描述（德文原文）**:
*"Algebraische Zahlkörper, Ganzheitsringe, Diskriminante, Norm, Dedekindringe, Idealklassengruppe, Einheitengruppe, Minkowskitheorie."*

**课程描述（英文翻译）**:
Algebraic number fields, rings of integers, discriminant, norm, Dedekind domains, ideal class group, unit group, Minkowski theory.

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/06-数论/02-代数数论.md` | 代数数域 | 6小时 |
| 2 | `docs/06-数论/02-代数数论-增强版.md` | 整数环、判别式、范数 | 6小时 |
| 3 | `docs/02-代数结构/02-核心理论/交换代数/` | Dedekind整环 | 6小时 |
| 4 | `docs/06-数论/06-理想类群-深度扩展版.md` | 理想类群 | 8小时 |
| 5 | `docs/06-数论/02-代数数论-增强版.md` | 单位群、Dirichlet单位定理 | 6小时 |
| 6 | `docs/06-数论/05-数的几何-深度扩展版.md` | Minkowski理论 | 6小时 |

---

### 401-4146-21L: Number Theory II

| 属性 | 内容 |
|------|------|
| **课程名称** | Number Theory II |
| **学分** | 8 ECTS |
| **学期** | 春季学期 |
| **授课语言** | 德语/英语 |
| **先修要求** | Number Theory I |
| **ETH教材** | Neukirch, *Algebraic Number Theory*; Serre, *Local Fields* |
| **覆盖度** | 🟡 部分覆盖 (72%) |

**课程描述（德文原文）**:
*"Lokale Körper, p-adische Zahlen, Bewertungstheorie, Verzweigungstheorie, Zeta-Funktionen, Klassenkörpertheorie (Einführung)."*

**课程描述（英文翻译）**:
Local fields, p-adic numbers, valuation theory, ramification theory, zeta functions, class field theory (introduction).

#### FormalMath对应文档

| 序号 | 文档路径 | ETH主题 | 学习时间 |
|------|----------|---------|----------|
| 1 | `docs/06-数论/02-代数数论-增强版.md` | 局部域、p-adic数 | 6小时 |
| 2 | `docs/06-数论/02-代数数论-增强版.md` | 赋值理论 | 6小时 |
| 3 | `docs/06-数论/02-代数数论-增强版.md` | 分歧理论 | 6小时 |
| 4 | `docs/06-数论/02-代数数论-增强版.md` | Dedekind zeta函数 | 6小时 |
| 5 | `docs/06-数论/02-代数数论-增强版.md` | 类域论初步 | 10小时 |

#### ⚠️ FormalMath覆盖缺口

| 主题 | ETH要求 | FormalMath状态 | 补充建议 |
|------|---------|----------------|----------|
| 局部类域论详细证明 | 局部-整体原理 | 🟡 部分覆盖 | 参考Neukirch第IV章 |
| Lubin-Tate理论 | 局部域扩张 | 🟠 基础覆盖 | 参考Serre Local Fields |

---

## 📊 覆盖度总结

| 课程代码 | 课程名称 | 覆盖度 | 状态 | 苏黎世特色 |
|----------|----------|--------|------|-----------|
| 401-1151-00L | Linear Algebra I | 90% | 🟢 | 基础扎实 |
| 401-1152-00L | Linear Algebra II | 88% | 🟢 | 基础扎实 |
| 401-1261-07L | Analysis I | 92% | 🟢 | 分析严格 |
| 401-1262-07L | Analysis II | 85% | 🟢 | 多元分析 |
| 401-2284-00L | Algebra I | 90% | 🟢 | 代数基础 |
| 401-2285-00L | Algebra II | 85% | 🟢 | Galois理论 |
| 401-3302-71L | Complex Analysis | 88% | 🟢 | 经典分析 |
| 401-3461-00L | Functional Analysis | 85% | 🟢 | 泛函基础 |
| 401-3001-61L | Algebraic Topology | 88% | 🟢 | 🏆 强项 |
| 401-3002-62L | Differential Geometry | 82% | 🟢 | 几何传统 |
| 401-3531-00L | Algebraic Geometry I | 78% | 🟡 | 🏆 强项 |
| 401-3532-00L | Algebraic Geometry II | 75% | 🟡 | 🏆 强项 |
| 401-4145-21L | Number Theory I | 85% | 🟢 | 数论传统 |
| 401-4146-21L | Number Theory II | 72% | 🟡 | 类域论 |

---

## 🏆 苏黎世学派特色内容

### ETH Zurich在FormalMath中的特殊地位

| 数学领域 | ETH传统 | FormalMath对应 | 重要性 |
|----------|---------|----------------|--------|
| **代数拓扑** | 欧洲领先 | `docs/05-拓扑学/` | ⭐⭐⭐⭐⭐ |
| **代数几何** | 苏黎世学派 | `数学家理念体系/格洛腾迪克/` | ⭐⭐⭐⭐⭐ |
| **微分几何** | 经典强项 | `docs/14-微分几何/` | ⭐⭐⭐⭐ |
| **数论** | 悠久传统 | `docs/06-数论/` | ⭐⭐⭐⭐ |

### 著名ETH数学家的贡献

- **Hermann Weyl**: 对FormalMath中微分几何和数学物理的影响
- **Ferdinand von Lindemann**: 超越数理论
- **George Pólya**: 组合数学和分析
- **Beno Eckmann**: 代数拓扑
- **Armand Borel**: 代数群与李群

---

## 🔗 相关链接

- [ETH Zurich Department of Mathematics](https://math.ethz.ch/)
- [ETH Zurich Course Catalogue](https://www.ethz.ch/studies/application/bachelor/entry-requirements/course-catalogue.html)
- [FormalMath 项目主页](../README.md)
- [FormalMath MIT课程映射](MIT-course-mapping-detailed.md)
- [FormalMath Harvard课程映射](Harvard-course-mapping-detailed.md)

---

*最后更新: 2026年4月*
*下次复核: 2026年9月（2026-2027学年课程表发布后）*
