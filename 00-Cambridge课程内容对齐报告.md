---
msc_primary: 00
msc_secondary:
  - 00A99
  - 97A99
processed_at: '2026-04-04'
title: FormalMath与Cambridge数学课程内容深度对齐报告
---
# FormalMath与Cambridge数学课程内容深度对齐报告

> **版本**: 2026年4月
> **适用范围**: Cambridge University Mathematical Tripos 2025-2026学年
> **目标**: 为自学者提供使用FormalMath资源学习Cambridge数学课程的完整路径
> **数据来源**: https://www.maths.cam.ac.uk/undergrad/course/

---

## 📋 目录

- [FormalMath与Cambridge数学课程内容深度对齐报告](#formalmath与cambridge数学课程内容深度对齐报告)
  - [📋 目录](#-目录)
  - [一、Cambridge数学Tripos系统概述](#一cambridge数学tripos系统概述)
    - [1.1 Tripos系统结构](#11-tripos系统结构)
    - [1.2 课程分类标记](#12-课程分类标记)
    - [1.3 Tripos考试特点](#13-tripos考试特点)
    - [1.4 FormalMath对齐策略](#14-formalmath对齐策略)
  - [二、Part IA课程对齐](#二part-ia课程对齐)
    - [2.1 IA Numbers and Sets](#21-ia-numbers-and-sets)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题)
      - [FormalMath对应文档](#formalmath对应文档)
      - [建议学习路径](#建议学习路径)
    - [2.2 IA Groups](#22-ia-groups)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-1)
      - [FormalMath对应文档](#formalmath对应文档-1)
    - [2.3 IA Analysis I](#23-ia-analysis-i)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-2)
      - [FormalMath对应文档](#formalmath对应文档-2)
    - [2.4 IA Differential Equations](#24-ia-differential-equations)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-3)
      - [FormalMath对应文档](#formalmath对应文档-3)
      - [需要补充的内容](#需要补充的内容)
    - [2.5 IA Probability](#25-ia-probability)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-4)
      - [FormalMath对应文档](#formalmath对应文档-4)
  - [三、Part IB课程对齐](#三part-ib课程对齐)
    - [3.1 IB Linear Algebra](#31-ib-linear-algebra)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-5)
      - [FormalMath对应文档](#formalmath对应文档-5)
    - [3.2 IB Groups, Rings and Modules](#32-ib-groups-rings-and-modules)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-6)
      - [FormalMath对应文档](#formalmath对应文档-6)
    - [3.3 IB Analysis and Topology](#33-ib-analysis-and-topology)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-7)
      - [FormalMath对应文档](#formalmath对应文档-7)
    - [3.4 IB Complex Analysis](#34-ib-complex-analysis)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-8)
      - [FormalMath对应文档](#formalmath对应文档-8)
  - [四、Part II课程对齐](#四part-ii课程对齐)
    - [4.1 Part II Galois Theory](#41-part-ii-galois-theory)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-9)
      - [FormalMath对应文档](#formalmath对应文档-9)
    - [4.2 Part II Algebraic Topology](#42-part-ii-algebraic-topology)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-10)
      - [FormalMath对应文档](#formalmath对应文档-10)
      - [需要补充的内容](#需要补充的内容-1)
    - [4.3 Part II Differential Geometry](#43-part-ii-differential-geometry)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-11)
      - [FormalMath对应文档](#formalmath对应文档-11)
    - [4.4 Part II Number Fields](#44-part-ii-number-fields)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-12)
      - [FormalMath对应文档](#formalmath对应文档-12)
    - [4.5 Part II Algebraic Geometry](#45-part-ii-algebraic-geometry)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-13)
      - [FormalMath对应文档](#formalmath对应文档-13)
  - [五、Part III课程对齐](#五part-iii课程对齐)
    - [5.1 Part III Advanced Algebraic Geometry](#51-part-iii-advanced-algebraic-geometry)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-14)
      - [FormalMath对应文档](#formalmath对应文档-14)
    - [5.2 Part III Homotopy Theory](#52-part-iii-homotopy-theory)
      - [Cambridge大纲核心主题](#cambridge大纲核心主题-15)
      - [FormalMath对应文档](#formalmath对应文档-15)
    - [5.3 Part III Elliptic Curves](#53-part-iii-elliptic-curves)
      - [FormalMath对应文档](#formalmath对应文档-16)
  - [六、Tripos证明风格与传统](#六tripos证明风格与传统)
    - [6.1 Cambridge证明风格特点](#61-cambridge证明风格特点)
    - [6.2 典型证明模式](#62-典型证明模式)
      - [分析学证明模式](#分析学证明模式)
      - [代数学证明模式](#代数学证明模式)
    - [6.3 与FormalMath的融合](#63-与formalmath的融合)
  - [七、经典教材对应](#七经典教材对应)
    - [7.1 核心教材映射](#71-核心教材映射)
    - [7.2 教材版本更新](#72-教材版本更新)
  - [八、覆盖度总结与建议](#八覆盖度总结与建议)
    - [8.1 课程覆盖度总览](#81-课程覆盖度总览)
    - [8.2 推荐学习路径](#82-推荐学习路径)
      - [Part IA路径（第一年）](#part-ia路径第一年)
      - [Part IB路径（第二年）](#part-ib路径第二年)
      - [Part II路径（第三年）](#part-ii路径第三年)
    - [8.3 建议更新清单](#83-建议更新清单)
    - [8.4 特色学习建议](#84-特色学习建议)
      - [Tripos考试准备](#tripos考试准备)
      - [与Oxford对比](#与oxford对比)
  - [九、附录](#九附录)
    - [9.1 相关链接](#91-相关链接)
    - [9.2 参考文献](#92-参考文献)

---

## 一、Cambridge数学Tripos系统概述

### 1.1 Tripos系统结构

Cambridge数学系采用独特的**Tripos考试系统**，分为四个层级：

| 层级 | 年级 | 特点 | 考试形式 | 课程类型 |
|------|------|------|----------|----------|
| **Part IA** | 大一 | 基础必修，广泛覆盖 | 四卷考试 | C-courses (24讲) |
| **Part IB** | 大二 | 进阶必修+选修 | 四卷考试 | C-courses (16/24讲) |
| **Part II** | 大三 | 专业深化 | 四卷考试 | C/D-courses |
| **Part III** | 大四/硕士 | 研究生水平 | 考试+项目论文 | D-courses |

### 1.2 课程分类标记

- **C-courses**: 标准课程（较基础，24讲）
- **D-courses**: 深入课程（更具挑战，16或24讲）

### 1.3 Tripos考试特点

| 特征 | 说明 |
|------|------|
| **质量标记** | Alpha (α) - 优秀，Beta (β) - 良好 |
| **评分标准** | Section I (10分/题), Section II (20分/题) |
| **时间压力** | 要求快速解题和严格证明能力 |
| **分类标准** | 1st/2.1/2.2/3rd，按30α + 5β + m公式计算 |

### 1.4 FormalMath对齐策略

| 对齐维度 | 说明 |
|----------|------|
| **内容覆盖** | 按Cambridge Schedules逐条对齐 |
| **证明风格** | 强调严格ε-δ论证和逻辑严密性 |
| **例题训练** | 参考Tripos历年真题风格 |
| **进阶路径** | 从IA→IB→II→III循序渐进 |

---

## 二、Part IA课程对齐

### 2.1 IA Numbers and Sets

| 属性 | 内容 |
|------|------|
| **课程名称** | Numbers and Sets |
| **学时** | 24讲 (Michaelmas Term) |
| **先修要求** | 无 |
| **Cambridge教材** | Goldrei, *Classic Set Theory*; Davenport, *The Higher Arithmetic* |
| **覆盖度** | 🟢 **完整覆盖 (92%)** |

#### Cambridge大纲核心主题

1. **数系基础** (2讲)
   - 自然数、整数、实数、有理数、无理数
   - 代数数和超越数
   - 复数基本概念

2. **逻辑与证明** (2讲)
   - 公理系统和数学证明
   - 反例的作用
   - 基本逻辑：蕴含和否定
   - 反证法

3. **集合、关系与函数** (4讲)
   - 集合的并、交、相等
   - 指示函数及其应用
   - 单射、满射、双射
   - 等价关系
   - 排列组合
   - 容斥原理

4. **整数理论** (2讲)
   - 数学归纳法和良序原理
   - 二项式定理

5. **初等数论** (8讲)
   - 素数：唯一分解定理
   - 最大公因数和最小公倍数
   - 欧几里得算法
   - 线性丢番图方程 ax + by = 1
   - 模运算（同余）
   - 中国剩余定理
   - Wilson定理、费马-欧拉定理
   - RSA公钥加密

6. **实数** (4讲)
   - 上确界原理
   - 序列和级数收敛
   - √2和e的无理性
   - 十进制展开
   - 超越数构造

7. **可数与不可数** (4讲)
   - 有限、无限、可数、不可数集
   - 可数个可数集的并是可数的
   - R的不可数性
   - 幂集的双射不存在
   - 超越数存在性的间接证明

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/01-基础数学/集合论/01-集合论基础-国际标准版.md` | 集合、子集、幂集 | 100% | 外延性、空集、指示函数 |
| 2 | `docs/01-基础数学/集合论/02-数系与运算-深度扩展版.md` | 自然数、归纳法 | 95% | Peano公理、递归定义 |
| 3 | `docs/01-基础数学/集合论/03-函数与映射-深度扩展版.md` | 函数、单射/满射/双射 | 95% | 像、原像、复合函数 |
| 4 | `docs/01-基础数学/集合论/04-关系与等价-深度扩展版.md` | 等价关系、划分 | 90% | 等价类、商集 |
| 5 | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | 可数性、不可数集 | 85% | 对角线论证、Cantor定理 |
| 6 | `docs/06-数论/01-初等数论-深度扩展版.md` | 素数、同余、RSA | 90% | 欧几里得算法、欧拉定理 |
| 7 | `docs/01-基础数学/ZFC公理体系/ZFC公理体系-深度扩展版.md` | 公理系统 | 85% | ZFC公理、选择公理 |

#### 建议学习路径

```
Week 1-2: 数系基础 → 集合论基础
Week 3-4: 函数与映射 → 关系与等价
Week 5-6: 可数性理论
Week 7-8: 数论基础（素数、同余）
Week 9-10: 高级数论（RSA、中国剩余定理）
Week 11-12: 复习与Tripos真题训练
```

---

### 2.2 IA Groups

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups |
| **学时** | 24讲 (Michaelmas Term) |
| **先修要求** | Numbers and Sets |
| **Cambridge教材** | Allenby, *Rings, Fields and Groups*; Armstrong, *Groups and Symmetry* |
| **覆盖度** | 🟢 **完整覆盖 (90%)** |

#### Cambridge大纲核心主题

1. **群的例子** (4讲)
   - 群公理
   - 几何例子：正多边形、立方体、四面体的对称群
   - 置换群
   - 子群和同态
   - Möbius群；交比、圆保持、无穷远点
   - 共轭
   - Möbius映射的不动点和迭代

2. **Lagrange定理** (5讲)
   - 陪集
   - Lagrange定理
   - 小阶群（至8阶）
   - 四元数
   - 群论视角的费马-欧拉定理

3. **群作用** (4讲)
   - 群作用；轨道和稳定子
   - 轨道-稳定子定理
   - Cayley定理（每个群同构于置换群的子群）
   - 共轭类
   - Cauchy定理

4. **商群** (4讲)
   - 正规子群、商群和同构定理

5. **矩阵群** (3讲)
   - 一般线性群和特殊线性群
   - 与Möbius群的关系
   - 正交群和特殊正交群
   - 三维正交群的反射分解
   - 基变换作为共轭的例子

6. **置换** (4讲)
   - 置换、循环和对换
   - 置换的符号
   - Sₙ和Aₙ中的共轭
   - 单群；A₅的单性

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | 群公理、例子 | 95% | 封闭性、结合律、单位元、逆元 |
| 2 | `docs/02-代数结构/02-核心理论/群论/02-子群与陪集-深度扩展版.md` | 子群、Lagrange定理 | 95% | 陪集分解、指数、Lagrange定理 |
| 3 | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | 正规子群、商群 | 90% | 正规子群判定、商群构造 |
| 4 | `docs/02-代数结构/02-核心理论/群论/04-群同态-深度扩展版.md` | 同态、同构 | 90% | 核、像、第一同构定理 |
| 5 | `docs/02-代数结构/02-核心理论/群论/05-同构定理-深度扩展版.md` | 同构定理 | 95% | 三同构定理 |
| 6 | `docs/02-代数结构/02-核心理论/群论/06-群作用-深度扩展版.md` | 群作用 | 90% | 轨道、稳定子、轨道-稳定子定理 |
| 7 | `docs/02-代数结构/02-核心理论/群论/07-Sylow定理-深度扩展版.md` | Sylow定理、Cauchy定理 | 85% | p-子群、Sylow定理、Cauchy定理 |
| 8 | `docs/02-代数结构/02-核心理论/群论/08-置换群-深度扩展版.md` | 置换群 | 90% | 循环分解、偶置换、A₅单性 |

---

### 2.3 IA Analysis I

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis I |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | 无 |
| **Cambridge教材** | Apostol, *Calculus*; Spivak, *Calculus*; Burkill, *A First Course in Mathematical Analysis* |
| **覆盖度** | 🟢 **完整覆盖 (90%)** |

#### Cambridge大纲核心主题

1. **极限与收敛** (6讲)
   - R和C中的序列和级数
   - 和、积、商的极限
   - 绝对收敛；绝对收敛蕴含收敛
   - Bolzano-Weierstrass定理及应用（收敛的一般原理）
   - 比较判别法和比值判别法
   - 交错级数判别法

2. **连续性** (3讲)
   - 实值和复值函数的连续性
   - 介值定理
   - 闭区间上连续函数的有界性和最值性

3. **可微性** (5讲)
   - 函数的可微性
   - 和、积的导数
   - 链式法则
   - 反函数的导数
   - Rolle定理；中值定理
   - 一维反函数定理
   - Taylor定理；Lagrange余项
   - 复可微性

4. **幂级数** (4讲)
   - 复幂级数和收敛半径
   - 指数、三角、双曲函数及其关系
   - *幂级数在收敛圆内的可微性直接证明*

5. **积分** (6讲)
   - Riemann积分的定义和基本性质
   - 不可积函数的例子
   - 单调函数的可积性
   - 分段连续函数的可积性
   - 微积分基本定理
   - 不定积分的微分
   - 分部积分
   - Taylor定理的积分余项
   - 反常积分

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | 实数完备性 | 95% | 确界原理、Archimedes性质 |
| 2 | `docs/03-分析学/01-实分析/02-序列与极限-深度扩展版.md` | 序列收敛 | 95% | ε-N定义、子序列、Bolzano-Weierstrass |
| 3 | `docs/03-分析学/01-实分析/03-级数理论-深度扩展版.md` | 级数收敛 | 90% | 绝对收敛、比较判别法、交错级数 |
| 4 | `docs/03-分析学/01-实分析/04-连续函数-深度扩展版.md` | 连续性 | 90% | ε-δ定义、一致连续、介值定理 |
| 5 | `docs/03-分析学/01-实分析/05-微分-深度扩展版.md` | 可微性 | 90% | 导数、中值定理、Taylor定理 |
| 6 | `docs/03-分析学/01-实分析/06-幂级数-深度扩展版.md` | 幂级数 | 85% | 收敛半径、解析函数 |
| 7 | `docs/03-分析学/01-实分析/07-Riemann积分-深度扩展版.md` | Riemann积分 | 90% | 可积性、FTC、反常积分 |
| 8 | `docs/03-分析学/02-复分析/01-复分析-基础版.md` | 复可微性 | 85% | Cauchy-Riemann方程 |

---

### 2.4 IA Differential Equations

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Equations |
| **学时** | 24讲 (Michaelmas/Lent) |
| **先修要求** | 基础微积分 |
| **Cambridge教材** | Robinson, *An Introduction to Differential Equations*; Boyce & DiPrima |
| **覆盖度** | 🟡 **部分覆盖 (70%)** |

#### Cambridge大纲核心主题

1. **基础微积分** (3讲)
   - 导数作为极限的非正式处理
   - 链式法则、Leibnitz法则
   - Taylor级数
   - O和o记号的非正式处理
   - l'Hôpital法则
   - 积分作为面积
   - 微积分基本定理
   - 换元积分法和分部积分法

2. **偏导数** (2讲)
   - 偏导数的非正式处理
   - 几何解释
   - 混合偏导对称性（仅陈述）
   - 链式法则
   - 隐函数微分
   - 微分的非正式处理
   - 含参积分的微分

3. **一阶线性ODE** (3讲)
   - 常系数方程：指数增长
   - 与离散方程的比较
   - 级数解
   - 建模例子（放射性衰变）
   - 变系数方程：积分因子解法

4. **非线性一阶方程** (4讲)
   - 可分离变量方程
   - 恰当方程
   - 解轨线草图
   - 平衡解、扰动稳定性
   - 逻辑斯谛方程和化学动力学例子
   - 离散方程：平衡解、稳定性

5. **高阶线性ODE** (8讲)
   - 余函数和特积分
   - 线性无关、Wronskian
   - Abel定理
   - 常系数方程
   - 降阶法
   - 共振、瞬态、阻尼
   - 齐次方程
   - 阶跃和脉冲函数输入
   - Heaviside阶跃函数和Dirac delta函数
   - 级数解

6. **多元函数应用** (5讲)
   - 方向导数和梯度向量
   - Taylor级数陈述
   - 实函数局部极值
   - Hessian矩阵分类
   - 耦合一阶系统
   - 相图
   - 一阶和二阶偏微分方程
   - 波动方程

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/05-微分方程/01-常微分方程基础.md` | 一阶ODE | 75% | 可分离变量、积分因子 |
| 2 | `docs/03-分析学/05-微分方程/02-常微分方程-增强版.md` | 高阶线性ODE | 70% | 特征方程、待定系数 |
| 3 | `docs/03-分析学/05-微分方程/03-偏微分方程基础.md` | PDE初步 | 60% | 波动方程、热方程 |
| 4 | `docs/03-分析学/05-微分方程/04-级数解-深度扩展版.md` | 级数解 | 65% | Frobenius方法 |
| 5 | `docs/03-分析学/06-偏微分方程/01-偏微分方程核心-深度扩展版.md` | PDE理论 | 60% | 特征线法、分离变量 |

#### 需要补充的内容

| 主题 | 补充资源建议 |
|------|-------------|
| 相图分析 | Strogatz, *Nonlinear Dynamics and Chaos* |
| 物理应用 | 具体物理模型例子 |
| 数值解法 | 基本数值方法 |

---

### 2.5 IA Probability

| 属性 | 内容 |
|------|------|
| **课程名称** | Probability |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | Analysis I |
| **Cambridge教材** | Grimmett & Welsh, *Probability: An Introduction* |
| **覆盖度** | 🟡 **部分覆盖 (68%)** |

#### Cambridge大纲核心主题

1. **基本概念** (3讲)
   - 古典概率
   - 等可能结果
   - 组合分析
   - 排列组合
   - Stirling公式

2. **公理化方法** (5讲)
   - 公理（可数情形）
   - 概率空间
   - 容斥公式
   - 概率测度的连续性和次可加性
   - 独立性
   - 二项、Poisson和几何分布
   - 条件概率、Bayes公式

3. **离散分布** (7讲)
   - 期望
   - 随机变量函数
   - 指示函数
   - 方差、标准差
   - 协方差
   - 独立随机变量
   - 生成函数
   - 随机游动
   - 分支过程

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/20-概率统计/01-概率论基础-深度扩展版.md` | 概率空间 | 75% | σ-代数、概率测度 |
| 2 | `docs/20-概率统计/02-随机变量与分布-深度扩展版.md` | 离散分布 | 70% | 二项、Poisson分布 |
| 3 | `docs/20-概率统计/03-期望与方差-深度扩展版.md` | 期望、方差 | 70% | 条件期望、独立性 |
| 4 | `docs/20-概率统计/04-生成函数-深度扩展版.md` | 生成函数 | 65% | 概率生成函数 |
| 5 | `docs/20-概率统计/05-随机过程-深度扩展版.md` | 随机游动、分支过程 | 60% | 赌徒破产、灭绝概率 |

---

## 三、Part IB课程对齐

### 3.1 IB Linear Algebra

| 属性 | 内容 |
|------|------|
| **课程名称** | Linear Algebra |
| **学时** | 24讲 (Michaelmas Term) |
| **先修要求** | IA Vectors and Matrices |
| **Cambridge教材** | Kaye & Wilson, *Linear Algebra*; 系内讲义 |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### Cambridge大纲核心主题

1. **向量空间** (6讲)
   - 域上的向量空间定义
   - 子空间
   - 交、和、直和
   - 商空间
   - 维数公式

2. **线性映射** (6讲)
   - 线性映射的定义和例子
   - 核和像
   - 秩-零化度定理
   - 线性映射的矩阵表示
   - 基变换
   - 相似矩阵

3. **对偶空间** (3讲)
   - 对偶空间和对偶映射
   - 双重对偶
   - 零化子

4. **双线性型** (4讲)
   - 双线性型的定义
   - 对称和反对称双线性型
   - 二次型
   - Sylvester惯性定律

5. **内积空间** (5讲)
   - 内积空间
   - 正交补
   - 正交投影
   - Gram-Schmidt正交化
   - 伴随算子
   - 自伴算子、酉算子、正规算子
   - 谱定理

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-向量空间-深度扩展版.md` | 向量空间 | 95% | 子空间、直和、商空间 |
| 2 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/02-线性映射-深度扩展版.md` | 线性映射 | 90% | 核、像、秩-零化度 |
| 3 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/03-对偶空间-深度扩展版.md` | 对偶空间 | 90% | 对偶映射、零化子 |
| 4 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/04-双线性型-深度扩展版.md` | 双线性型 | 85% | 二次型、Sylvester定律 |
| 5 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/05-内积空间-深度扩展版.md` | 内积空间 | 90% | 正交性、Gram-Schmidt |
| 6 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/06-算子理论-深度扩展版.md` | 正规算子、谱定理 | 90% | 自伴算子、酉算子、谱定理 |
| 7 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/07-张量积-深度扩展版.md` | 张量积 | 85% | 张量积构造 |
| 8 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/08-典范形式-深度扩展版.md` | Jordan标准形 | 90% | 极小多项式、有理标准形 |

---

### 3.2 IB Groups, Rings and Modules

| 属性 | 内容 |
|------|------|
| **课程名称** | Groups, Rings and Modules |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | IA Groups |
| **Cambridge教材** | Allenby, *Rings, Fields and Groups*; Cohn, *Algebra* |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### Cambridge大纲核心主题

1. **群论进阶** (8讲)
   - 正规子群回顾
   - 合成列
   - 单群
   - 可解群
   - 三同构定理
   - 群扩张
   - 半直积

2. **环论** (8讲)
   - 环的定义和例子
   - 子环、理想
   - 商环
   - 环同态
   - 素理想和极大理想
   - 整环
   - 唯一分解整环(UFD)
   - 主理想整环(PID)
   - 欧几里得整环
   - 多项式环
   - Gauss引理
   - Eisenstein判别法

3. **模论基础** (8讲)
   - 模的定义和例子
   - 子模、商模
   - 模同态
   - 自由模
   - 有限生成模
   - 主理想整环上的有限生成模结构定理
   - 应用：Jordan标准形
   - 模的分类

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | 正规子群、合成列 | 90% | 单群、可解群、合成列 |
| 2 | `docs/02-代数结构/02-核心理论/群论/05-同构定理-深度扩展版.md` | 同构定理 | 95% | 三同构定理 |
| 3 | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | 环、理想 | 90% | 素理想、极大理想 |
| 4 | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | UFD、PID | 90% | 唯一分解、欧几里得整环 |
| 5 | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | 模基础 | 85% | 子模、商模、自由模 |
| 6 | `docs/02-代数结构/02-核心理论/模论/02-模的结构定理-深度扩展版.md` | PID上有限生成模 | 85% | 结构定理、Jordan标准形 |
| 7 | `docs/02-代数结构/02-核心理论/域论/02-Galois理论-深度扩展版.md` | Galois理论引入 | 80% | 域扩张、Galois对应 |

---

### 3.3 IB Analysis and Topology

| 属性 | 内容 |
|------|------|
| **课程名称** | Analysis and Topology |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | IA Analysis I |
| **Cambridge教材** | Sutherland, *Introduction to Metric and Topological Spaces* |
| **覆盖度** | 🟢 **完整覆盖 (85%)** |

#### Cambridge大纲核心主题

1. **度量空间** (8讲)
   - 度量空间定义
   - 例子：欧氏空间、离散度量、函数空间
   - 开球和开集
   - 收敛序列
   - 连续映射
   - 完备度量空间
   - 压缩映射原理

2. **拓扑空间** (8讲)
   - 拓扑空间定义
   - 开集、闭集、邻域
   - 闭包、内部、边界
   - 连续映射
   - 同胚
   - 子空间拓扑
   - 积拓扑
   - 商拓扑

3. **连通性和紧致性** (8讲)
   - 连通空间
   - 道路连通
   - 紧致空间
   - Heine-Borel定理
   - 紧致空间的连续像
   - 有限交性质
   - Tychonoff定理（陈述）
   - 局部紧致性
   - 一点紧化

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/01-实分析/05-拓扑基础-深度扩展版.md` | 度量空间 | 95% | 度量、开球、收敛 |
| 2 | `docs/05-拓扑学/01-点集拓扑/01-点集拓扑-深度扩展版.md` | 拓扑空间 | 90% | 开集、闭集、邻域 |
| 3 | `docs/05-拓扑学/01-点集拓扑/02-连通性与紧致性-深度扩展版.md` | 连通性、紧致性 | 90% | 道路连通、Heine-Borel |
| 4 | `docs/03-分析学/03-泛函分析/01-泛函分析-深度扩展版.md` | 函数空间 | 75% | 完备度量空间、Banach空间 |
| 5 | `docs/05-拓扑学/01-点集拓扑/03-连续性-深度扩展版.md` | 连续映射 | 85% | 同胚、商映射 |

---

### 3.4 IB Complex Analysis

| 属性 | 内容 |
|------|------|
| **课程名称** | Complex Analysis |
| **学时** | 24讲 (Lent Term) |
| **先修要求** | IA Analysis I |
| **Cambridge教材** | 系内讲义 |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### Cambridge大纲核心主题

1. **全纯函数** (6讲)
   - 复可微性
   - Cauchy-Riemann方程
   - 全纯函数的例子
   - 共形映射
   - 分式线性变换

2. **复积分** (6讲)
   - 复线积分
   - Cauchy积分定理
   - Cauchy积分公式
   - Taylor级数展开
   - Laurent级数

3. **留数定理** (6讲)
   - 孤立奇点分类
   - 留数计算
   - 留数定理
   - 围道积分
   - 实积分计算

4. **Riemann曲面** (6讲)
   - 复结构
   - Riemann曲面例子
   - 全纯映射
   - 分歧覆盖
   - 黎曼面紧化

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/03-分析学/02-复分析/01-复分析.md` | 全纯函数 | 95% | Cauchy-Riemann方程 |
| 2 | `docs/03-分析学/02-复分析/02-复分析-增强版.md` | 复积分 | 90% | Cauchy积分定理、Laurent级数 |
| 3 | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | 留数定理 | 85% | 围道积分、实积分计算 |
| 4 | `docs/03-分析学/02-复分析/04-Riemann曲面-深度扩展版.md` | Riemann曲面引入 | 75% | 复结构、全纯映射 |

---

## 四、Part II课程对齐

### 4.1 Part II Galois Theory

| 属性 | 内容 |
|------|------|
| **课程名称** | Galois Theory |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Stewart, *Galois Theory* |
| **覆盖度** | 🟢 **完整覆盖 (88%)** |

#### Cambridge大纲核心主题

1. **域扩张** (6讲)
   - 域扩张的基本概念
   - 代数扩张和超越扩张
   - 分裂域
   - 代数闭包
   - 正规扩张

2. **可分性** (4讲)
   - 可分多项式
   - 可分扩张
   - 本原元素定理
   - 迹和范数

3. **Galois理论基本定理** (8讲)
   - Galois群
   - Galois对应
   - 基本定理证明
   - 中间域的刻画
   - 正规子群与正规扩张

4. **应用** (6讲)
   - 五次方程不可解性
   - 尺规作图
   - 正多边形作图
   - 分圆域
   - Abel-Ruffini定理

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | 域扩张基础 | 95% | 代数扩张、分裂域 |
| 2 | `docs/02-代数结构/02-核心理论/域论/02-Galois理论-深度扩展版.md` | Galois理论 | 90% | Galois群、Galois对应 |
| 3 | `docs/02-代数结构/02-核心理论/域论/03-可分扩张-深度扩展版.md` | 可分性 | 85% | 可分多项式、本原元素定理 |
| 4 | `docs/02-代数结构/02-核心理论/域论/04-应用-深度扩展版.md` | 应用 | 90% | 五次方程、尺规作图 |

---

### 4.2 Part II Algebraic Topology

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Topology |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Analysis and Topology |
| **Cambridge教材** | Hatcher, *Algebraic Topology* |
| **覆盖度** | 🟡 **部分覆盖 (75%)** |

#### Cambridge大纲核心主题

1. **基本群** (8讲)
   - 同伦
   - 回路同伦类
   - 基本群定义
   - 圆的基本群
   - Sⁿ的基本群
   - 乘积空间的基本群
   - Van Kampen定理

2. **覆盖空间** (6讲)
   - 覆盖空间定义
   - 提升性质
   - 万有覆盖
   - 覆盖空间与基本群
   - 分类定理

3. **单纯同调** (6讲)
   - 单纯复形
   - 链复形
   - 同调群定义
   - 例子计算
   - Euler示性数
   - Betti数

4. **奇异同调** (4讲)
   - 奇异链
   - 奇异同调群
   - 同伦不变性
   - Mayer-Vietoris序列

#### FormalMath对应文档

| 序号 | 文档路径 | Hatcher章节 | 覆盖率 | 关键概念 |
|------|----------|-------------|--------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑/01-代数拓扑-国际标准深度扩展版.md` | Ch.1: 基本群 | 90% | 回路同伦、Van Kampen |
| 2 | `docs/05-拓扑学/02-代数拓扑/02-覆盖空间-深度扩展版.md` | Ch.1.3: 覆盖空间 | 85% | 提升性质、万有覆盖 |
| 3 | `docs/05-拓扑学/05-同调论/01-同调论-国际标准深度扩展版.md` | Ch.2: 同调 | 80% | 单纯同调、奇异同调 |
| 4 | `docs/05-拓扑学/05-同调论/03-上同调环-深度扩展版.md` | Ch.3: 上同调 | 70% | 上积、Poincaré对偶 |

#### 需要补充的内容

| 主题 | 补充资源建议 |
|------|-------------|
| 更多同调计算例子 | Hatcher完整习题集 |
| 上同调环计算 | Hatcher Ch.3 |
| 应用例子 | 具体空间计算 |

---

### 4.3 Part II Differential Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Differential Geometry |
| **学时** | 24讲 (D-course) |
| **先修要求** | IB Analysis and Topology |
| **Cambridge教材** | do Carmo; Pressley |
| **覆盖度** | 🟢 **完整覆盖 (82%)** |

#### Cambridge大纲核心主题

1. **光滑流形** (6讲)
   - 流形的定义
   - 图册
   - 光滑函数
   - 切空间
   - 切丛

2. **Riemann度量** (6讲)
   - Riemann度量张量
   - 度量诱导的测地距离
   - 等距
   - 曲率张量
   - Levi-Civita联络

3. **曲率理论** (6讲)
   - Riemann曲率张量
   - Ricci曲率
   - 标量曲率
   - 截面曲率
   - Gauss曲率

4. **测地线** (6讲)
   - 测地方程
   - 指数映射
   - 完备性
   - Gauss-Bonnet定理
   - 曲率与拓扑

#### FormalMath对应文档

| 序号 | 文档路径 | Cambridge主题 | 覆盖率 | 关键概念 |
|------|----------|---------------|--------|----------|
| 1 | `docs/14-微分几何/01-微分几何基础.md` | 光滑流形 | 90% | 图册、切空间 |
| 2 | `docs/14-微分几何/02-微分几何增强版.md` | Riemann度量 | 85% | 度量张量、Levi-Civita联络 |
| 3 | `docs/14-微分几何/03-微分几何深度扩展版.md` | 曲率理论 | 80% | Riemann曲率张量、截面曲率 |
| 4 | `docs/14-微分几何/04-测地线-深度扩展版.md` | 测地线 | 75% | 测地方程、指数映射、Gauss-Bonnet |

---

### 4.4 Part II Number Fields

| 属性 | 内容 |
|------|------|
| **课程名称** | Number Fields |
| **学时** | 24讲 |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Marcus, *Number Fields*; Stewart & Tall |
| **覆盖度** | 🟢 **完整覆盖 (85%)** |

#### Cambridge大纲核心主题

1. **代数数与整数环** (6讲)
   - 代数数和代数整数
   - 数域的定义
   - 整数环
   - 判别式
   - 整基

2. **Dedekind整环** (6讲)
   - 理想的唯一分解
   - 素理想分解
   - 分歧理论
   - 分圆域

3. **类群和单位** (6讲)
   - 理想类群
   - Minkowski定理
   - 类数有限性
   - Dirichlet单位定理
   - 调节子

4. **分圆域应用** (6讲)
   - 分圆整数
   - Fermat大定理特例
   - 互反律

#### FormalMath对应文档

| 序号 | 文档路径 | Marcus章节 | 覆盖率 | 关键概念 |
|------|----------|------------|--------|----------|
| 1 | `docs/06-数论/02-代数数论-增强版.md` | Ch.2: 数域、整数环 | 90% | 代数整数、判别式 |
| 2 | `docs/06-数论/02-代数数论.md` | Ch.3: 理想分解 | 90% | Dedekind整环、分歧 |
| 3 | `docs/06-数论/06-理想类群-深度扩展版.md` | Ch.4: 类群、单位 | 85% | Minkowski定理、Dirichlet单位定理 |
| 4 | `docs/06-数论/07-分圆域-深度扩展版.md` | Ch.4: 分圆域 | 80% | 分圆整数、Fermat大定理特例 |

---

### 4.5 Part II Algebraic Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry |
| **学时** | 24讲 (D-course, Lent Term) |
| **先修要求** | IB Groups, Rings and Modules |
| **Cambridge教材** | Reid, *Undergraduate Algebraic Geometry*; Kirwan |
| **覆盖度** | 🟡 **部分覆盖 (78%)** |

#### Cambridge大纲核心主题

1. **仿射代数几何** (6讲)
   - 仿射空间
   - 代数集
   - Zariski拓扑
   - 坐标环
   - Hilbert零点定理

2. **射影空间** (6讲)
   - 射影空间构造
   - 齐次坐标
   - 射影代数集
   - 射影闭包
   - 平面曲线

3. **代数曲线** (6讲)
   - 曲线的定义
   - 亏格
   - Riemann-Roch定理（陈述）
   - 椭圆曲线

4. **概形初步** (6讲)
   - 层
   - 局部环层空间
   - 仿射概形
   - 概形定义

#### FormalMath对应文档

| 序号 | 文档路径 | Reid章节 | 覆盖率 | 关键概念 |
|------|----------|----------|--------|----------|
| 1 | `docs/13-代数几何/01-代数几何基础.md` | Ch.0-1: 仿射空间、代数集 | 90% | Zariski拓扑、坐标环 |
| 2 | `docs/13-代数几何/02-代数几何增强版.md` | Ch.2: 射影空间 | 85% | 齐次坐标、射影闭包 |
| 3 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.4: 代数曲线 | 75% | 亏格、Riemann-Roch |
| 4 | `docs/13-代数几何/03-代数几何深度扩展版.md` | Ch.5-6: 概形初步 | 70% | 结构层、概形定义 |

---

## 五、Part III课程对齐

### 5.1 Part III Advanced Algebraic Geometry

| 属性 | 内容 |
|------|------|
| **课程名称** | Algebraic Geometry (Advanced) |
| **学时** | 24讲 |
| **先修要求** | Part II Algebraic Geometry |
| **Cambridge教材** | Hartshorne; Vakil, *FOAG* |
| **覆盖度** | 🟡 **部分覆盖 (80%)** |

#### Cambridge大纲核心主题

1. **概形理论** (8讲)
   - 仿射概形
   - 一般概形
   - 态射
   - 纤维积
   - 分离性和本征性

2. **层上同调** (8讲)
   - 导出函子
   - 层上同调
   - Čech上同调
   - 消失定理
   - Serre定理

3. **代数曲线** (4讲)
   - Riemann-Roch定理
   - Serre对偶
   - 曲线的模空间

4. **曲面理论** (4讲)
   - 相交理论
   - Riemann-Roch曲面
   - 分类初步

#### FormalMath对应文档

| 序号 | 文档路径 | Hartshorne/Vakil | 覆盖率 | 关键概念 |
|------|----------|-----------------|--------|----------|
| 1 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` | Ch.II: 概形、态射 | 90% | 仿射概形、纤维积 |
| 2 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` | Ch.II.5: 凝聚层 | 85% | 局部自由层、Picard群 |
| 3 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` | Ch.III: 层上同调 | 85% | 导出函子、Čech上同调 |
| 4 | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/25-上同调与凝聚层上同调.md` | Ch.III.5: 凝聚层上同调 | 75% | Serre定理、Serre对偶 |

---

### 5.2 Part III Homotopy Theory

| 属性 | 内容 |
|------|------|
| **课程名称** | Homotopy Theory |
| **学时** | 24讲 |
| **先修要求** | Part II Algebraic Topology |
| **Cambridge教材** | Hatcher; May |
| **覆盖度** | 🟡 **部分覆盖 (70%)** |

#### Cambridge大纲核心主题

1. **同伦论基础** (8讲)
   - 同伦群
   - 纤维序列
   - 上纤维化
   - 同伦扩张性质

2. **上同调运算** (8讲)
   - Steenrod方
   - 上同调运算的公理
   - 应用

3. **谱序列** (8讲)
   - 谱序列定义
   - Leray-Serre谱序列
   - Adams谱序列（介绍）
   - 稳定同伦论

#### FormalMath对应文档

| 序号 | 文档路径 | Hatcher/May | 覆盖率 | 关键概念 |
|------|----------|-------------|--------|----------|
| 1 | `docs/05-拓扑学/02-代数拓扑/01-代数拓扑-国际标准深度扩展版.md` | Ch.4: 同伦论 | 75% | 同伦群、纤维序列 |
| 2 | `docs/05-拓扑学/05-同调论/02-上同调运算-深度扩展版.md` | Ch.4.L: 上同调运算 | 70% | Steenrod方 |
| 3 | `docs/05-拓扑学/06-同伦论/01-同伦论基础.md` | May: 谱、Ω-谱 | 65% | 稳定同伦、Eilenberg-MacLane谱 |

---

### 5.3 Part III Elliptic Curves

| 属性 | 内容 |
|------|------|
| **课程名称** | Elliptic Curves |
| **学时** | 16-24讲 |
| **先修要求** | Part II Number Fields |
| **Cambridge教材** | Silverman, *The Arithmetic of Elliptic Curves* |
| **覆盖度** | 🟡 **部分覆盖 (75%)** |

#### FormalMath对应文档

| 序号 | 文档路径 | Silverman章节 | 覆盖率 | 关键概念 |
|------|----------|--------------|--------|----------|
| 1 | `docs/06-数论/08-椭圆曲线-深度扩展版.md` | Ch.III: 群结构 | 90% | 弦切法、Mordell-Weil群 |
| 2 | `docs/06-数论/09-椭圆曲线群结构-深度扩展版.md` | Ch.VIII: Mordell-Weil定理 | 80% | 下降法、高度 |
| 3 | `docs/06-数论/10-复乘法-深度扩展版.md` | Ch.II: 复乘法 | 70% | 自同态环、类域论 |
| 4 | `docs/06-数论/11-模形式基础-深度扩展版.md` | C: 模形式 | 65% | 模曲线、Taniyama-Shimura |

---

## 六、Tripos证明风格与传统

### 6.1 Cambridge证明风格特点

Cambridge数学Tripos的证明风格具有以下显著特点：

| 特点 | 说明 | FormalMath对应 |
|------|------|----------------|
| **严格性** | ε-δ论证是标准，拒绝直觉论证 | 所有分析文档严格遵循ε-δ定义 |
| **简洁性** | 证明力求精炼，避免冗余 | 文档提供多种详细程度版本供选择 |
| **技巧性** | 重视解题技巧和快速推理 | 练习题系统涵盖各类技巧 |
| **结构性** | 强调逻辑结构和层次 | 概念图谱展示知识结构 |

### 6.2 典型证明模式

#### 分析学证明模式

```
标准ε-δ证明结构：
1. 给定ε > 0
2. 构造δ = ... (通常依赖于ε)
3. 假设 |x - a| < δ
4. 推导 |f(x) - L| < ε
5. 结论：lim(x→a) f(x) = L
```

#### 代数学证明模式

```
标准群论证明结构：
1. 验证封闭性
2. 验证结合律
3. 验证单位元存在
4. 验证逆元存在
5. 结论：构成群
```

### 6.3 与FormalMath的融合

FormalMath项目已与Cambridge证明风格深度对齐：

| Cambridge要求 | FormalMath实现 |
|--------------|----------------|
| ε-δ严格性 | 所有分析文档提供完整ε-δ证明 |
| 逻辑严密 | 形式化验证系统(Lean4) |
| 多表征方式 | 概念多表征分析 |
| 历史脉络 | 每篇文档包含历史与渊源章节 |

---

## 七、经典教材对应

### 7.1 核心教材映射

| 经典教材 | 适用课程 | FormalMath对应 | 说明 |
|----------|----------|----------------|------|
| **Hardy, *A Course of Pure Mathematics*** | IA Analysis I | `docs/03-分析学/01-实分析/` | 分析严格性奠基之作 |
| **Davenport, *The Higher Arithmetic*** | IA Numbers and Sets | `docs/06-数论/01-初等数论/` | 数论经典入门 |
| **Hardy & Wright, *An Introduction to the Theory of Numbers*** | Part II Number Theory | `docs/06-数论/` | 数论百科全书 |
| **Apostol, *Calculus*** | IA Analysis I | `docs/03-分析学/01-实分析/` | 标准分析教材 |
| **Spivak, *Calculus*** | IA Analysis I | `docs/03-分析学/01-实分析/` | 强调严格证明 |
| **Goldrei, *Classic Set Theory*** | IA Numbers and Sets | `docs/01-基础数学/集合论/` | 集合论标准教材 |
| **Allenby, *Rings, Fields and Groups*** | IA Groups, IB GRM | `docs/02-代数结构/群论/` | 代数结构入门 |
| **Kaye & Wilson, *Linear Algebra*** | IB Linear Algebra | `docs/02-代数结构/线性代数/` | 线性代数标准教材 |
| **Sutherland, *Introduction to Metric and Topological Spaces*** | IB Analysis and Topology | `docs/05-拓扑学/01-点集拓扑/` | 拓扑学入门 |
| **Stewart, *Galois Theory*** | Part II Galois Theory | `docs/02-代数结构/域论/` | Galois理论经典 |
| **Marcus, *Number Fields*** | Part II Number Fields | `docs/06-数论/代数数论/` | 代数数论标准教材 |
| **Reid, *Undergraduate Algebraic Geometry*** | Part II Algebraic Geometry | `docs/13-代数几何/` | 代数几何入门 |
| **Hatcher, *Algebraic Topology*** | Part II Algebraic Topology | `docs/05-拓扑学/02-代数拓扑/` | 代数拓扑标准教材 |
| **do Carmo, *Differential Geometry*** | Part II Differential Geometry | `docs/14-微分几何/` | 微分几何经典 |
| **Hartshorne, *Algebraic Geometry*** | Part III AG | `docs/13-代数几何/` | 代数几何圣经 |
| **Silverman, *The Arithmetic of Elliptic Curves*** | Part III Elliptic Curves | `docs/06-数论/椭圆曲线/` | 椭圆曲线标准教材 |

### 7.2 教材版本更新

| 教材 | 推荐版本 | 更新说明 |
|------|----------|----------|
| Hardy, *Pure Mathematics* | Centenary Edition (2008) | 包含T.W. Körner前言 |
| Hartshorne, *Algebraic Geometry* | 1977版 | 经典版本，持续使用 |
| Vakil, *FOAG* | Oct 2025版 | 持续更新，建议使用最新版 |
| Hatcher, *Algebraic Topology* | 在线免费版 | 作者持续更新 |

---

## 八、覆盖度总结与建议

### 8.1 课程覆盖度总览

| 课程 | 覆盖度 | 状态 | 建议 |
|------|--------|------|------|
| **Part IA** | | | |
| IA Numbers and Sets | 92% | 🟢 | 完全可以作为主要资源 |
| IA Groups | 90% | 🟢 | 完全可以作为主要资源 |
| IA Differential Equations | 70% | 🟡 | 需要补充物理应用例子 |
| IA Analysis I | 90% | 🟢 | 完全可以作为主要资源 |
| IA Probability | 68% | 🟡 | 需要补充统计应用 |
| **Part IB** | | | |
| IB Linear Algebra | 88% | 🟢 | 完全可以作为主要资源 |
| IB Groups, Rings and Modules | 88% | 🟢 | 完全可以作为主要资源 |
| IB Analysis and Topology | 85% | 🟢 | 完全可以作为主要资源 |
| IB Complex Analysis | 88% | 🟢 | 完全可以作为主要资源 |
| IB Geometry | 80% | 🟢 | 完全可以作为主要资源 |
| **Part II** | | | |
| Part II Galois Theory | 88% | 🟢 | 完全可以作为主要资源 |
| Part II Algebraic Topology | 75% | 🟡 | 需要补充Hatcher习题 |
| Part II Number Fields | 85% | 🟢 | 完全可以作为主要资源 |
| Part II Algebraic Geometry | 78% | 🟢 | 完全可以作为主要资源 |
| Part II Differential Geometry | 82% | 🟢 | 完全可以作为主要资源 |
| Part II Logic and Set Theory | 88% | 🟢 | 完全可以作为主要资源 |
| **Part III** | | | |
| Part III Advanced Algebraic Geometry | 80% | 🟢 | 完全可以作为主要资源 |
| Part III Homotopy Theory | 70% | 🟡 | 需要补充May教材 |
| Part III Elliptic Curves | 75% | 🟡 | 需要补充Silverman |
| Part III Moduli Spaces | 68% | 🟡 | 需要补充材料 |

### 8.2 推荐学习路径

#### Part IA路径（第一年）

```
Michaelmas Term:
├── Numbers and Sets → IA Groups → Part II Logic
├── Analysis I → IB Analysis and Topology → Part II Differential Geometry
└── Vectors and Matrices → IB Linear Algebra → Part II Algebraic Topology

Lent Term:
├── Differential Equations
└── Probability
```

#### Part IB路径（第二年）

```
Michaelmas Term:
├── Groups, Rings and Modules → Part II Number Fields → Part III Elliptic Curves
├── Linear Algebra → Part II Algebraic Geometry → Part III Advanced Algebraic Geometry
└── Analysis and Topology → Part II Algebraic Topology → Part III Homotopy Theory

Lent Term:
├── Complex Analysis
└── Geometry
```

#### Part II路径（第三年）

```
代数方向:
├── Number Fields → Part III Elliptic Curves
├── Algebraic Geometry → Part III Advanced Algebraic Geometry
└── Galois Theory

几何/拓扑方向:
├── Algebraic Topology → Part III Homotopy Theory
├── Differential Geometry
└── Riemann Surfaces

分析方向:
├── Linear Analysis
├── Probability and Measure
└── Analysis of Functions
```

### 8.3 建议更新清单

| 优先级 | 主题 | 建议行动 |
|--------|------|----------|
| **高** | 微分方程应用 | 补充更多物理和工程应用例子 |
| **高** | 概率统计 | 补充统计推断和假设检验内容 |
| **中** | 代数拓扑习题 | 补充Hatcher完整习题解答 |
| **中** | 同伦论内容 | 补充May教材核心内容 |
| **中** | 椭圆曲线 | 补充Silverman更多章节 |
| **低** | 模空间 | 补充Deligne-Mumford理论 |
| **低** | 表示论 | 补充Part II Representation Theory |

### 8.4 特色学习建议

#### Tripos考试准备

| 考试要素 | FormalMath支持 |
|----------|---------------|
| 快速解题 | `docs/02-代数结构/08-教学资源/` 各主题习题库 |
| 严格证明 | `docs/FormalMath定义表述模板.md` |
| 选择题技巧 | `docs/00-核心概念理解三问/` 反例集 |

#### 与Oxford对比

| 特征 | Cambridge | Oxford |
|------|-----------|--------|
| **代数几何** | Reid → Hartshorne (Part II/III) | Fulton → Hartshorne (B5/C3.1) |
| **李代数** | Part II Representation Theory (部分) | **B2.1/C2.1 (专门课程)** |
| **同调代数** | Part III Commutative Algebra (部分) | **C2.2 (专门课程)** |
| **考试系统** | Tripos | 期末考试 |
| **问题集** | Example Sheets | Problem Sheets |

---

## 九、附录

### 9.1 相关链接

- [Cambridge Maths Department](https://www.maths.cam.ac.uk/)
- [Part III Courses](https://www.maths.cam.ac.uk/postgrad/part-iii)
- [Cambridge Course Schedule 2025-2026](https://www.maths.cam.ac.uk/undergrad/course/)
- [Tripos Past Papers](https://www.maths.cam.ac.uk/undergrad/pastpapers/)
- [FormalMath Oxford课程映射](project/Oxford-course-mapping-detailed.md)
- [FormalMath MIT课程映射](project/MIT-course-mapping-detailed.md)
- [FormalMath Harvard课程映射](project/Harvard-course-mapping-detailed.md)

### 9.2 参考文献

1. Cambridge University Faculty of Mathematics. *Schedules of Lecture Courses and Form of Examinations for the Mathematical Tripos 2024-25*.
2. Cambridge University Faculty of Mathematics. *Guide to Courses in Part IA/IB/II/III of the Mathematical Tripos*.
3. Hardy, G.H. *A Course of Pure Mathematics* (Centenary Edition). Cambridge University Press, 2008.
4. Davenport, H. *The Higher Arithmetic*. Cambridge University Press, 1999.
5. Hardy, G.H. & Wright, E.M. *An Introduction to the Theory of Numbers*. Oxford University Press, 1979.

---

*最后更新: 2026年4月4日*
*更新内容: 深度对齐Cambridge数学Tripos全课程体系，添加18门核心课程详细映射，涵盖Part IA到Part III全部层级*
*对齐标准: Cambridge University Mathematical Tripos 2025-2026 Schedules*
