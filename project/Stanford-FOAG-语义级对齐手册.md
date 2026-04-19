---
msc_primary: 14
msc_secondary:
  - 14-01
title: Stanford FOAG (Foundations of Algebraic Geometry) 语义级对齐手册
course_code: Stanford Math 216
course_name: Foundations of Algebraic Geometry
instructor: Ravi Vakil
version: FOAG Oct 2025
processed_at: '2026-04-09'
---

# Stanford FOAG 语义级对齐手册

**课程代码**: Stanford Math 216
**课程名称**: Foundations of Algebraic Geometry
**授课教师**: Ravi Vakil
**教材版本**: FOAG October 2025 (v2.0)
**项目对应**: 格洛腾迪克数学理念/02-概形理论
**对齐等级**: L3-L6
**文档版本**: v1.0

---

## 课程概览

### 课程描述

FOAG是Stanford数学系研究生代数几何核心课程，采用Ravi Vakil的同名教材。课程强调几何直观与形式理论并重，从范畴论基础出发，系统构建概形理论，最终达到层上同调与上同调技巧的应用水平。

### 课程特色

| 特色 | 说明 |
|------|------|
| 范畴论基础 | 从极限、伴随函子等范畴论概念出发 |
| 几何直观 | 强调几何图景，避免过度形式化 |
| 练习丰富 | 大量Starred exercises（挑战性习题） |
| 现代视角 | 导出范畴、栈等现代工具 |

### 核心教材

**Foundations of Algebraic Geometry**

- 作者: Ravi Vakil
- 版本: October 2025 (更新自Feb/Jul 2024)
- 页数: ~800页
- 获取: https://math.stanford.edu/~vakil/216blog/FOAGoct2125public.pdf

### 先修要求

- 交换代数（Atiyah-Macdonald水平）
- 同调代数基础
- 点集拓扑与基础代数拓扑
- 复分析（有助于几何直觉）

---

## FOAG结构与FormalMath对应

### Part I: Preliminaries（预备知识）

#### Chapter 1: Category Theory（范畴论）

**FOAG内容**:

- 范畴、函子、自然变换
- 极限与余极限
- 伴随函子
- Abel范畴

**FormalMath对应**:

- `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md`
- `docs/15-同调代数/同调代数基础.md` (Abel范畴)

**Stacks Project Tags**:

- 0017: 范畴定义
- 0032: 极限
- 0036: 伴随函子

#### Chapter 2: Sheaves（层）

**FOAG内容**:

- 预层与层
- 茎与芽
- 层的态射
- 层的 pushforward/pullback

**FormalMath对应**:

- `docs/13-代数几何/03-上同调理论/01-层上同调基础.md`

**关键概念**:

```
层 (Sheaf)
├─ 定义: 满足胶合公理的预层
├─ 茎 (Stalk): F_x = colim_{U∋x} F(U)
└─ 芽 (Germ): 茎中的元素
```

---

### Part II: Schemes（概形）

#### Chapter 3: Toward Affine Schemes（迈向仿射概形）

**FOAG内容**:

- 环的谱 Spec R
- Zariski拓扑
- 结构层结构

**FormalMath对应**:

- `docs/13-代数几何/概形理论-深度版.md`
- `docs/02-代数结构/交换代数/素谱.md`

**Stacks Project Tags**:

- **00E0**: 环的谱的性质（最常用标签）
- 00E1: 素理想
- 00E2: 极大理想

#### Chapter 4: The Structure Sheaf（结构层）

**FOAG内容**:

- 结构层 O_Spec R 的构造
- 局部化与茎
- 仿射概形的定义

**关键定理**:
> **定理**: 对仿射概形 X = Spec R，有 O_X(X) = R，且对任意 p ∈ Spec R，茎 O_{X,p} = R_p

#### Chapter 5: Properties of Schemes（概形的性质）

**FOAG内容**:

- 连通、不可约
- 约化、整
- Noetherian概形
- 维数

**FormalMath对应**:

- `docs/13-代数几何/02-概形理论/00-概形理论-概念总览.md`

**Stacks Project Tags**:

- **00KD**: Krull维数
- 00DT: Noetherian拓扑空间

#### Chapter 6: Morphisms of Schemes（概形态射）

**FOAG内容**:

- 态射的定义
- 局部有限型、有限型
- 仿射态射、有限态射
- 分离态射、固有态射

**关键概念对比**:

| 性质 | 定义要点 | 几何意义 |
|------|----------|----------|
| **分离** | 对角线闭嵌入 | Hausdorff类比 |
| **固有** | 泛闭+分离+有限型 | 紧致类比 |
| **仿射** | 原像仿射 | 纤维丛类比 |
| **有限** | 仿射+模有限 | 覆叠类比 |

---

### Part III: Morphisms（态射的深入性质）

#### Chapter 7: Useful Classes of Morphisms（有用的态射类）

**FOAG内容**:

- 开浸入、闭浸入
- 局部闭浸入
- 有效Cartier除子

#### Chapter 8: Closed Embeddings and Related Notions（闭嵌入与相关概念）

**FOAG内容**:

- 闭嵌入的函子刻画
- 理想层
- 正规层与余法层

#### Chapter 9: Fibered Product of Schemes（概形纤维积）

**FOAG内容**:

- 纤维积的存在性
- 纤维积的直观
- 基变换

**关键直觉**:

```
X ×_Z Y 的直观:
┌─────────────────────────┐
│  "X与Y在Z上相交的方式"    │
│                         │
│  几何: 纤维的乘积        │
│  代数: 张量积            │
└─────────────────────────┘
```

#### Chapter 10: Separated and Proper Morphisms（分离与固有态射）

**FOAG内容**:

- 分离态射（ valuative criterion）
- 固有态射
- 射影态射

**FOAG特色**:
> Vakil强调 valuative criterion 的几何直觉："一条曲线趋近于一个点的方式"

---

### Part IV: "Geometric" Properties（"几何"性质）

#### Chapter 11: Dimension（维数）

**FOAG内容**:

- Krull维数
- 余维数
- 平坦性

**Stacks Project Tags**:

- **00KD**: Krull维数
- 00KJ: 高度

#### Chapter 12: Regularity and Smoothness（正则性与光滑性）

**FOAG内容**:

- 正则局部环
- 光滑态射
- 平展态射

**关键对比**:

| 概念 | 代数定义 | 几何意义 |
|------|----------|----------|
| **正则** | 维数=嵌入维数 | 无奇点 |
| **光滑** | 形式平展+局部有限展示 | 微分几何中的光滑 |
| **平展** | 光滑+相对维数0 | 局部同构 |

---

### Part V: Quasicoherent Sheaves（拟凝聚层）

#### Chapter 13: Quasicoherent and Coherent Sheaves（拟凝聚与凝聚层）

**FOAG内容**:

- 拟凝聚层的定义
- 仿射情形：模对应
- 凝聚层

**FormalMath对应**:

- `docs/13-代数几何/03-上同调理论/25-凝聚层上同调.md`

**Stacks Project Tags**:

- **01LC**: 拟凝聚层定义
- 01NT: 凝聚层

**关键定理**:
> **定理**: 在仿射概形 Spec R 上，拟凝聚层范畴等价于 R-模范畴

#### Chapter 14: Line Bundles: Invertible Sheaves and Divisors（线丛：可逆层与除子）

**FOAG内容**:

- 可逆层（线丛）
- Weil除子与Cartier除子
- 线丛与射影嵌入

---

### Part VI: More（更多内容）

#### Chapter 17: Cohomology of Quasicoherent Sheaves（拟凝聚层上同调）

**FOAG内容**:

- 导出函子定义
- Čech上同调
- 仿射概形的消失定理

**FormalMath对应**:

- `docs/13-代数几何/03-上同调理论/01-层上同调基础.md`

**Stacks Project Tags**:

- **01DZ**: Čech上同调等价性（⭐核心）
- **01X8**: 仿射概形上同调
- **01XI**: 仿射对角线消失

**关键定理**:
> **Serre消失定理**: 设 X 为射影概形，O(1) 为极丰富线丛，F 为凝聚层。则对足够大的 n，有 H^i(X, F(n)) = 0（i > 0）

#### Chapter 18: Cohomology of Projective Schemes（射影概形的上同调）

**FOAG内容**:

- 射影空间的上同调计算
- 上同调与Hilbert多项式
- Riemann-Roch定理（曲线情形）

**Stacks Project Tags**:

- **02O3**: 射影空间上同调计算
- **01YG**: Serre消失定理

---

## FOAG vs FormalMath 深度对比

### 内容对齐表

| FOAG章节 | FormalMath覆盖 | 差距分析 |
|----------|----------------|----------|
| Ch 1-2 范畴论与层 | ✅ 良好 | 需补充更多例子 |
| Ch 3-6 概形基础 | ✅ 良好 | 定义等价 |
| Ch 7-10 态射性质 | ⚠️ 部分 | 需补充 valuative criterion |
| Ch 11-12 维数与光滑性 | ⚠️ 部分 | 需补充平展态射 |
| Ch 13-14 拟凝聚层 | ✅ 良好 | 需更新层对应定理证明 |
| Ch 17-18 上同调 | 🔄 进行中 | 需对齐Stacks Tags |
| Ch 19+ 高级主题 | ❌ 缺失 | 需要新建 |

### 特色内容对比

| 特色 | FOAG | FormalMath现状 | 建议 |
|------|------|----------------|------|
| **Starred Exercises** | 大量挑战性习题 | 少量 | 需系统建设 |
| **几何直觉** | 强调直观解释 | 偏重形式 | 补充直观说明 |
| **图示** | 大量手绘图 | 缺少 | 增加图示 |
| **例子密度** | 丰富 | 中等 | 增加典型例子 |

---

## 六级对齐验证

### L1-L2: 结构对齐 ✅

| FOAG Part | FormalMath对应 | 状态 |
|-----------|----------------|------|
| Part I 预备 | 范畴论、层论 | ✅ |
| Part II 概形 | 概形理论 | ✅ |
| Part III 态射 | 态射性质 | ✅ |
| Part IV 几何性质 | 维数、光滑性 | ✅ |
| Part V 层 | 凝聚层 | ✅ |
| Part VI 上同调 | 上同调理论 | ✅ |

### L3: 定义对齐 🔄

| 概念 | FOAG定义 | FormalMath | 等价性 |
|------|----------|------------|--------|
| 概形 | 局部环化空间+局部仿射 | 同 | ✅ |
| 拟凝聚层 | 局部可表为模的层 | 同 | ✅ |
| 分离态射 | 对角线闭嵌入 | 同 | ✅ |
| 固有态射 | 泛闭+分离+有限型 | 同 | ✅ |

### L4: 定理对齐 ⏳

| 定理 | FOAG | FormalMath | 状态 |
|------|------|------------|------|
| 仿射层对应 | Ch 13 | 有待完善 | ⏳ |
| Serre消失 | Ch 17 | 有，需补充证明 | ⏳ |
| 上同调计算 | Ch 18 | 部分 | ⏳ |

### L5: 习题对齐 📋

**FOAG特点**: 大量Starred Exercises（难度高）

| 类型 | FOAG数量 | FormalMath目标 | 当前状态 |
|------|----------|----------------|----------|
| 常规习题 | ~300 | 配套解答 | 📋 |
| Starred | ~100 | 详细解答+思路 | 📋 |

### L6: 思想方法 📋

**FOAG强调的思想方法**:

1. **范畴论思维**: 泛性质优先于构造
2. **几何直觉**: 代数对应几何图景
3. **技术工具**: 上同调作为计算工具
4. **现代视角**: 导出范畴、导出代数几何

---

## 学习路径建议

### 使用FOAG+FormalMath的组合学习

```
预备阶段
├─ 阅读 FormalMath 范畴论基础
├─ 阅读 FormalMath 交换代数
└─ 参考 Stacks Project Tag 00E0, 00DV

概形入门
├─ 阅读 FOAG Part II
├─ 参考 FormalMath 概形理论
└─ 完成配套习题

态射深入
├─ 阅读 FOAG Part III
├─ 参考 Stacks Project 相关Tags
└─ 练习 valuative criterion

上同调应用
├─ 阅读 FOAG Part VI
├─ 参考 FormalMath 上同调理论
└─ 完成 Stacks Tag 01DZ 解读
```

---

## 下一步行动计划

### Round 35-36

| 优先级 | 任务 | 目标 |
|--------|------|------|
| P0 | FOAG前18章习题映射 | 建立对应关系表 |
| P0 | 核心定理证明补充 | 仿射层对应、Serre消失 |
| P1 | Starred Exercises精选 | 20道难题详细解答 |

### Round 37-40

- 完成FOAG全书的L3-L4对齐
- 建立与Kerodon的内容对应
- 启动相关内容的Lean4形式化

---

**对齐负责人**: [待指定]
**最后更新**: 2026年4月9日
