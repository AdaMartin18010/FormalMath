---
title: Stanford FOAG 对齐深化执行计划
task_id: P2-Stanford-FOAG- deepen
course_code: Stanford FOAG
course_name: Foundations of Algebraic Geometry
level: silver
target_courses:
  - Stanford FOAG
version: v1.0
date_created: '2026-04-17'
---

# Stanford FOAG 对齐深化执行计划

> **任务编号**：P2-Stanford-FOAG
> **课程代码**：Stanford FOAG / Math 216A/B/C
> **课程名称**：Foundations of Algebraic Geometry（Ravi Vakil）
> **对齐等级**：Silver（银层标准：完整证明 + 几何直觉 + 习题解答 + Lean4 引用）

---

## 1. 现状审计

### 1.1 现有文档覆盖

| 区域 | 现有 AG-VK 文档 | 状态 |
|------|----------------|------|
| Part I (Ch 1–2) | AG-VK-002 (层的基本运算), AG-VK-005 (可表函子) | 🟡 层化定理与 stalk 正合性缺失 |
| Part II (Ch 3–6) | AG-VK-001 (概形泛性质), AG-VK-003 (分离/真态射), AG-VK-004 (Proj) | 🟡 结构层构造、Proj 泛性质证明薄弱 |
| Part III (Ch 7–11) | — | 🔴 Valuative Criterion 证明缺失 |
| Part V (Ch 18) | AG-VK-007 (导出函子), AG-VK-008 (消失定理) | 🟡 Čech-导出等价深层证明不足 |
| Part VI (Ch 23–29) | — | 🔴 平坦性、基变化、Serre 对偶证明极度稀缺 |

### 1.2 P1-T3 识别出的关键薄弱点

1. **stalk 的泛化定义缺失**：`D020-stanford-foag-definition-alignment.md` 指出项目文档完全缺失 stalk 的一般定义。
2. **结构层构造细节待补**：仿射概形 `Spec A` 上结构层 `O_X` 的显式构造与泛性质证明不完整。
3. **Proj 细节待补**：分次环 `Proj S` 的构造、泛性质及到 `P^n` 的映射细节不足。
4. **Valuative Criterion 证明缺失**：分离性与本征性的 valuative criterion 仅有陈述，无完整推导。
5. **上同调计算题不足**：Čech 上同调与导出上同调的等价性证明缺乏细节。
6. **Part VI 证明极度稀缺**：Ch 23–29（平坦性、光滑性、上同调与基变化、深度、Serre 对偶）在项目中多为历史/哲学叙述，缺少手写数学证明。

---

## 2. 执行目标

### 2.1 总体目标

为 **5–7 个 FOAG 核心但项目文档薄弱** 的章节撰写 **Silver 级** 深化文档，使 FOAG L4（定理证明）从 ~50% 提升到 ≥80%，L5（习题解答）从 15/30 主题提升到 22/30 主题以上。

### 2.2 Silver 级标准

每篇深化文档必须满足：

| 要求 | 说明 |
|------|------|
| YAML frontmatter | `level: "silver"`, `target_courses: ["Stanford FOAG"]` |
| 精确章节对应 | 标明 FOAG 章号、关键定义、定理编号 |
| 完整自然语言证明 | 手写数学风格的严格推导，步骤清晰 |
| 几何直觉解释 | 体现 Vakil “几何直觉 + 严格代数” 的特色 |
| ≥2 道 FOAG 习题解答 | 详细解答，标明 FOAG 习题号 |
| Lean4 代码引用 | 引用 `FormalMath-Enhanced/lean4/` 或 `Mathlib4` 中的相关 `.lean` 文件 |

---

## 3. 选定的 7 篇深化文档

| 编号 | 主题 | 对应 FOAG 章节 | 修复的薄弱点 |
|------|------|----------------|-------------|
| **AG-VK-016** | 层的层化与 stalk 判定正合性 | Ch 2 | stalk 泛化定义缺失、层化定理证明缺失 |
| **AG-VK-017** | 仿射概形的结构层与 Spec–Γ 范畴等价 | Ch 3–4 | 结构层构造细节待补 |
| **AG-VK-018** | Proj 构造与其泛性质 | Ch 6 | Proj 细节待补 |
| **AG-VK-019** | 分离与本征态射的 Valuative Criterion | Ch 7–9 | valuative criterion 证明缺失 |
| **AG-VK-020** | 导出函子与 Čech-导出上同调等价性 | Ch 18 | 上同调计算题不足 |
| **AG-VK-021** | 曲线的 Riemann-Roch 定理与计算 | Ch 18–19 | 曲线理论证明深化 |
| **AG-VK-022** | 平坦性、光滑性与上同调基变换 | Ch 23–25 | Part VI 证明极度稀缺 |

---

## 4. 每篇文档的内容规划

### AG-VK-016：层的层化与 stalk 判定正合性

- **核心定理**：Sheafification 定理（Ch 2.4）、Exactness can be checked at stalks（Ch 2.5）
- **几何直觉**：stalk 是“局部显微镜”，层的正合性可以在每一点检验，如同函数的连续性可以逐点检验
- **习题**：
  - Ex 2.4.B：层在基上的恢复
  - Ex 2.5.D：逆像层的泛性质
- **Lean4 引用**：`Mathlib.Topology.Sheaves.Stalks`、`Mathlib.Topology.Sheaves.Sheafify`

### AG-VK-017：仿射概形的结构层与 Spec–Γ 范畴等价

- **核心定理**：结构层 `O_{Spec A}` 是层（Ch 3.2–3.4）、`Spec–Γ` 伴随等价（Ch 3.5–4.1）
- **几何直觉**：`Spec A` 上的结构层把每个开集对应到“在该开集上正则的函数”；范畴等价意味着“几何对象”与“代数对象”可以无损互译
- **习题**：
  - Ex 3.7.E：`Spec A` 的不可约闭子集与素理想一一对应
  - Ex 4.3.B：仿射概形映射的泛性质
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.AffineScheme`、`algebraicGeometry.equivCommRingCatToAffineSchemeCat`

### AG-VK-018：Proj 构造与其泛性质

- **核心定理**：`Proj S` 是概形（Ch 6.3）、`Proj` 的泛性质（Ch 6.4）
- **几何直觉**：`Proj` 是把分次环“proj 化”成紧几何对象的过程；`P^n` 是最简单的例子，对应齐次坐标
- **习题**：
  - Ex 6.3.M：`Proj` 的泛性质
  - Ex 6.4.F：射影空间的坐标环与映射到 `P^n`
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`

### AG-VK-019：分离与本征态射的 Valuative Criterion

- **核心定理**：分离态射的 Valuative Criterion（Ch 7.3）、本征态射的 Valuative Criterion（Ch 8.4）
- **几何直觉**：分离性意味着“极限唯一”，本征性意味着“极限存在且唯一”；DVR 的赋值盘是检验曲线极限的显微镜
- **习题**：
  - Ex 7.3.D：Chevalley 定理的证明
  - Ex 8.4.G：真态射判别的应用
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.Morphisms.Separated`、`Mathlib.AlgebraicGeometry.ValuativeCriterion`

### AG-VK-020：导出函子与 Čech-导出上同调等价性

- **核心定理**：Čech 上同调 = 导出上同调（Ch 18.2）、Leray 定理
- **几何直觉**：Čech 上同调用“开覆盖拼图”计算整体不变量；当每一块及其交集都是上同调平凡时，拼图完美还原整体
- **习题**：
  - Ex 18.2.H：Čech = 导出上同调
  - Ex 18.3.A：Serre 消失定理的证明要点
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.CechCohomology`、`Mathlib.Algebra.Homology.DerivedCategory`

### AG-VK-021：曲线的 Riemann-Roch 定理与计算

- **核心定理**：Riemann-Roch 定理（Ch 18.4）、Serre 对偶在曲线上的形式（Ch 19.2）
- **几何直觉**：Riemann-Roch 是曲线上“自由度 = 次数 + 拓扑修正”的精确公式；亏格 g 是曲面上“洞”的数量
- **习题**：
  - Ex 18.4.A：Riemann-Roch 的曲线情形
  - Ex 19.2.B：椭圆曲线上的显式计算
- **Lean4 引用**：`FormalMath.AlgebraicGeometry` 中的 `riemann_roch` 定理框架

### AG-VK-022：平坦性、光滑性与上同调基变换

- **核心定理**：平坦性的局部判别（Ch 24.5）、上同调与基变化定理（Ch 25.2）、形式光滑性（Ch 25.3）
- **几何直觉**：平坦性保证纤维“连续变化”——在平坦族中，纤维的维数、次数等不变量保持恒定；基变化定理保证上同调在平坦基变换下具有良好的函子性
- **习题**：
  - Ex 24.5.J/K：平坦性的拓扑含义
  - Ex 25.2.E：上同调与基变化的应用
- **Lean4 引用**：`Mathlib.RingTheory.Flat`、`Mathlib.AlgebraicGeometry.Smooth`

---

## 5. 习题解答覆盖统计

本次深化将新增 **14 道 FOAG 习题的详细解答**：

| 文档 | 习题号 |
|------|--------|
| AG-VK-016 | Ex 2.4.B, Ex 2.5.D |
| AG-VK-017 | Ex 3.7.E, Ex 4.3.B |
| AG-VK-018 | Ex 6.3.M, Ex 6.4.F |
| AG-VK-019 | Ex 7.3.D, Ex 8.4.G |
| AG-VK-020 | Ex 18.2.H, Ex 18.3.A |
| AG-VK-021 | Ex 18.4.A, Ex 19.2.B |
| AG-VK-022 | Ex 24.5.J, Ex 25.2.E |

**总计：14 道习题解答**，超出任务要求的“至少 10 道”。

---

## 6. 输出文件清单

```
project/
└── Stanford-FOAG-对齐深化执行计划.md       ← 本计划

docs/13-代数几何/习题/
├── AG-VK-016-层的层化与stalk判定正合性.md   ← 新建
├── AG-VK-017-仿射概形的结构层与Spec-Γ范畴等价.md ← 新建
├── AG-VK-018-Proj构造与其泛性质.md         ← 新建
├── AG-VK-019-分离与本征态射的ValuativeCriterion.md ← 新建
├── AG-VK-020-导出函子与Čech-导出上同调等价性.md ← 新建
├── AG-VK-021-曲线的Riemann-Roch定理与计算.md ← 新建
└── AG-VK-022-平坦性光滑性与上同调基变换.md ← 新建
```

---

## 7. 质量检查清单

- [ ] 每篇文档包含 `level: "silver"` 和 `target_courses: ["Stanford FOAG"]`
- [ ] 每篇文档精确引用 FOAG 章节号和习题号
- [ ] 每篇文档包含完整自然语言证明或严格推导
- [ ] 每篇文档包含“几何直觉”独立段落
- [ ] 每篇文档至少包含 2 道 FOAG 习题的详细解答
- [ ] 每篇文档嵌入或引用相关的 Lean4 代码
- [ ] 所有文档经过拼写和格式一致性检查

---

**计划编制日期**：2026-04-17
**执行负责人**：FormalMath 项目
**预计完成**：本次会话内一次性完成 7 篇文档产出
