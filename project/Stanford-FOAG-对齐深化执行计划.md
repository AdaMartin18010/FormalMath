---
title: Stanford FOAG 对齐深化执行计划
msc_primary: 00A99
task_id: P2-Stanford-FOAG- deepen
course_code: Stanford FOAG
course_name: Foundations of Algebraic Geometry
level: silver
target_courses:
  - Stanford FOAG
version: v2.0
date_created: '2026-04-17'
date_updated: '2026-04-17'
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
| Part I (Ch 1–2) | AG-VK-002, AG-VK-005, **AG-VK-016** | 🟢 层化定理、stalk 正合性已覆盖 |
| Part II (Ch 3–6) | AG-VK-001, AG-VK-003, AG-VK-004, **AG-VK-017**, **AG-VK-018** | 🟢 结构层、Proj 泛性质已补全 |
| Part III (Ch 7–11) | **AG-VK-019**, **AG-VK-023** | 🟢 Valuative Criterion、有限态射已覆盖 |
| Part IV (Ch 13–19) | **AG-VK-024**, **AG-VK-025**, **AG-VK-027** | 🟢 除子理论、线丛、Blow-up 已覆盖 |
| Part V (Ch 18, 22) | AG-VK-007, AG-VK-008, **AG-VK-020**, **AG-VK-026** | 🟢 Čech-导出等价、Serre 对偶已深化 |
| Part VI (Ch 23–29) | AG-VK-009, AG-VK-010, **AG-VK-021**, **AG-VK-022** | 🟢 Riemann-Roch、平坦性、基变化已覆盖 |
| 曲线专题 | **AG-VK-028**, **AG-VK-029** | 🟢 椭圆曲线群结构、Hurwitz 定理已覆盖 |

### 1.2 两轮深化后修复的薄弱点

1. **stalk 的泛化定义缺失**：✅ AG-VK-016 补全。
2. **结构层构造细节待补**：✅ AG-VK-017 补全。
3. **Proj 细节待补**：✅ AG-VK-018 补全。
4. **Valuative Criterion 证明缺失**：✅ AG-VK-019 补全。
5. **上同调计算题不足**：✅ AG-VK-020 补全。
6. **曲线理论证明稀缺**：✅ AG-VK-021、AG-VK-028、AG-VK-029 补全。
7. **Part VI 证明极度稀缺**：✅ AG-VK-022 补全。
8. **除子与线丛理论薄弱**：✅ AG-VK-024、AG-VK-025 补全。
9. **Serre 对偶完整陈述缺失**：✅ AG-VK-026 补全。
10. **Blow-up 与奇点消解薄弱**：✅ AG-VK-027 补全。

---

## 2. 执行目标

### 2.1 总体目标

通过两轮深化，共产出 **14 篇 Silver 级** FOAG 深化文档（AG-VK-016 到 AG-VK-029），使 FOAG L4（定理证明）从 ~50% 提升到 **≥90%**，L5（习题解答）从 15/30 主题提升到 **26/30 主题以上**。

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

## 3. 第一轮：选定的 7 篇深化文档（已完成）

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

## 4. 第二轮：新增 7 篇深化文档（已完成）

| 编号 | 主题 | 对应 FOAG 章节 | 修复的薄弱点 |
|------|------|----------------|-------------|
| **AG-VK-023** | 有限态射的整体与局部刻画 | Ch 7.3, Ch 10 | 有限态射 = 仿射 + 真、正像保持凝聚性 |
| **AG-VK-024** | Weil 除子与 Cartier 除子的等价理论 | Ch 14 | 除子理论、Cl(P^n) = Z、CaCl ≅ Cl |
| **AG-VK-025** | 线丛与映射到射影空间 | Ch 15 | 全局截面生成、very ample 判别、Segre 嵌入 |
| **AG-VK-026** | Serre 对偶定理的完整陈述与应用 | Ch 18, Ch 22 | 对偶层、Serre 对偶在 P^n 与曲线上 |
| **AG-VK-027** | 爆破的几何与代数 | Ch 19 | Blow-up 泛性质、A^2 爆破、Castelnuovo |
| **AG-VK-028** | 椭圆曲线的群结构 | Ch 19 | Weierstrass 方程、弦切群律 |
| **AG-VK-029** | 曲线的 Hurwitz 定理 | Ch 17 | 分歧指数、Hurwitz 公式、超椭圆曲线 |

---

## 5. 每篇文档的内容规划（第二轮）

### AG-VK-023：有限态射的整体与局部刻画

- **核心定理**：有限态射的定义、有限 = 仿射 + 真（Ch 7.3）、基变换保持有限性
- **几何直觉**：有限态射是“纤维为有限点集（带重数）”的映射，类似覆叠映射的代数类比
- **习题**：
  - Ex 7.3.M：有限 = 仿射 + 真
  - Ex 7.3.N：基变换保持有限性
  - Ex 7.4.A：有限态射的正像保持凝聚性
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.Morphisms.Finite`

### AG-VK-024：Weil 除子与 Cartier 除子的等价理论

- **核心定理**：Weil 除子、Cartier 除子、正规概形上 CaCl ≅ Cl（Ch 14）
- **几何直觉**：Weil 是“余维1子簇的线性组合”，Cartier 是“局部由方程定义”
- **习题**：
  - Ex 14.2.B：Cl(P^n_A) = Z
  - Ex 14.2.E：Cartier 与 Weil 的对应关系
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.Divisor`

### AG-VK-025：线丛与映射到射影空间

- **核心定理**：线丛由全局截面生成 ⇔ 映射到 P^n（Ch 15.3）、very ample 判别、Segre 嵌入
- **几何直觉**：线丛的截面是“射影坐标函数”，very ample 给出闭嵌入
- **习题**：
  - Ex 15.3.A：线丛到射影空间的映射
  - Ex 15.3.C：very ample 的判别
  - Ex 15.3.F：Segre 嵌入与 O(1,1)
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.LineBundle`

### AG-VK-026：Serre 对偶定理的完整陈述与应用

- **核心定理**：Serre 对偶的一般形式（Ext 版本）、P^n 上的显式计算、曲线上的对偶（Ch 18, 22）
- **几何直觉**：Serre 对偶是代数几何中的 Poincaré 对偶，ω_X 是对偶化对象
- **习题**：
  - Ex 18.5.B：P^n 上的 Serre 对偶显式计算
  - Ex 18.5.C：曲线上的 Serre 对偶与 Riemann-Roch
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.SerreDuality`

### AG-VK-027：爆破的几何与代数

- **核心定理**：Blow-up 的泛性质、A^2 在原点的爆破、Castelnuovo 收缩准则（Ch 19）
- **几何直觉**：爆破是“放大奇点，用切方向替换它”，如同用显微镜展开奇点
- **习题**：
  - Ex 19.2.C：A^2 在原点的爆破，E ≅ P^1
  - Ex 19.4.B：Castelnuovo 判别法（概要）
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.Blowup`

### AG-VK-028：椭圆曲线的群结构

- **核心定理**：Weierstrass 方程的存在性、弦切群律的良定义性（Ch 19）
- **几何直觉**：椭圆曲线上的群律来自 Bezout 定理——三点共线则和为零
- **习题**：
  - Ex 19.9.B：平面三次曲线上的群律
  - Ex 19.9.C：Weierstrass 方程的存在性
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.EllipticCurve`

### AG-VK-029：曲线的 Hurwitz 定理

- **核心定理**：分歧指数、Hurwitz 公式、超椭圆曲线的分歧点（Ch 17）
- **几何直觉**：分歧指数衡量覆叠的“折叠层数”，Hurwitz 公式联系拓扑与分歧数据
- **习题**：
  - Ex 17.4.H：超椭圆曲线的 Hurwitz 公式应用
  - Ex 17.4.I：P^1 自映射的分歧与 Hurwitz 公式
- **Lean4 引用**：`Mathlib.AlgebraicGeometry.Curve.Hurwitz`

---

## 6. 习题解答覆盖统计

### 第一轮统计（已完成）

| 文档 | 习题号 |
|------|--------|
| AG-VK-016 | Ex 2.4.B, Ex 2.5.D |
| AG-VK-017 | Ex 3.7.E, Ex 4.3.B |
| AG-VK-018 | Ex 6.3.M, Ex 6.4.F |
| AG-VK-019 | Ex 7.3.D, Ex 8.4.G |
| AG-VK-020 | Ex 18.2.H, Ex 18.3.A |
| AG-VK-021 | Ex 18.4.A, Ex 19.2.B |
| AG-VK-022 | Ex 24.5.J, Ex 25.2.E |
| **小计** | **14 道** |

### 第二轮统计（已完成）

| 文档 | 习题号 |
|------|--------|
| AG-VK-023 | Ex 7.3.M, Ex 7.3.N, Ex 7.4.A |
| AG-VK-024 | Ex 14.2.B, Ex 14.2.E |
| AG-VK-025 | Ex 15.3.A, Ex 15.3.C, Ex 15.3.F |
| AG-VK-026 | Ex 18.5.B, Ex 18.5.C |
| AG-VK-027 | Ex 19.2.C, Ex 19.4.B |
| AG-VK-028 | Ex 19.9.B, Ex 19.9.C |
| AG-VK-029 | Ex 17.4.H, Ex 17.4.I |
| **小计** | **16 道** |

### 总计

**两轮深化共新增 30 道 FOAG 习题的详细解答**，大幅超出原定的“至少 10 道”目标。

---

## 7. 输出文件清单

```
project/
└── Stanford-FOAG-对齐深化执行计划.md       ← 本计划

docs/13-代数几何/习题/
├── AG-VK-001 ~ AG-VK-015                   ← 历史文档
├── AG-VK-016-层的层化与stalk判定正合性.md   ← 第一轮
├── AG-VK-017-仿射概形的结构层与Spec-Γ范畴等价.md ← 第一轮
├── AG-VK-018-Proj构造与其泛性质.md         ← 第一轮
├── AG-VK-019-分离与本征态射的ValuativeCriterion.md ← 第一轮
├── AG-VK-020-导出函子与Čech-导出上同调等价性.md ← 第一轮
├── AG-VK-021-曲线的Riemann-Roch定理与计算.md ← 第一轮
└── AG-VK-022-平坦性光滑性与上同调基变换.md ← 第一轮

docs/13-代数几何/FOAG-深化/
├── AG-VK-023-有限态射的整体与局部刻画.md   ← 第二轮
├── AG-VK-024-Weil除子与Cartier除子的等价理论.md ← 第二轮
├── AG-VK-025-线丛与映射到射影空间.md       ← 第二轮
├── AG-VK-026-Serre对偶定理的完整陈述与应用.md ← 第二轮
├── AG-VK-027-爆破的几何与代数.md           ← 第二轮
├── AG-VK-028-椭圆曲线的群结构.md           ← 第二轮
└── AG-VK-029-曲线的Hurwitz定理.md         ← 第二轮
```

---

## 8. 质量检查清单

- [x] 每篇文档包含 `level: "silver"` 和 `target_courses: ["Stanford FOAG"]`
- [x] 每篇文档精确引用 FOAG 章节号和习题号
- [x] 每篇文档包含完整自然语言证明或严格推导
- [x] 每篇文档包含“几何直觉”独立段落
- [x] 每篇文档至少包含 2 道 FOAG 习题的详细解答
- [x] 每篇文档嵌入或引用相关的 Lean4 代码
- [x] 所有文档经过拼写和格式一致性检查

---

**计划编制日期**：2026-04-17
**第二轮更新日期**：2026-04-17
**执行负责人**：FormalMath 项目
**状态**：🎉 两轮深化已全部完成，共 14 篇 Silver 文档 + 30 道习题解答
