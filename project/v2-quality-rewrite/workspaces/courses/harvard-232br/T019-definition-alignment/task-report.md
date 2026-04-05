---
title: T019 Definition Alignment — Task Report
msc_primary: 00A99
processed_at: '2026-04-05'
---
# T019 Definition Alignment — Task Report

**Course**: Harvard Math 232br (Curves, Surfaces, Varieties / Cohomology)  
**Task ID**: T019  
**Deliverable**: D019-harvard-232br-definition-alignment.md  
**Standard**: D002 — L3 Semantic Alignment Playbook  
**Execution Date**: 2026-04-04  
**Analyst**: Kimi Code CLI — Algebraic Geometry Course Analyst  

---

## 1. 任务概述

本任务对 Harvard Math 232br 课程大纲（D009）中列出的全部定义条目执行 L3 语义对齐审查。对齐依据 D002 的“严格等价 / 近似表述 / 缺失”三档标准，逐条核对课程定义与项目文档中的数学表述，生成《L3 定义对齐手册》（D019）。

---

## 2. 执行过程

1. **读取 syllabus (D009)**：提取 Module 0–5 中全部 `definitions` 条目，共 **73** 个定义。
2. **读取对齐手册 (D002)**：内化 L3 的 5 条严格等价判据（对象域、逻辑等价、符号兼容、边界一致、等价路径文档化）。
3. **批量读取项目文档**：共读取 ~25 份文档，涵盖
   - `docs/13-代数几何/`（01–09）
   - `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/`（00, 05, 06, 07, 12, 16, 17, 25, 31）
   - `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/`（01, 15, 17, 21）
4. **逐条比对与判定**：对每个定义，记录课程定义、项目路径、项目摘录、判定结论、差异分析、修正建议。
5. **生成统计与附录**：汇总严格/近似/缺失的数量与百分比，输出新增文档需求列表。

---

## 3. 对齐统计

| 类别 | 数量 | 百分比 | 备注 |
|:-----|:----:|:------:|:-----|
| **严格等价** | 31 | 42.5% | 多数来自 `docs/13-代数几何/` 的深度扩展文档（层论、除子、曲面、霍奇理论）。 |
| **近似表述** | 13 | 17.8% | 主要因对象域扩大（概形而非簇）、缺少显式边界条件、或仅有 ASCII 框图式描述。 |
| **缺失** | 29 | 39.7% | 核心定义块完全缺失，或仅有符号使用而无定义。 |
| **总计** | 73 | 100% | — |

### 3.1 按模块分布

| 模块 | 严格 | 近似 | 缺失 | 总计 |
|:-----|:----:|:----:|:----:|:----:|
| Module 0 (Review) | 5 | 2 | 9 | 16 |
| Module 1 (Sheaves) | 5 | 2 | 6 | 13 |
| Module 2 (Cohomology) | 3 | 0 | 7 | 10 |
| Module 3 (Duality & Curves) | 4 | 2 | 2 | 8 |
| Module 4 (Surfaces) | 5 | 0 | 7 | 12 |
| Module 5 (Advanced) | 4 | 2 | 3 | 9 |

---

## 4. 关键发现与问题

### 4.1 严格等价率较高的领域
- **层上同调基础**：`docs/13-代数几何/04-层与上同调-深度扩展版.md` 中的 presheaf、sheaf、sheafification、sheaf cohomology 定义完整且与 Hartshorne 一致。
- **除子与线丛**：`04-除子与线丛的完整理论.md` 对 Weil divisor、Cartier divisor、principal divisor、linear equivalence、Picard group 的定义精确。
- **曲面相交理论**：`08-曲面理论-深度扩展版.md` 对 intersection pairing、self-intersection、exceptional divisor、blow-up、minimal surface、geometric genus 的定义精确。
- **霍奇理论**：`09-霍奇理论入门.md` 对 Hodge decomposition、Hodge numbers、period map 的定义精确。

### 4.2 近似表述的主要根因
1. **对象域扩大**：Zariski topology、Krull dimension、Blow-up 在 Grothendieck 路径文档中以概形/泛性质形式呈现，缺少对古典簇情形的显式回注。
2. **ASCII 框图式描述**：`05-拟凝聚层与凝聚层.md`、`31-概形的层理论与层范畴.md` 使用高度压缩的框图，缺少严格的形式化定义块。
3. **凝聚层定义的数学不精确**：`05-拟凝聚层与凝聚层.md` 将 coherent 简化为“拟凝聚 + 有限型”，遗漏 Hartshorne 的核心 kernel 有限型条件；若不加 Noether 条件，这是错误的。
4. **对偶化层仅覆盖光滑情形**：`21-上同调与Serre对偶.md` 仅定义了光滑簇上的 $\omega_X$，未涉及 proper/Cohen-Macaulay 的一般 dualizing sheaf。

### 4.3 缺失条目的集中领域
- **Module 0**：quasi-projective variety、regular map、smooth point、tangent cone、Hilbert function/polynomial、arithmetic genus、$g^r_d$、canonical divisor $K_X$。
- **Module 1–2**：stalk、exact sequences of sheaves、structure sheaf $\mathcal{O}_X$（因指向空壳索引页）、injective resolution、flasque sheaf、acyclic resolution、refinement、twisting sheaf $\mathcal{O}_{\mathbb{P}^n}(d)$、locally free sheaf（一般秩）、reflexive sheaf。
- **Module 4**：arithmetic genus $p_a(S)$、irregularity $q(S)$、Kodaira dimension $\kappa(S)$、ruled/K3/Enriques/Abelian surface。
- **Module 5**：Kodaira-Spencer map、obstruction theory、moduli space（严格定义缺失）。

---

## 5. 阻塞性问题

本次任务 **无阻塞性问题**。输出目录已存在，D019 与 task-report 均已成功生成。

---

## 6. 建议的后续行动（按优先级）

### P0 — 必须尽快补足以避免课程使用断裂
1. **修正 coherent sheaf 的定义**：在 `05-拟凝聚层与凝聚层.md` 中补全 Hartshorne 的两条标准条件（有限型 + kernel 有限型），并标注 Noether 条件。
2. **补充 twisting sheaf**：在 `04-除子与线丛的完整理论.md` 或 `04-层与上同调-深度扩展版.md` 中给出 $\mathcal{O}_{\mathbb{P}^n}(d)$ 的显式定义（$S(d)^\sim$ 或转移函数）。
3. **补充 stalk 与 exact sequence of sheaves**：在 `04-层与上同调-深度扩展版.md` 中补充这两个核心层论定义。
4. **修正 structure sheaf 的引用路径**：D009 指向 `00-概形理论-概念总览.md`（空壳索引页），应将路径改为有实际定义的文档（如 `02-仿射概形基础.md` 或 `docs/13-代数几何/02-代数几何增强版.md`）。

### P1 — 高价值补充（涉及课程核心考试内容）
5. 在 `08-曲面理论-深度扩展版.md` 中补充 Enriques 分类的核心不变量：$p_a(S)$、$q(S)$、$\kappa(S)$、ruled/K3/Enriques/Abelian surface。
6. 在 `07-曲线理论-深度扩展版.md` 中补充 $g^r_d$、canonical divisor $K_X$、degree of line bundle on curve、curve embedding via $|D|$。
7. 在 `02-代数几何增强版.md` 中补充 regular map、smooth point（非循环定义）、tangent cone。
8. 在 `03-代数几何深度扩展版.md` 中补充 Hilbert function / polynomial 的完整定义。

### P2 — 深造/前沿内容（Module 5）
9. 大幅扩充 `25-概形的平坦族与形变理论.md`：补充 deformation functor（Schlessinger 条件）、first-order deformation 的完整定义、obstruction theory。
10. 在独立文档或 `03-代数几何深度扩展版.md` 中补充 Kodaira-Spencer map 的完整定义。
11. 在 `03-代数几何深度扩展版.md` 中补充 moduli space 的粗/精细定义（coarse vs. fine）。

---

## 7. 产出文件

| 文件 | 路径 | 状态 |
|:-----|:-----|:----:|
| D019 定义对齐手册 | `project/v2-quality-rewrite/deliverables/D019-harvard-232br-definition-alignment.md` | 已生成 |
| T019 任务报告 | `project/v2-quality-rewrite/workspaces/courses/harvard-232br/T019-definition-alignment/task-report.md` | 已生成 |

---

**报告结束**
