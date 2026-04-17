---
title: Harvard 232br 习题系统建设计划
task_id: P2-Harvard-232br
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
alignment_level: L5 (习题级)
processed_at: '2026-04-17'
status: 已完成 Chapter II 核心习题 60 道
version: v1.1
---

# Harvard 232br 习题系统建设计划

## 1. 背景与问题

根据 P1-T3 对齐真实性核查结果，Harvard Math 232br 的 **L5（习题解答）覆盖率仅约 4.5%**，是银层课程中最薄弱的环节。课程以 Hartshorne《Algebraic Geometry》第二章至第五章习题为核心，但项目文档中仅有个别习题（如 AG-EX-001、AG-EX-002 等）拥有完整对应解答。

本计划旨在系统性地为 Hartshorne Chapter II 的核心习题建立高质量解答文档，作为银层攻坚的第一步。

## 2. 建设目标

### 2.1 短期目标（已完成）

- ✅ 为 **Hartshorne Chapter II** 的 **26 道核心习题** 建立详细解答文档。
- 每篇文档必须包含：
  - 精确的题号引用（如 "Hartshorne II.1.1"）
  - 问题重述
  - 完整推导的详细解答
  - 关键概念提示
  - 常见错误警示
  - 嵌入相关 Lean4 代码（定义或 `sorry` 占位）
- 文档按主题合并为 **5 个文件**，便于主题式学习与后续维护。
- 建立统一的 YAML frontmatter 规范，包含 `source_textbook`、`source_chapter`、`source_exercise` 字段。

### 2.2 中期目标（本轮完成）

- ✅ 补充 Hartshorne Chapter II 剩余核心习题（II.5 续、II.6、II.7、II.8、II.9），使 Chapter II 核心习题覆盖率达到 **60+ 道**。
- 启动 Chapter III（上同调）核心习题（III.2.1、III.3.1、III.4.1、III.5.1、III.7.1 等）。
- 启动 Chapter IV（曲线）与 Chapter V（曲面）的精选习题（IV.1.1、IV.4.1、V.1.1、V.3.2 等）。

### 2.3 长期目标

- 使 Harvard 232br 的 L5 覆盖率从 **~4.5% 提升至 60% 以上**。
- 下一步启动 Chapter III（上同调）与 Chapter IV（曲线）核心习题。
- 建立可检索的 Hartshorne 习题解答知识库，与 `docs/00-习题示例反例库/` 互通索引。

## 3. 本轮已完成的习题清单

系统累计完成 **60 道** Hartshorne Chapter II 核心习题，按文件组织如下：

### 第一批（26 道）

| 文件路径 | 覆盖习题 | 数量 |
|:---------|:---------|:----:|
| `docs/13-代数几何/Harvard-232br-习题解答/II.1-层的基本性质.md` | II.1.1, II.1.2, II.1.3, II.1.4 | 4 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.2-概形的基本性质.md` | II.2.1, II.2.2, II.2.3, II.2.4, II.2.5, II.2.6 | 6 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.3-态射性质.md` | II.3.1, II.3.2, II.3.3, II.3.4, II.3.5, II.3.6 | 6 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.4-分离性与本征性.md` | II.4.1, II.4.2, II.4.3, II.4.4, II.4.5(a)(b)(d) | 5 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层.md` | II.5.1, II.5.2, II.5.3, II.5.4 | 4 |
| **小计** | — | **26** |

### 第二批（34 道，本轮新增）

| 文件路径 | 覆盖习题 | 数量 |
|:---------|:---------|:----:|
| `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层-续.md` | II.5.5, II.5.6, II.5.7, II.5.8, II.5.9 | 5 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.6-除子.md` | II.6.1, II.6.2, II.6.3, II.6.4, II.6.5, II.6.6, II.6.7, II.6.8, II.6.9, II.6.10, II.6.11, II.6.12 | 12 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.7-射影态射.md` | II.7.1, II.7.2, II.7.3, II.7.4, II.7.5, II.7.6, II.7.7 | 7 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.8-微分形式.md` | II.8.1, II.8.2, II.8.3, II.8.4, II.8.5, II.8.6 | 6 |
| `docs/13-代数几何/Harvard-232br-习题解答/II.9-形式概形.md` | II.9.1, II.9.2, II.9.3, II.9.4 | 4 |
| **小计** | — | **34** |
| **合计** | — | **60** |

## 4. 文档质量标准

所有新建文档必须满足以下规范：

1. **YAML Frontmatter**

   ```yaml
   ---
   title: Harvard 232br - Hartshorne Chapter II §X 习题解答
   course_code: Harvard Math 232br
   textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
   source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
   source_chapter: "Chapter II - Schemes, Section X - ..."
   source_exercise:
     - "II.X.Y"
     - "II.X.Z"
   difficulty: ⭐⭐ to ⭐⭐⭐⭐
   processed_at: 'YYYY-MM-DD'
   ---
   ```

2. **内容结构**
   - 每道习题独立成节，包含：题号与精确引用、问题重述、详细解答、关键概念提示、常见错误警示、Lean4 代码占位。
   - 解答必须完整，不跳步；不确定的步骤需明确标注 **"待验证"**。

3. **Lean4 代码**
   - 每道习题至少嵌入一段 Lean4 代码（定义或 `sorry` 占位），体现与形式化方向的对接。
   - 代码需使用 Mathlib 的代数几何相关命名空间（如 `AlgebraicGeometry`）。

4. **交叉引用**
   - 解答中引用的其他习题（如 II.2.1、II.3.6、II.4.1）需标注精确引用。
   - 关键定理（如 Nakayama 引理、Affine Communication Lemma、赋值判别法）需标注 Hartshorne 中的位置。

## 5. 与现有文档的关系

- **已有解答**：`docs/13-代数几何/习题/` 中已有 AG-EX-001 至 AG-EX-015 等 15 道习题，覆盖 Chapter I、III、IV、V 的部分内容。本轮新建的 Harvard 232br 习题解答位于独立目录 `docs/13-代数几何/Harvard-232br-习题解答/`，避免与原有通用习题库混淆。
- **索引更新**：建议后续在 `project/Harvard-232br-L5-习题对齐表.md` 中更新"当前状态"列，将本轮 26 道习题标记为 ✅ 已对齐，并填入对应文件路径。

## 6. 风险评估与待验证项

| 风险/待验证项 | 说明 | 应对措施 |
|:-------------|:-----|:---------|
| II.3.4 的下降引理细节 | 从仿射局部有限性粘合到整体的证明涉及模的下降理论 | 当前解答已给出标准论证；如需严格形式化，可参考 Stacks Project Tag 00ME |
| II.4.5(c) 的逆命题 | 赋值判别法的完整逆证明较复杂 | 已在文档中标记为"待验证补充项"，计划在后续轮次中补全 |
| II.5.4 中 codim 1 非正则点 | 非 DVR 的 1 维 Noetherian 局部整环上无挠模是否必自由 | 已在文档中标注"待验证"，并给出 DVR 情形下的完整论证 |
| II.6.7 结点三次曲线的 Picard 群 | 利用标准化映射计算 Picard 群的细节涉及层上同调的长正合列 | 已给出标准论证并标注"待验证"，可参考 Stacks Project Tag 0B5S |
| II.6.11 射影空间的 K-群结构 | 环结构的严格证明需用 Koszul 复形或分次模的消解 | 已给出框架性论证并标注"待验证" |
| II.8.3 正则局部环的微分判别 | 反向证明中 embedding dimension 与 Krull dimension 的比较 | 已给出标准论证并标注"待验证" |
| II.9.4 完备化定理的一般 $i$ | 高阶上同调的完备化定理即 Zariski 的 Theorem on Formal Functions | 文档中已给出 $i=0$ 的完整证明，并引用一般定理 |

## 7. 下一步行动

1. **索引同步**：更新 `project/Harvard-232br-L5-习题对齐表.md`，将新增 34 道习题的 FormalMath 对应路径填入。
2. **下一轮选题**（建议）：
   - Chapter II 剩余零散习题（II.5.10–II.5.18 中的精选）
   - III.2.1, III.4.1, III.5.1, III.7.1（上同调基础计算与 Serre 对偶）
   - IV.1.1, IV.3.1, IV.4.1（Riemann-Roch、曲线嵌入与线丛）
   - V.1.1, V.3.2（曲面相交理论与爆破）
3. **质量审查**：由审核人对解答中的"待验证"标注进行数学正确性核查。

---

**计划文档位置**: `project/Harvard-232br-习题系统建设计划.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17
**负责人**: FormalMath 项目
**当前状态**: Chapter II 核心习题 60 道已完成
