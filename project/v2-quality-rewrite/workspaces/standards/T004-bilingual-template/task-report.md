---
title: T004 任务报告：双语（自然语言 + Lean4）文档模板设计
msc_primary: 00A99
processed_at: '2026-04-05'
---
# T004 任务报告：双语（自然语言 + Lean4）文档模板设计

## 任务概述

为 FormalMath 项目设计一套标准的《双语（自然语言 + Lean4）文档模板》，并产出 3 个完整示例，保存至指定交付路径。

---

## 执行情况

### 已完成的工作

1. **项目调研**
   - 阅读了 FormalMath 项目中已有的 3 个代表性 `.lean` 文件：
     - `docs/09-形式化证明/Lean4/EuclideanAlgorithm.lean`
     - `docs/09-形式化证明/Lean4/ChineseRemainderTheorem.lean`
     - `docs/09-形式化证明/Lean4/BolzanoWeierstrass.lean`
   - 理解了现有代码的风格：使用 `/- ... -/` 大块注释包裹自然语言说明，定理证明中混合 tactic 与中文行注释。

2. **模板设计**
   - 设计了一份包含 7 个标准部分的 Markdown + Lean4 双语文档模板：
     1. 定理标题（自然语言 + Lean4 theorem name）
     2. 数学陈述（LaTeX + Lean4 type signature）
     3. 证明思路（自然语言段落）
     4. 详细形式化证明（Lean4 code block，带逐行注释）
     5. 关键 tactic 解释（战术解释）
     6. 常见变体（等价表述）
     7. 参考文献
   - 额外补充了：模板使用指南、Mathlib4 对接规范、命名规范速查表。

3. **三个完整示例撰写**
   - **示例 A**：鸽巢原理（`pigeonhole_principle`）—— 基础定理，展示反证法与 `Finset` 的组合。
   - **示例 B**：中国剩余定理的显式构造性证明（`chinese_remainder_constructive`）—— 构造性证明，展示 Bézout 系数与模运算的形式化对应。
   - **示例 C**：Bolzano-Weierstrass 定理的等价形式（`seq_compact_implies_cluster_point` / `cluster_point_implies_seq_compact`）—— 等价形式/反例结构，展示拓扑、滤子与序列收敛的双语叙述。

4. **文件交付**
   - 主交付物：`project/v2-quality-rewrite/deliverables/D004-bilingual-document-template.md`（约 40 KB）
   - 过程文件：`project/v2-quality-rewrite/workspaces/standards/T004-bilingual-template/task-report.md`（本文件）

---

## 遇到的问题与处理

### 问题 1：现有 `.lean` 文件中的 `sorry` 与未完成证明
- **现象**：`BolzanoWeierstrass.lean` 中存在个别 `sorry`，说明某些高维拓扑证明在项目内部尚未完全闭合。
- **处理**：在示例 C 中，对于递归构造子序列的某些冗长步骤，也使用了 `sorry` 作为占位，并在文档中明确说明了这一点，强调“本示例的重点在于展示双语文档如何组织等价性证明的思路与代码框架”。

### 问题 2：Mathlib4 定理名的稳定性
- **现象**：部分 Mathlib4 的定理名可能在版本迭代中发生变更（如 `IsCompact.tendsto_subseq` 的具体参数列表）。
- **处理**：在文档中统一使用“模块 + 定理名”的引用方式，并建议在项目 CI 中增加 Mathlib4 版本锁定（`lake-manifest.json` 跟踪），以确保文档中的引用与实际编译环境一致。

### 问题 3：示例 C 的代码长度控制
- **现象**：Bolzano-Weierstrass 的等价性证明涉及大量拓扑/滤子引理，完全展开会导致示例过长，喧宾夺主。
- **处理**：对核心思路进行了完整代码框架展示，对过于技术化的递归构造细节使用 `sorry` 并配以自然语言说明。这样既保证了模板的教育价值，又避免了文档过度冗长。

---

## 质量自检清单

- [x] 文档使用了 Markdown 格式，Lean4 代码块使用 ```lean 标注
- [x] LaTeX 公式使用 `$` 和 `$$` 包裹
- [x] 包含通用模板结构说明
- [x] 包含 3 个完整示例（基础定理、构造性证明、等价形式）
- [x] 包含模板使用指南（何时嵌入代码、何时引用 Mathlib4）
- [x] 包含与现有 Mathlib4 的对接规范
- [x] 示例中的 Lean4 代码语法正确（除故意标注的 `sorry` 外）
- [x] 注释清晰，逐行对应自然语言说明

---

## 后续建议

1. **模板落地**：建议选取 2–3 个现有的 `.lean` 文件（如 `EuclideanAlgorithm.lean`）按照本模板重构其配套 Markdown，验证模板的可实施性。
2. **自动化检查**：可开发一个简单的脚本，检查新撰写的双语文档是否包含模板中要求的 7 个章节标题。
3. **Mathlib4 版本同步**：在 CONTRIBUTING.md 中增加一条规范，要求引用 Mathlib4 定理时必须注明所基于的 Mathlib4 版本号或 commit hash。
