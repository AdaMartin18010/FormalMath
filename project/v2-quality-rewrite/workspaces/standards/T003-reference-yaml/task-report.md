---
title: T003 任务报告：参考文献硬链接 YAML 规范
msc_primary: 00A99
processed_at: '2026-04-05'
---
# T003 任务报告：参考文献硬链接 YAML 规范

## 任务概述

- **任务编号**：T003-reference-yaml
- **任务名称**：设计《参考文献硬链接 YAML 规范》
- **执行时间**：2026-04-04
- **输出文件**：
  - `project/v2-quality-rewrite/deliverables/D003-reference-linking-spec.yaml`
  - `project/v2-quality-rewrite/workspaces/standards/T003-reference-yaml/task-report.md`（本文件）

---

## 执行情况

### 1. 已完成的工作

1. **设计了完整的 YAML Schema**
   - 定义了 `references` 根键下的四个核心数组：`textbooks`、`papers`、`databases`、`online_resources`。
   - 为每个字段明确了数据类型、必填/选填规则以及示例值。
   - 特别对 `stacks_project` 的 `identifier` 做出了 4 位字母数字的格式约束。

2. **提供了 5 个跨领域的完整示例**
   - **分析学**：以 Rudin《Principles of Mathematical Analysis》、Royden《Real Analysis》及 Lebesgue 1902 年论文为核心。
   - **代数学**：以 Dummit & Foote《Abstract Algebra》、Artin《Algebra》及 Feit-Thompson 1963 年论文为核心。
   - **几何学**：以 do Carmo《Differential Geometry of Curves and Surfaces》、O'Neill 及 Gauss 1828 年原始论文为核心。
   - **数理逻辑**：以 Jech《Set Theory》、Kunen《Set Theory: An Introduction to Independence Proofs》及 Cohen 1963-1964 年连续统假设独立性论文为核心。
   - **数论**：以 Hardy & Wright《An Introduction to the Theory of Numbers》、Apostol《Introduction to Analytic Number Theory》及 Hadamard 1896 年、Riemann 1859 年经典论文为核心。
   - 每个示例均包含教科书引用（精确到章节/页码）、论文引用（含 DOI/zbMATH/MR Number）以及数据库链接。

3. **制定了引用密度建议**
   - 铜层（基础入门）：≥ 2 条/1000 字，章节级精度。
   - 银层（本科核心）：≥ 4 条/1000 字，节/页码级精度。
   - 金层（研究生前沿）：≥ 6 条/1000 字，页码/Tag 级精度。

4. **编写了 Stacks Project Tag 引用规范**
   - 明确了 Tag 的 4 位字母数字格式。
   - 区分了 Tag 级、Section 级、Chapter 级三种引用精度。
   - 规定了 URL 构造规则：`https://stacks.math.columbia.edu/tag/{identifier}[需更新]`。

5. **提供了自动化建议**
   - DOI → BibTeX：Crossref API 使用示例。
   - zbMATH Open API：文献信息查询工作流。
   - arXiv API：预印本元数据获取脚本。
   - CI 校验规则建议（ISBN 校验、URL 格式、Stacks Tag 长度等）。

### 2. 文献信息来源

为确保示例中的书目信息尽可能真实精确，执行过程中通过 Web Search 验证了以下关键信息：
- Rudin, *Principles of Mathematical Analysis*, 3rd ed. (1976) — ISBN 978-0-07-054235-8, zbMATH Zbl 0346.26002
- Dummit & Foote, *Abstract Algebra*, 3rd ed. (2004) — ISBN 978-0-471-43334-7, MR 2286236
- do Carmo, *Differential Geometry of Curves and Surfaces* (1976) — ISBN 978-0-13-212589-5, zbMATH Zbl 0326.53001
- Jech, *Set Theory*, 3rd Millennium ed. (2002) — ISBN 978-3-540-44085-7, zbMATH Zbl 1007.03002
- Hardy & Wright, *An Introduction to the Theory of Numbers*, 6th ed. (2008) — ISBN 978-0-19-921986-5
- Cohen 1963 PNAS 论文 — DOI 10.1073/pnas.50.6.1143
- Hadamard 1896 论文 — Bull. Soc. Math. France 24, pp. 199-220
- Riemann 1859 论文 — Monatsberichte der Berliner Akademie, pp. 671-680

### 3. 遇到的问题与处理

| 问题 | 处理方案 |
|------|----------|
| 部分古典数学论文（如 Gauss 1828、Riemann 1859、Hadamard 1896）没有现代 DOI。 | 在 YAML 中保留空 `doi` 字段，同时提供 zbMATH ID、MR Number 以及档案馆/Numdam 链接。 |
| zbMATH Open API 需要注册 Key，无法在规范中直接提供可运行的在线示例。 | 在自动化建议部分说明了注册流程，并提供了 Python 伪代码。 |
| Stacks Project 的 Tag 与人类可读的 Section 标题之间没有直观映射。 | 在规范中明确要求使用 Tag 作为 `identifier`，并在 `notes` 中补充说明对应的数学内容。 |
| 需要同时支持中文说明和 YAML 机器可读格式。 | 采用 Markdown 包裹 YAML 的方式，主体文件保存为 `.yaml` 扩展名，兼顾可读性与解析性。 |

### 4. 交付物清单

- [x] `project/v2-quality-rewrite/deliverables/D003-reference-linking-spec.yaml`（约 30.7 KB）
- [x] `project/v2-quality-rewrite/workspaces/standards/T003-reference-yaml/task-report.md`（本文件）

### 5. 后续建议

1. **自动化工具开发**：建议开发一个 Python CLI 工具，支持通过 DOI/arXiv ID/zbMATH ID 自动生成符合本规范的 YAML 片段。
2. **CI 集成**：在 GitHub Actions 中加入 YAML Linter，自动检查引用格式的合规性。
3. **Stacks Project Tag 缓存**：建立本地 Tag → 标题的缓存映射表，方便作者快速查找正确的 Tag。
4. **ISBN 校验库**：统一使用 `isbnlib` 或类似库进行 ISBN-10/ISBN-13 校验与转换。

---

## 结论

本任务已按要求完成，交付了详细的《参考文献硬链接 YAML 规范》及相应的过程报告。规范覆盖了 Schema 定义、5 个数学领域示例、引用密度建议、Stacks Project Tag 规范以及自动化工作流建议，可直接用于 FormalMath 项目的质量改写阶段。
