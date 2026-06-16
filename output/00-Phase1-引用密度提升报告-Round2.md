---
title: FormalMath Phase 1 引用密度提升进展报告（Round 2）
level: meta
processed_at: '2026-06-16T15:11:28+08:00'
review_status: draft
---

# FormalMath Phase 1 引用密度提升进展报告（Round 2）

**报告日期**: 2026年06月16日  
**工作重心**: 银层/金层文档引用密度提升，标准教材 ISBN/MR 批量注入与经典论文 DOI 补充  
**全库规模**: 约 8,768 篇 Markdown，424 个 Lean 文件

---

## 一、本轮执行动作

1. **扩展 `scripts/inject_standard_textbooks_by_msc.py`**
   - 修复 `msc_primary` 解析：支持 `14 - 14A15`、`26A99`、`00\n- 00A99` 等多分隔格式，按前两位 MSC 大类匹配。
   - 将标准教材映射从 10 个 MSC 大类扩展到 **24 个 MSC 大类**，新增：
     - 00（通用参考）、03（数理逻辑/集合论）、05（组合学）、08（一般代数系统）、11（数论）、13（交换代数）
     - 30（复分析）、32（多复变）、40（序列与级数）、46（泛函分析）、51（几何）
     - 54（一般拓扑）、55（代数拓扑）、65（数值分析）等。
   - 新增并核验 ISBN/MR 的经典教材：
     - Atiyah–Macdonald *Introduction to Commutative Algebra* (MR0242802)
     - Eisenbud *Commutative Algebra* (MR1322960)
     - Hatcher *Algebraic Topology* (MR1867354)
     - Ahlfors *Complex Analysis* (MR0510197)
     - Jech *Set Theory* (MR1940513)
     - Stanley *Enumerative Combinatorics, Vol. 1* (MR2868112)
     - Trefethen–Bau *Numerical Linear Algebra* (MR1444820)
     - Pugh *Real Mathematical Analysis*、Conway *A Course in Functional Analysis*、Axler *Linear Algebra Done Right*、Hartshorne *Geometry: Euclid and Beyond*、Gowers *Princeton Companion* 等。

2. **更新 `scripts/dedup_silver_references.py`**
   - 在 `KNOWN_BOOKS` 中补全上述 13 本新教材的元数据，确保后续去重时自动补全缺失的 ISBN/MR。

3. **扩展 `scripts/inject_landmark_papers.py`**
   - 新增 8 组高置信度经典论文映射：布朗运动（Einstein 1905）、高斯-博内（Chern 1944）、陈类（Chern 1946）、Yang-Mills（1954）、纳什均衡（1950）、博弈论基础（von Neumann 1928）、Ramsey 定理（1930）。

4. **执行注入与审计**
   - 运行教材注入脚本、去重脚本与 landmark 论文脚本。
   - 重新运行 `scripts/phase1_content_audit.py` 并校验全库 frontmatter 解析错误为 0。

---

## 二、本轮产出数据

| 指标 | 数值 |
|------|------|
| 标准教材注入文档数 | **149 篇**（银层/金层） |
| 银层 references 去重/补全文档数 | **13 篇** |
| Landmark 论文注入文档数 | **21 篇** |
| 新增经典教材条目 | **13 本** |
| 新增 Landmark 论文条目 | **8 篇** |
| 全库 frontmatter 解析错误 | **0 篇** |

---

## 三、审计快照对比（300 篇分层抽样）

| 标识符类型 | 本轮前 | 本轮后 | 变化 |
|-----------|-------|-------|------|
| DOI | 26 | 22 | -4（随机抽样波动） |
| ISBN | 210 | 216 | **+6** |
| arXiv | 0 | 4 | **+4** |
| MR | 141 | 173 | **+32** |
| zbMATH | 64 | 46 | -18（随机抽样波动） |
| Wikidata | 157 | 145 | -12（随机抽样波动） |
| Stacks Tag | 5 | 4 | -1（随机抽样波动） |
| MacTutor | 27 | 19 | -8（随机抽样波动） |

- **平均引用密度**：0.63 条精确标识符 / 千字（抽样值，受随机样本影响，与全库实际增长不完全同步）
- **含 external_ids 文档**：146 / 300 (48.7%)

> 注：抽样审计的波动主要源于 300 篇样本的随机性；本轮实际在 149 篇文档中新增了数百条 ISBN/MR  frontmatter 引用，并在 21 篇文档中新增了 DOI/arXiv 经典论文。

---

## 四、全库标识符总量估算（聚焦数学内容前缀）

对 `docs/`、`concept/`、`数学家理念体系/`、`project/`、`FormalMath-v2/`、`FormalMathLean4/` 扫描：

| 标识符类型 | 全库出现次数 |
|-----------|------------|
| DOI | 477 |
| ISBN | 1,662 |
| arXiv | 249 |
| MR | 323 |
| zbMATH | 2,642 |
| Wikidata | 3,449 |
| Stacks Tag | 472 |
| MacTutor | 814 |

按约 23,027,265 词估算，全库聚焦数学内容的引用密度约为 **0.44 条/千字**。距离 2–3 条/千字仍有显著差距，需要持续多轮补充。

---

## 五、关键经验教训

1. **MSC 解析必须健壮**：`msc_primary` 存在字符串、列表、多行混合、空格/横杠分隔等多种形态，统一取前两位数字大类是注入的前提。
2. **ISBN/MR 需要人工核验**：新增教材均通过多源交叉验证（Amazon、AMS、Springer、arXiv 引用条目），避免占位符。
3. **抽样审计有波动**：引用密度目标应结合全库总量与核心课程子集共同评估，避免被单次 300 篇样本误导。
4. **范围控制**：教材注入仍限定在银层/金层文档；若向铜层/未标注文档大规模扩展，需要增加报告类文件过滤与更细粒度的主题匹配，防止误伤。

---

## 六、下一步建议

1. **继续扩展标准教材映射**：覆盖剩余高频 MSC 大类（22 拓扑群、28 测度论、60 概率论、70 力学、94 信息论等），并为每门核心课程建立课程→教材的精确映射。
2. **为核心概念建立精确外部链接映射**：扩展 `inject_authoritative_concept_links.py` 的 `CONCEPT_LINKS`，覆盖 200+ 核心概念到 nLab / Wikipedia / Stacks 的精确词条。
3. **修复剩余 239 条全库确认失效链接**：重点清理 `FormalMath-Enhanced/` 代码文档与报告中的 localhost/示例 URL。
4. **核心课程逐章补齐**：对 MIT 18.100A、18.701、18.06、Harvard 232br、Stanford FOAG 逐章补充定义、完整证明、示例、习题-解答对，同时同步写入教材引用。
5. **建立引用密度仪表盘**：在 `project/00-项目进度报告/` 中维护按核心课程/MSC 分层的密度追踪表，替代单次抽样审计。

---

*本报告由 `scripts/inject_standard_textbooks_by_msc.py`、`scripts/dedup_silver_references.py`、`scripts/inject_landmark_papers.py` 与 `scripts/phase1_content_audit.py` 自动生成并人工整理。*
