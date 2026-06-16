---
msc_primary: '03

  - 03E20 - 00A99 - 00A99 - 00A99'
title: Sylow 第一定理 - 工作示例
processed_at: '2026-04-05'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/Sylow+theorem
  wikipedia_url: https://en.wikipedia.org/wiki/Sylow_theorems
  stacks_search_url: https://stacks.math.columbia.edu/search?query=Sylow
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=03E20
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q1057919
    consulted_at: '2026-06-16'
  textbooks:
  - title: Set Theory
    author: Thomas Jech
    edition: 3rd Millennium
    publisher: Springer
    year: 2003
    isbn: '9783540440857'
    mr_number: MR1940513
    doi: 10.1007/3-540-44761-X
  - title: A Course in Mathematical Logic
    author: Yu.I. Manin
    edition: 1st
    publisher: Springer
    year: 1977
    isbn: '9780387902432'
    mr_number: MR0453490
    doi: 10.1007/978-1-4757-4385-2
---
# Sylow 第一定理 - 工作示例

**类型**: 证明示例
**领域**: 群论
**难度**: L2
**前置知识**: 群作用、轨道、稳定子、Lagrange
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | Sylow 第一定理：Sylow \(p\)-子群存在性 |
| **领域** | 代数结构 / 群论 |
| **MSC** | 20D20（Sylow 定理） |
| **相关概念** | Sylow \(p\)-子群、群作用 |

---

## 题目

设 \(G\) 为有限群，\(|G|=p^a m\)，\(p \nmid m\)。证明 \(G\) 存在阶为 \(p^a\) 的子群（Sylow \(p\)-子群）。

---

## 完整解答（工作示例）

**步骤 1**：考虑 \(G\) 在集合 \(X = \{A \subseteq G : |A|=p^a\}\) 上的左乘作用。\(|X| = \binom{p^a m}{p^a} \equiv m \pmod{p}\)（用二项式模 \(p\) 的结论），故 \(p \nmid |X|\)。

**步骤 2**：\(X\) 的轨道分解中，存在轨道长不被 \(p\) 整除。设 \(A\) 在该轨道中，\(H = \{g \in G : gA = A\}\) 为稳定子。\(|G|=|H| \cdot |\text{轨道}|\)，故 \(p^a \mid |H|\)。又对 \(a \in A\)，\(H \subseteq a^{-1}A\)（因 \(ha \in A\)），故 \(|H| \leq |A| = p^a\)。因此 \(|H| = p^a\)，\(H\) 即为 Sylow \(p\)-子群。

---

**文档状态**: ✅ 完成  
**最后更新**: 2026年2月2日

---

## 参考文献

- Thomas Jech, *Set Theory*, 3rd Millennium ed., Springer, 2003, ISBN: 9783540440857 / MR1940513
- Yu.I. Manin, *A Course in Mathematical Logic*, 1st ed., Springer, 1977, ISBN: 9780387902432 / MR0453490