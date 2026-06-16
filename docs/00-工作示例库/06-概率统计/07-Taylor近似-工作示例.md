---
msc_primary: '00

  - 00A99 - 26A42 - 03B40'
title: Taylor 近似 - 工作示例
processed_at: '2026-04-05'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/Taylor's+theorem
  wikipedia_url: https://en.wikipedia.org/wiki/Taylor's_theorem
  stacks_search_url: https://stacks.math.columbia.edu/search?query=Taylor
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q1137206
    consulted_at: '2026-06-16'
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
---
# Taylor 近似 - 工作示例

**类型**: 应用示例
**领域**: 微积分
**难度**: L1
**前置知识**: 导数、Taylor 公式
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 用 Taylor 多项式近似计算 \(e^{0.1}\) |
| **领域** | 分析学 / 微积分 |
| **MSC** | 26A24（导数） |
| **相关概念** | [导数](../../../concept/核心概念/15-导数.md) |

---

## 题目

用 \(e^x\) 在 \(x=0\) 处的 3 次 Taylor 多项式近似计算 \(e^{0.1}\)，并估计误差。

---

## 完整解答（工作示例）

**步骤 1**：\(e^x = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + R_3(x)\)，其中 \(R_3(x) = \frac{e^\xi}{4!} x^4\)，\(\xi\) 在 0 与 \(x\) 之间。取 \(x=0.1\)：\(e^{0.1} \approx 1 + 0.1 + \frac{0.01}{2} + \frac{0.001}{6} = 1 + 0.1 + 0.005 + 0.000167\ldots \approx 1.10517\)。

**步骤 2**：误差 \(|R_3(0.1)| \le \frac{e^{0.1}}{24}(0.1)^4 < \frac{2}{24}\cdot 10^{-4} < 10^{-5}\)，故近似值精确到约 \(10^{-5}\)。

---

## 关键步骤说明

- **Taylor 多项式**：用多项式逼近函数，便于计算与估计。
- **余项**：Lagrange 余项可给出误差上界。

---

## 相关概念链接

- [导数（核心概念）](../../../concept/核心概念/15-导数.md)

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845