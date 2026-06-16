---
msc_primary: '00

  - 00A99 - 16A99 - 52A99'
title: Jordan 标准形 - 工作示例
processed_at: '2026-04-05'
references:
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
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
# Jordan 标准形 - 工作示例

**类型**: 计算示例
**领域**: 线性代数
**难度**: L2
**前置知识**: 特征值、特征向量、广义特征空间
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 求矩阵的 Jordan 标准形与过渡矩阵 |
| **领域** | 代数结构 / 线性代数 |
| **MSC** | 15A21（标准形） |
| **相关概念** | Jordan 块、广义特征向量 |

---

## 题目

求 \(A = \begin{pmatrix} 2 & 1 \\ 0 & 2 \end{pmatrix}\) 的 Jordan 标准形及可逆矩阵 \(P\) 使 \(P^{-1}AP\) 为 Jordan 形。

---

## 完整解答（工作示例）

**步骤 1**：特征多项式 \(p_A(t) = (t-2)^2\)，特征值 \(\lambda=2\)（代数重数 2）。\(\mathrm{rank}(A-2I) = 1\)，故几何重数为 \(2-1=1\)，仅一个 Jordan 块，Jordan 形为 \(J = \begin{pmatrix} 2 & 1 \\ 0 & 2 \end{pmatrix}\)（即 \(A\) 本身已是 Jordan 形）。

**步骤 2**：取 \(v\) 为 \((A-2I)\) 的非零列（如 \((1,0)^T\)），\(w\) 满足 \((A-2I)w = v\)（如 \(w = (0,1)^T\)）。则 \(P = [w \mid v]\) 或 \([v \mid w]\) 依约定，\(P^{-1}AP = J\)。取 \(P = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}\)，则 \(AP = PJ\)，即 \(P^{-1}AP = J\)。

---

**文档状态**: ✅ 完成
**最后更新**: 2026年2月2日

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845