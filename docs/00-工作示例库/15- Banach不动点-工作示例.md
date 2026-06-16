---
msc_primary: '00

  - 00A99 - 03B35 - 03B40'
title: Banach 不动点 - 工作示例
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
  wikipedia_url: https://en.wikipedia.org/wiki/Stefan_Banach
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Banach/
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
# Banach 不动点 - 工作示例

**类型**: 证明示例 **领域**: 泛函分析 **难度**: L2 **前置知识**: 完备度量空间、压缩映射
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 压缩映射在完备空间中存在唯一不动点 |
| **领域** | 泛函分析 |
| **MSC** | 47H10（不动点定理） |

---

## 题目

设 \((X,d)\) 完备，\(T : X \to X\) 满足 \(d(Tx,Ty) \leq k d(x,y)\)（\(0 \leq k < 1\)）。证明 \(T\) 有唯一不动点。

---

## 完整解答

**步骤 1**：任取 \(x_0\)，令 \(x_{n+1}=Tx_n\)。则 \(d(x_{n+1},x_n) \leq k^n d(x_1,x_0)\)，故 \(\sum d(x_{n+1},x_n)\) 收敛，\(\{x_n\}\) 为 Cauchy 列，收敛于某 \(x \in X\)。
**步骤 2**：由 \(T\) 连续（Lipschitz），\(Tx = \lim Tx_n = \lim x_{n+1} = x\)，故 \(x\) 为不动点。若 \(x,y\) 均为不动点，则 \(d(x,y)=d(Tx,Ty) \leq k d(x,y)\)，得 \(d(x,y)=0\)，唯一。

---

**文档状态**: ✅ 完成 **最后更新**: 2026年2月2日

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845