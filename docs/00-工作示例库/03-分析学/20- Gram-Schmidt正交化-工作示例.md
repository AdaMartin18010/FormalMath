---
msc_primary: '00

  - 00A99 - 16A99 - 00A99'
title: Gram–Schmidt 正交化 - 工作示例
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
# Gram–Schmidt 正交化 - 工作示例

**类型**: 计算示例
**领域**: 线性代数
**难度**: L1
**前置知识**: 内积、正交、线性无关
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | Gram–Schmidt 正交化计算 |
| **领域** | 代数结构 / 线性代数 |
| **MSC** | 15A63（正交化） |
| **相关概念** | 内积、正交投影、标准正交基 |

---

## 题目

在 \(\mathbb{R}^3\) 上带标准内积。将 \(v_1=(1,1,0)\)，\(v_2=(1,0,1)\)，\(v_3=(0,1,1)\) 正交化并单位化。

---

## 完整解答（工作示例）

**步骤 1**：\(u_1 = v_1 = (1,1,0)\)，\(\|u_1\|^2 = 2\)，\(e_1 = u_1/\sqrt{2}\)。

**步骤 2**：\(u_2 = v_2 - \frac{\langle v_2,u_1\rangle}{\|u_1\|^2}u_1 = (1,0,1) - \frac{1}{2}(1,1,0) = (1/2,-1/2,1)\)。\(\|u_2\|^2 = 1/4+1/4+1 = 3/2\)，\(e_2 = u_2/\sqrt{3/2}\)。

**步骤 3**：\(u_3 = v_3 - \frac{\langle v_3,u_1\rangle}{\|u_1\|^2}u_1 - \frac{\langle v_3,u_2\rangle}{\|u_2\|^2}u_2\)。\(\langle v_3,u_1\rangle = 1\)，\(\langle v_3,u_2\rangle = -1/2+1 = 1/2\)。得 \(u_3 = (-2/3, -2/3, 2/3)\)，单位化得 \(e_3\)。

---

**文档状态**: ✅ 完成  
**最后更新**: 2026年2月2日

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845