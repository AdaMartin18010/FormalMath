---
msc_primary: '00

  - 03B20 - 00A99 - 26A42'
title: Rolle 定理证明 - 工作示例
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
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=03B20
---
# Rolle 定理证明 - 工作示例

**类型**: 证明示例
**领域**: 实分析
**难度**: L1
**前置知识**: 连续、可导、极值
**创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **命题** | Rolle 定理：\(f(a)=f(b)\) 且可导则存在 \(c\in(a,b)\) 使 \(f'(c)=0\) |
| **领域** | 分析学 / 微积分 |
| **MSC** | 26A24（导数） |
| **相关概念** | [导数](../../../concept/核心概念/15-导数.md)、[连续](../../../concept/核心概念/14-连续.md) |

---

## 命题

**Rolle 定理**：设 \(f\) 在 \([a,b]\) 上连续、在 \((a,b)\) 内可导，且 \(f(a)=f(b)\)，则存在 \(c \in (a,b)\) 使得 \(f'(c)=0\)。

---

## 完整证明（工作示例）

**步骤 1**：若 \(f\) 在 \([a,b]\) 上为常数，则对任意 \(c\in(a,b)\) 有 \(f'(c)=0\)，结论成立。

**步骤 2**：若 \(f\) 非常数，由极值定理，\(f\) 在 \([a,b]\) 上取得最大值 \(M\) 与最小值 \(m\)，且 \(M>m\)。因 \(f(a)=f(b)\)，至少有一个最值在 \((a,b)\) 内取得，记为 \(f(c)\)，\(c\in(a,b)\)。

**步骤 3**：\(c\) 为内点极值且 \(f\) 在 \(c\) 处可导，故 \(f'(c)=0\)（Fermat 引理：内点极值点处导数为 0）。

---

## 关键步骤说明

- **思路**：常数情形直接；非常数时由最值定理得内点极值，再由可导得 \(f'(c)=0\)。
- **应用**：中值定理、不等式证明的常用引理。

---

## 相关概念链接

- [导数（核心概念）](../../../concept/核心概念/15-导数.md)

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845