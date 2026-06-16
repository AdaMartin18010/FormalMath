---
msc_primary: '00

  - 00A99'
title: 连续映射思维导图
processed_at: '2026-04-05'
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/function
  wikipedia_url: https://en.wikipedia.org/wiki/Function_(mathematics)
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E6%98%A0%E5%B0%84
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q11348
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
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 连续映射思维导图

## 概述
连续映射是拓扑学中保持拓扑结构的映射，是研究拓扑空间之间关系的核心工具。

## 思维导图

```mermaid
mindmap
  root((连续映射<br/>Continuous Map))
    定义
      ε-δ定义
        度量空间
      开集原像
        开集的原像为开集
      邻域定义
        像点邻域包含像的邻域
      闭集原像
        闭集的原像为闭集
      序列收敛
        序列像收敛
    连续性类型
      点连续
        单点处的连续性
      全局连续
        每点都连续
      一致连续
        度量空间
        δ不依赖于点
      Lipschitz连续
        有Lipschitz常数
      同胚
        双射+双向连续
    诱导拓扑
      初始拓扑
        由映射族诱导
        使映射连续的最粗拓扑
      最终拓扑
        由映射诱导
        使映射连续的最细拓扑
    连续映射的性质
      保持紧致性
      保持连通性
      保持道路连通性
      复合保持连续
    重要映射
      嵌入
        同胚于子空间
      商映射
        满射+开集判定
      覆叠映射
        局部同胚
      纤维丛投影
    同伦
      同伦等价
        连续形变
      收缩核
        形变到子空间
      形变收缩
        更强的收缩
    映射空间
      紧开拓扑
        函数空间拓扑
      一致收敛拓扑
        度量空间
      紧收敛拓扑

```

## 核心要点

| 连续性类型 | 条件 | 关系 |
|-----------|------|------|
| **连续** | 开集原像为开集 | 最一般 |
| **一致连续** | ∀ε>0, ∃δ>0 | 强于连续 |
| **Lipschitz** | d(f(x),f(y))≤Ld(x,y) | 强于一致连续 |
| **同胚** | 双射+双向连续 | 拓扑等价 |

## 连续性等价条件

对于映射 $f: X \to Y$，以下等价：
1. $f$ 连续
2. 任意开集 $V \subset Y$，$f^{-1}(V)$ 开
3. 任意闭集 $F \subset Y$，$f^{-1}(F)$ 闭
4. 任意 $A \subset X$，$f(\bar{A}) \subset \overline{f(A)}$

## 关联概念
- [拓扑空间](./topology-topological-space.md)
- [同伦论](./algebraic-homotopy.md)
- [纤维丛](./algebraic-fiber-bundle.md)

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845