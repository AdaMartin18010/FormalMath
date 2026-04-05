---
msc_primary: 00A05
title: 样本文档：集合论基础
processed_at: '2026-04-05'
---
# 样本文档：集合论基础

## 定义

**定义 1.1** (集合). 集合是由确定的、互不相同的对象组成的整体。这些对象称为集合的元素。

我们用 $x \in A$ 表示 $x$ 是集合 $A$ 的元素，用 $x \notin A$ 表示 $x$ 不是集合 $A$ 的元素。

## 定理与证明

**定理 1.1** (空集的唯一性). 空集是唯一的。

**证明**: 假设存在两个空集 $\emptyset_1$ 和 $\emptyset_2$。根据空集的定义，对于任意元素 $x$，都有 $x \notin \emptyset_1$ 且 $x \notin \emptyset_2$。

因此，$\emptyset_1 \subseteq \emptyset_2$ 且 $\emptyset_2 \subseteq \emptyset_1$，所以 $\emptyset_1 = \emptyset_2$。

证毕。

## 例子

**例子 1.1**. 以下是一些常见集合的例子：

1. 自然数集：$\mathbb{N} = \{0, 1, 2, 3, \ldots\}$
2. 整数集：$\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, \ldots\}$
3. 有理数集：$\mathbb{Q} = \{\frac{p}{q} : p, q \in \mathbb{Z}, q \neq 0\}$

## 应用

集合论是现代数学的基础，在以下领域有广泛应用：
- 数学逻辑
- 抽象代数
- 拓扑学
- 计算机科学

## 参考

1. [集合论 - Wikipedia](https://zh.wikipedia.org/wiki/集合论)
2. Naive Set Theory, Paul Halmos
