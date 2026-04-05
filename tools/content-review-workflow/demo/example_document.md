---
concept_id: MATH.ALG.GROUP.001
concept_name: 群 (Group)
category: 代数学
subcategory: 群论
created_date: 2024-01-15
author: demo_author
title: 群 (Group)
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 群 (Group)

## 定义

**群** (Group) 是代数学中的基本概念，是一个配备了二元运算的集合，满足特定的公理。

### 群的公理

设 $G$ 是一个非空集合，$\cdot$ 是 $G$ 上的二元运算。如果满足以下条件，则称 $(G, \cdot)$ 为一个**群**：

1. **封闭性**: 对于任意 $a, b \in G$，有 $a \cdot b \in G$
2. **结合律**: 对于任意 $a, b, c \in G$，有 $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
3. **单位元**: 存在 $e \in G$，使得对于任意 $a \in G$，有 $e \cdot a = a \cdot e = a$
4. **逆元**: 对于任意 $a \in G$，存在 $b \in G$，使得 $a \cdot b = b \cdot a = e$

## 例子

### 例子 1: 整数加法群

$(\mathbb{Z}, +)$ 是一个群，其中：
- 单位元是 $0$
- $n$ 的逆元是 $-n$

### 例子 2: 非零有理数乘法群

$(\mathbb{Q}^*, \times)$ 是一个群，其中：
- 单位元是 $1$
- $q$ 的逆元是 $\frac{1}{q}$

## 性质

群具有以下基本性质：

- 单位元是唯一的
- 每个元素的逆元是唯一的
- 消去律成立

## 参见

- [半群](semigroup.md)
- [环](ring.md)
- [域](field.md)

## 参考文献

1. Dummit, D. S., & Foote, R. M. (2004). Abstract Algebra. Wiley.
2. Artin, M. (2011). Algebra. Pearson.
