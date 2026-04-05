---
title: "类型论 (Type Theory)"
msc_primary: "03B15"
msc_secondary: ["03B38", "03B40", "03B70", "68N18", "68V20"]
processed_at: '2026-04-05'
---

# 类型论 (Type Theory)

## 模块概述

类型论是数学基础、逻辑学和计算机科学的交叉领域，为形式化证明和程序语言提供了统一框架。本模块涵盖λ演算、依赖类型、同伦类型论等核心主题。

## 内容导航

| 文档 | 主题 | 核心内容 |
|------|------|----------|
| [01-基础概念.md](./01-基础概念.md) | λ演算 | 简单类型、多态、System F |
| [01-基础概念.md](./01-基础概念.md) | 依赖类型 | Π类型、Σ类型、归纳类型 |
| [01-基础概念.md](./01-基础概念.md) | HoTT | 同一性类型、Univalence、高阶归纳类型 |
| [02-核心定理.md](./02-核心定理.md) | 核心定理 | Church-Rosser、强正规化、Univalence |
| [03-实战问题.md](./03-实战问题.md) | 应用问题 | Coq/Lean形式化、证明携带代码 |

## 学习路径

```

λ演算 → 简单类型 → 多态类型 → 依赖类型 → 归纳族 → HoTT

```

## 前置知识

- 一阶逻辑
- 证明论基础
- 范畴论（对HoTT有帮助）

## 关联分支

- **03-证明论**: Curry-Howard对应
- **04-可计算性理论**: 可计算性与类型
- **09-形式化证明**: Coq, Lean, Agda

## 参考文献

1. Pierce, B. C. *Types and Programming Languages* (2002)
2. Nederpelt, R., & Geuvers, H. *Type Theory and Formal Proof* (2014)
3. The Univalent Foundations Program. *Homotopy Type Theory* (2013)
4. Martin-Löf, P. *Intuitionistic Type Theory* (1984)
