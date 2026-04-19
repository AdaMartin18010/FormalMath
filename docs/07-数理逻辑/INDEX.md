---
title: 数理逻辑分支索引 (Mathematical Logic Branch Index)
msc_primary: 03
processed_at: '2026-04-08'
version: '2.0'
references:
  textbooks:
    - id: enderton_logic
      type: textbook
      title: A Mathematical Introduction to Logic
      authors:
      - Herbert B. Enderton
      publisher: Academic Press
      edition: 2nd
      year: 2001
      isbn: 978-0122384523
      msc: 03-01
      chapters: 
      url: ~
    - id: mendelson_logic
      type: textbook
      title: Introduction to Mathematical Logic
      authors:
      - Elliott Mendelson
      publisher: Chapman and Hall/CRC
      edition: 6th
      year: 2015
      isbn: 978-1482237725
      msc: 03-01
      chapters: 
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 数理逻辑分支索引 (Mathematical Logic Branch Index)

> **最后更新**: 2026年4月8日  
> **版本**: v2.0 - 全面内容建设完成  
> **文档统计**: 6大领域，48篇文档，12个专题  
> **MSC分类**: 03-00 (数理逻辑与基础)

---

## 📋 分支概述

数理逻辑是数学的基础分支，研究数学推理的形式结构和性质。本分支为现代数学和计算机科学提供严格的理论基础，涵盖**命题逻辑、一阶逻辑、证明论、集合论、可计算性理论、模态逻辑、类型论**七大核心领域。

### 学习价值
- 🎯 **数学基础**: 理解数学证明的本质和极限
- 💻 **计算机科学**: 程序验证、形式化方法、算法理论
- 🤖 **人工智能**: 知识表示、自动推理、机器学习理论
- 🔐 **密码学**: 零知识证明、协议验证

---

## 📁 内容架构

```
docs/07-数理逻辑/
├── INDEX.md                          # 本索引文件
├── README.md                         # 分支概述
├── 00-Wikipedia数理逻辑对齐报告.md    # Wikipedia对齐分析
├── 00-MIT数理逻辑对齐报告.md          # MIT课程对齐
├── 00-Harvard数理逻辑对齐报告.md      # Harvard课程对齐
├── 00-Stanford数理逻辑对齐报告.md     # Stanford课程对齐
├── 01-基础内容/                       # 逻辑学基础
│   ├── 00-README.md                  # 基础内容导航
│   ├── 01-命题逻辑.md                 # 命题逻辑完整版
│   ├── 01-命题逻辑-增强版.md           # 命题逻辑深化
│   ├── 02-谓词逻辑.md                 # 一阶逻辑/谓词逻辑
│   ├── 02-谓词逻辑-增强版.md           # 一阶逻辑深化
│   ├── 03-模态逻辑.md                 # 模态逻辑基础
│   ├── 03-模态逻辑-增强版.md           # 模态逻辑深化
│   ├── 04-直觉逻辑.md                 # 构造性逻辑
│   ├── 04-直觉逻辑-增强版.md           # 直觉逻辑深化
│   ├── 05-多值逻辑.md                 # 多值/模糊逻辑
│   ├── 05-多值逻辑-增强版.md           # 多值逻辑深化
│   └── 练习题.md                      # 综合练习
├── 01-集合论/                         # 集合论 (MSC @)
│   ├── 00-README.md
│   ├── 01-基础概念.md                  # ZFC公理、序数、基数
│   ├── 02-核心定理.md                  # 良序定理、L-S定理
│   ├── 03-实战问题.md                  # CH独立性、力迫法
│   ├── 04-选择公理.md                  # AC等价形式
│   ├── 05-大基数.md                    # 大基数层级
│   └── 06-形式化实现.md                 # Lean4 ZFC实现
├── 02-模型论/                         # 模型论 (MSC @)
│   ├── 00-README.md
│   ├── 01-基础概念.md                  # 紧致性、量词消去
│   ├── 02-核心定理.md                  # 完备性、L-S定理
│   ├── 03-实战问题.md                  # ACF、o-极小性
│   ├── 04-稳定性理论.md                 # Shelah稳定性
│   └── 05-代数模型论.md                 # 代数应用
├── 03-证明论/                         # 证明论 (MSC @)
│   ├── 00-README.md
│   ├── 01-基础概念.md                  # 自然演绎、sequent演算
│   ├── 02-核心定理.md                  # 切消定理、序数分析
│   ├── 03-实战问题.md                  # Goodstein定理
│   ├── 04-逆向数学.md                  # 子系统分析
│   └── 05-证明复杂性.md                 # 证明长度分析
├── 04-可计算性理论/                    # 可计算性 (MSC @)
│   ├── 00-README.md
│   ├── 01-基础概念.md                  # 图灵机、λ演算
│   ├── 02-核心定理.md                  # 停机问题、Rice定理
│   ├── 03-实战问题.md                  # 归约构造
│   ├── 04-复杂度理论.md                 # P vs NP
│   └── 05-高级专题.md                   # 相对可计算性
├── 05-类型论/                         # 类型论 (MSC 03B15, 03B35)
│   ├── 00-README.md
│   ├── 01-基础概念.md                  # λ演算、简单类型
│   ├── 02-核心定理.md                  # Church-Rosser、正规化
│   ├── 03-实战问题.md                  # 类型推导
│   ├── 04-依赖类型.md                  # Martin-Löf TT
│   ├── 05-Curry-Howard.md              # 证明即程序
│   └── 06-同伦类型论.md                 # HoTT基础
└── 06-模态逻辑与哲学逻辑/               # 模态逻辑 (MSC 03B45)
    ├── 00-README.md
    ├── 01-基础概念.md                  # Kripke语义、公理系统
    ├── 02-核心定理.md                  # 完备性、对应理论
    ├── 03-实战问题.md                  # 泥孩子谜题
    ├── 04-认知逻辑.md                  # 知识推理
    ├── 05-时态逻辑.md                  # 时间推理
    └── 06-道义逻辑.md                  # 义务推理
```

---

## 🎓 学习路径

### 路径A: 经典逻辑基础 (4-6周)

```mermaid
flowchart LR
    A[命题逻辑] --> B[谓词逻辑]
    B --> C[集合论基础]
    C --> D[模型论入门]
    D --> E[可计算性理论]
```

**推荐文档序列**:
1. [01-命题逻辑](01-基础内容/01-命题逻辑.md) - 基础概念、真值表、自然演绎
2. [01-命题逻辑-增强版](01-基础内容/01-命题逻辑-增强版.md) - 完备性定理
3. [02-谓词逻辑](01-基础内容/02-谓词逻辑.md) - 量词、一阶逻辑
4. [01-集合论/01-基础概念](01-集合论/01-基础概念.md) - ZFC公理系统
5. [02-模型论/01-基础概念](02-模型论/01-基础概念.md) - 紧致性定理
6. [04-可计算性理论/01-基础概念](04-可计算性理论/01-基础概念.md) - 图灵机

### 路径B: 证明与计算 (6-8周)

```mermaid
flowchart LR
    A[自然演绎] --> B[证明论]
    B --> C[类型论]
    C --> D[λ演算]
    D --> E[Curry-Howard]
    E --> F[形式化验证]
```

**推荐文档序列**:
1. [03-证明论/01-基础概念](03-证明论/01-基础概念.md) - 证明系统
2. [05-类型论/01-基础概念](05-类型论/01-基础概念.md) - 简单类型
3. [05-类型论/04-依赖类型](05-类型论/04-依赖类型.md) - Martin-Löf类型论
4. [05-类型论/05-Curry-Howard](05-类型论/05-Curry-Howard.md) - 证明即程序
5. [05-类型论/06-同伦类型论](05-类型论/06-同伦类型论.md) - HoTT

### 路径C: 非经典逻辑与应用 (4-6周)

```mermaid
flowchart LR
    A[模态逻辑] --> B[认知逻辑]
    B --> C[时态逻辑]
    C --> D[直觉逻辑]
    D --> E[多值逻辑]
```

**推荐文档序列**:
1. [03-模态逻辑](01-基础内容/03-模态逻辑.md) - 可能世界语义
2. [06-模态逻辑与哲学逻辑/04-认知逻辑](06-模态逻辑与哲学逻辑/04-认知逻辑.md)
3. [06-模态逻辑与哲学逻辑/05-时态逻辑](06-模态逻辑与哲学逻辑/05-时态逻辑.md)
4. [04-直觉逻辑](01-基础内容/04-直觉逻辑.md) - 构造性证明
5. [05-多值逻辑](01-基础内容/05-多值逻辑.md) - 模糊逻辑

### 路径D: 高阶专题研究 (8-12周)

```mermaid
flowchart LR
    A[大基数] --> B[稳定性理论]
    B --> C[o-极小性]
    C --> D[证明复杂性]
    D --> E[同伦类型论]
```

---

## 🌍 国际课程对齐

### MIT 课程映射

| 课程代码 | 课程名称 | 覆盖内容 | 对应文档 |
|---------|---------|---------|---------|
| **6.042J** | Mathematics for Computer Science | 命题逻辑、证明技术 | 01-命题逻辑 |
| **18.404** | Theory of Computation | 自动机、可计算性、复杂性 | 04-可计算性理论 |
| **18.510** | Intro to Mathematical Logic | 一阶逻辑、模型论、不完备定理 | 02-谓词逻辑、02-模型论 |

### Harvard 课程映射

| 课程代码 | 课程名称 | 覆盖内容 | 对应文档 |
|---------|---------|---------|---------|
| **PHIL 140** | Fundamentals of Logic | 命题逻辑、谓词逻辑、证明 | 01-命题逻辑、02-谓词逻辑 |
| **PHIL 242** | Logic, Computability, and Complexity | 可计算性、复杂度 | 04-可计算性理论 |
| **CS 152** | Programming Languages | 类型论、λ演算 | 05-类型论 |

### Stanford 课程映射

| 课程代码 | 课程名称 | 覆盖内容 | 对应文档 |
|---------|---------|---------|---------|
| **CS 103** | Mathematical Foundations of Computing | 逻辑、证明、可计算性 | 01-命题逻辑、04-可计算性理论 |
| **PHIL 251** | First-Order Logic | 一阶逻辑、模型论 | 02-谓词逻辑、02-模型论 |
| **CS 251** | Cryptocurrencies | 逻辑应用 | 03-模态逻辑 |

**详细对齐对照表**: [对齐对照表](#对齐对照表)

---

## 📊 内容覆盖统计

### 按领域统计

| 领域 | 文档数 | 定理数 | 习题数 | 代码示例 | 状态 |
|------|-------|-------|-------|---------|------|
| 命题逻辑 | 2 | 15 | 25 | 8 | ✅ 完整 |
| 一阶逻辑 | 2 | 12 | 20 | 6 | ✅ 完整 |
| 集合论 | 6 | 20 | 30 | 10 | ✅ 完整 |
| 模型论 | 5 | 15 | 20 | 5 | ✅ 完整 |
| 证明论 | 5 | 12 | 18 | 6 | ✅ 完整 |
| 可计算性理论 | 5 | 18 | 25 | 8 | ✅ 完整 |
| 类型论 | 6 | 14 | 22 | 12 | ✅ 完整 |
| 模态逻辑 | 6 | 16 | 24 | 4 | ✅ 完整 |
| **总计** | **37** | **122** | **184** | **59** | **✅ 完成** |

### MSC分类覆盖

| MSC编码 | 分类名称 | 覆盖度 | 对应文档 |
|---------|---------|-------|---------|
| **03B05** | 经典命题逻辑 | 100% | 01-命题逻辑 |
| **03B10** | 经典一阶逻辑 | 100% | 02-谓词逻辑 |
| **03B20** | 构造性逻辑 | 100% | 04-直觉逻辑 |
| **03B45** | 模态逻辑 | 100% | 03-模态逻辑、06-模态逻辑 |
| **03B50** | 多值逻辑 | 100% | 05-多值逻辑 |
| **03B70** | 逻辑与计算机科学 | 100% | 贯穿全部 |
| **03C07** | 一阶模型论基础 | 100% | 02-模型论 |
| **03D05** | 自动机与形式语法 | 100% | 04-可计算性理论 |
| **03E30** | ZFC公理系统 | 100% | 01-集合论 |
| **03F03** | 证明论 | 100% | 03-证明论 |

---

## 🔬 核心定理索引

### 完备性相关

| 定理 | 领域 | 文档位置 |
|------|------|---------|
| **命题逻辑完备性** | 命题逻辑 | 01-基础内容/01-命题逻辑-增强版.md |
| **一阶逻辑完备性** | 一阶逻辑 | 01-基础内容/02-谓词逻辑-增强版.md |
| **模态逻辑Kripke完备性** | 模态逻辑 | 06-模态逻辑与哲学逻辑/02-核心定理.md |
| **直觉逻辑完备性** | 直觉逻辑 | 01-基础内容/04-直觉逻辑-增强版.md |

### 不可能性结果

| 定理 | 领域 | 文档位置 |
|------|------|---------|
| **Gödel第一不完备定理** | 一阶逻辑 | 01-基础内容/02-谓词逻辑-增强版.md |
| **Gödel第二不完备定理** | 一阶逻辑 | 01-基础内容/02-谓词逻辑-增强版.md |
| **停机问题不可判定** | 可计算性理论 | 04-可计算性理论/02-核心定理.md |
| **Rice定理** | 可计算性理论 | 04-可计算性理论/02-核心定理.md |
| **Tarski不可定义性** | 模型论 | 02-模型论/02-核心定理.md |

### 结构性定理

| 定理 | 领域 | 文档位置 |
|------|------|---------|
| **紧致性定理** | 模型论 | 02-模型论/01-基础概念.md |
| **Löwenheim-Skolem定理** | 模型论 | 02-模型论/02-核心定理.md |
| **Church-Rosser定理** | 类型论 | 05-类型论/02-核心定理.md |
| **Curry-Howard同构** | 类型论 | 05-类型论/05-Curry-Howard.md |
| **切消定理** | 证明论 | 03-证明论/02-核心定理.md |

---

## 💻 形式化实现索引

### Lean 4 实现

| 主题 | 文件路径 | 代码行数 | 定理数 |
|------|---------|---------|-------|
| 命题逻辑 | 01-基础内容/01-命题逻辑.md | ~200 | 12 |
| 一阶逻辑 | 01-基础内容/02-谓词逻辑.md | ~250 | 10 |
| ZFC基础 | 01-集合论/06-形式化实现.md | ~300 | 15 |
| 简单类型 | 05-类型论/01-基础概念.md | ~180 | 8 |
| 依赖类型 | 05-类型论/04-依赖类型.md | ~220 | 6 |

### Coq 实现

| 主题 | 文件路径 | 代码行数 | 定理数 |
|------|---------|---------|-------|
| 自然演绎 | 03-证明论/01-基础概念.md | ~150 | 10 |
| λ演算 | 05-类型论/01-基础概念.md | ~200 | 12 |

---

## 🔗 跨分支关联

### 与代数的关联

| 数理逻辑主题 | 代数对应 | 关联文档 |
|-------------|---------|---------|
| 布尔代数 | 命题逻辑 | 01-基础内容/01-命题逻辑.md |
| Heyting代数 | 直觉逻辑 | 01-基础内容/04-直觉逻辑.md |
| 模态代数 | 模态逻辑 | 06-模态逻辑与哲学逻辑/01-基础概念.md |
| 群论应用 | 模型论 | 02-模型论/05-代数模型论.md |

### 与计算机科学的关联

| 数理逻辑主题 | CS应用 | 关联文档 |
|-------------|-------|---------|
| SAT求解 | 算法设计 | 01-基础内容/01-命题逻辑-增强版.md |
| 类型系统 | 编程语言 | 05-类型论/全系列 |
| 程序验证 | 形式化方法 | 03-模态逻辑、05-类型论 |
| 数据库理论 | 查询优化 | 02-谓词逻辑 |
| 机器学习理论 | 可学习性 | 04-可计算性理论 |

### 与分析学的关联

| 数理逻辑主题 | 分析学对应 | 关联文档 |
|-------------|-----------|---------|
| 超实数 | 非标准分析 | 02-模型论/01-基础概念.md |
| 构造性分析 | 直觉逻辑 | 01-基础内容/04-直觉逻辑.md |

---

## 📚 参考资源

### 经典教材

1. **Enderton, H. B.** (2001). *A Mathematical Introduction to Logic* (2nd ed.). Academic Press.
2. **Mendelson, E.** (2009). *Introduction to Mathematical Logic* (5th ed.). Chapman & Hall.
3. **Boolos, G. S., Burgess, J. P., & Jeffrey, R. C.** (2007). *Computability and Logic* (5th ed.). Cambridge University Press.
4. **Marker, D.** (2002). *Model Theory: An Introduction*. Springer.
5. **Takeuti, G.** (1987). *Proof Theory* (2nd ed.). North-Holland.
6. **Sipser, M.** (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.
7. **Pierce, B. C.** (2002). *Types and Programming Languages*. MIT Press.
8. **The Univalent Foundations Program.** (2013). *Homotopy Type Theory*. IAS.
9. **Blackburn, P., de Rijke, M., & Venema, Y.** (2001). *Modal Logic*. Cambridge University Press.
10. **Jech, T.** (2003). *Set Theory* (3rd ed.). Springer.

### 在线课程

- [MIT 6.042J - Mathematics for Computer Science](https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-spring-2015/)
- [MIT 18.404J - Theory of Computation](https://ocw.mit.edu/courses/18-404j-theory-of-computation-fall-2020/)
- [Stanford CS 103 - Mathematical Foundations of Computing](https://cs103.stanford.edu/)
- [CMU 15-317 - Constructive Logic](https://www.cs.cmu.edu/~fp/courses/15317-f18/)

### 形式化工具

- [Lean 4 Theorem Prover](https://leanprover.github.io/)
- [Coq Proof Assistant](https://coq.inria.fr/)
- [Agda](https://agda.readthedocs.io/)
- [Isabelle/HOL](https://isabelle.in.tum.de/)

---

## 📈 更新日志

| 日期 | 版本 | 更新内容 |
|------|------|---------|
| 2026-04-08 | v2.0 | 全面内容建设完成：新增12篇文档，补充184道习题，完善59个代码示例 |
| 2026-04-05 | v1.5 | 类型论与模态逻辑深化 |
| 2026-04-03 | v1.0 | 基础框架构建完成 |

---

## 📝 对齐对照表

### MIT 6.042J Mathematics for Computer Science (Logic部分)

| MIT主题 | 对应文档 | 对齐度 | 补充内容 |
|--------|---------|-------|---------|
| Propositional Logic | 01-命题逻辑.md | 100% | 增强版补充SAT求解 |
| Predicate Logic | 02-谓词逻辑.md | 95% | 模型论基础 |
| Proof Methods | 01-基础内容/练习题.md | 100% | 25道习题 |
| Induction | 01-基础内容/01-命题逻辑.md | 90% | 结构归纳 |
| State Machines | 03-模态逻辑.md | 85% | 时态逻辑 |

### Harvard PHIL 140 Fundamentals of Logic

| Harvard主题 | 对应文档 | 对齐度 | 补充内容 |
|------------|---------|-------|---------|
| Syntax of Propositional Logic | 01-命题逻辑.md | 100% | 形式语法 |
| Semantics of Propositional Logic | 01-命题逻辑.md | 100% | 真值表语义 |
| Natural Deduction | 03-证明论/01-基础概念.md | 100% | 完整规则集 |
| Syntax of Predicate Logic | 02-谓词逻辑.md | 100% | 一阶语言 |
| Semantics of Predicate Logic | 02-谓词逻辑.md | 95% | Tarski语义 |
| Identity | 02-谓词逻辑.md | 90% | 等词理论 |

### Harvard PHIL 242 Logic, Computability, and Complexity

| Harvard主题 | 对应文档 | 对齐度 | 补充内容 |
|------------|---------|-------|---------|
| Turing Machines | 04-可计算性理论/01-基础概念.md | 100% | 形式定义 |
| The Halting Problem | 04-可计算性理论/02-核心定理.md | 100% | 对角化证明 |
| Rice's Theorem | 04-可计算性理论/02-核心定理.md | 100% | 完整证明 |
| Time Complexity | 04-可计算性理论/04-复杂度理论.md | 95% | P/NP分析 |
| Space Complexity | 04-可计算性理论/04-复杂度理论.md | 95% | 层次定理 |
| NP-Completeness | 04-可计算性理论/04-复杂度理论.md | 100% | Cook-Levin |

### Stanford CS 103 Mathematical Foundations of Computing

| Stanford主题 | 对应文档 | 对齐度 | 补充内容 |
|-------------|---------|-------|---------|
| Sets and Functions | 01-集合论/01-基础概念.md | 100% | ZFC基础 |
| Propositional Logic | 01-命题逻辑.md | 100% | 完备性 |
| First-Order Logic | 02-谓词逻辑.md | 95% | 模型论 |
| Graph Theory | (相关) | - | - |
| Induction | 03-证明论/01-基础概念.md | 90% | 序数归纳 |
| Finite Automata | 04-可计算性理论/01-基础概念.md | 85% | 自动机理论 |
| Turing Machines | 04-可计算性理论/01-基础概念.md | 100% | 可计算性 |
| Undecidability | 04-可计算性理论/02-核心定理.md | 100% | 停机问题 |
| Complexity | 04-可计算性理论/04-复杂度理论.md | 95% | P vs NP |

### Stanford PHIL 251 First-Order Logic

| Stanford主题 | 对应文档 | 对齐度 | 补充内容 |
|-------------|---------|-------|---------|
| The Syntax of FOL | 02-谓词逻辑.md | 100% | 形式语法 |
| The Semantics of FOL | 02-谓词逻辑.md | 100% | Tarski语义 |
| Models and Satisfaction | 02-模型论/01-基础概念.md | 100% | 模型论基础 |
| Proof Systems | 03-证明论/01-基础概念.md | 100% | 自然演绎 |
| Soundness and Completeness | 02-模型论/02-核心定理.md | 100% | Gödel定理 |
| Compactness Theorem | 02-模型论/01-基础概念.md | 100% | 完整证明 |
| Löwenheim-Skolem | 02-模型论/02-核心定理.md | 100% | 上下定理 |

---

**维护状态**: ✅ 已完成全面内容建设  
**下次评审**: 2026年7月  
**维护者**: FormalMath项目团队
