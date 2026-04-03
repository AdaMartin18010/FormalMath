---
msc_primary: "00A99"
msc_secondary: ['00-XX', '03B35', '68V20']
mathlib4_version: "v4.29.0"
last_updated: "2026-04-03"
---

# 形式化证明

**最后更新**: 2026年4月3日
**Mathlib4版本**: v4.29.0

---

## 📋 目录概述

形式化证明系统、定理证明器，以及与Mathlib4的深度对齐文档和代码示例。

---

## 📁 目录结构

### 核心文档

| 文档 | 描述 |
|-----|------|
| [00-Mathlib4概念映射索引.md](00-Mathlib4概念映射索引.md) | 数学概念与Mathlib4代码的完整映射 |
| [00-从FormalMath到Mathlib4学习路径.md](00-从FormalMath到Mathlib4学习路径.md) | 从阅读文档到贡献Mathlib4的过渡指南 |
| [00-Mathlib4对齐状态报告.md](00-Mathlib4对齐状态报告.md) | 对齐工作进度报告 |

### 理论文档

| 文档 | 描述 |
|-----|------|
| [01-证明系统基础-深度扩展版.md](01-证明系统基础-深度扩展版.md) | 形式化证明基础理论 |
| [02-自动定理证明-深化版.md](02-自动定理证明-深化版.md) | 自动定理证明技术 |
| [03-模型检测-深化版.md](03-模型检测-深化版.md) | 模型检测方法 |
| [04-类型论与证明-深化版.md](04-类型论与证明-深化版.md) | 类型论基础 |
| [05-量子证明系统-深化版.md](05-量子证明系统-深化版.md) | 量子计算证明系统 |
| [06-机器学习证明系统-深化版.md](06-机器学习证明系统-深化版.md) | ML辅助证明 |
| [07-区块链证明系统-深化版.md](07-区块链证明系统-深化版.md) | 区块链形式化验证 |

### Lean4代码

#### 核心定理形式化

位于 [Lean4/](Lean4/) 目录，包含15个核心定理的完整形式化证明。

#### Mathlib4示例集

位于 [Lean4/00-Mathlib4示例集/](Lean4/00-Mathlib4示例集/) 目录：

| 示例文件 | 对应数学分支 | Mathlib4模块 |
|---------|-------------|-------------|
| [01-群论示例.lean](Lean4/00-Mathlib4示例集/01-群论示例.lean) | 群论 | `Mathlib.Algebra.Group.Basic` |
| [02-环论示例.lean](Lean4/00-Mathlib4示例集/02-环论示例.lean) | 环论 | `Mathlib.Algebra.Ring.Basic` |
| [03-数论示例.lean](Lean4/00-Mathlib4示例集/03-数论示例.lean) | 数论 | `Mathlib.NumberTheory.Primes` |
| [04-实分析示例.lean](Lean4/00-Mathlib4示例集/04-实分析示例.lean) | 实分析 | `Mathlib.Analysis.Calculus.Deriv` |
| [05-拓扑示例.lean](Lean4/00-Mathlib4示例集/05-拓扑示例.lean) | 拓扑学 | `Mathlib.Topology.Basic` |
| [06-线性代数示例.lean](Lean4/00-Mathlib4示例集/06-线性代数示例.lean) | 线性代数 | `Mathlib.Algebra.Module.LinearMap` |
| [07-集合论示例.lean](Lean4/00-Mathlib4示例集/07-集合论示例.lean) | 集合论 | `Mathlib.Data.Set.Basic` |
| [08-证明策略示例.lean](Lean4/00-Mathlib4示例集/08-证明策略示例.lean) | 证明策略 | `Mathlib.Tactic` |
| [09-类型论示例.lean](Lean4/00-Mathlib4示例集/09-类型论示例.lean) | 类型论 | `Mathlib.Init.Core` |
| [10-代数几何示例.lean](Lean4/00-Mathlib4示例集/10-代数几何示例.lean) | 代数几何 | `Mathlib.AlgebraicGeometry.Scheme` |

---

## 🚀 快速开始

### 1. 了解映射关系

阅读 [Mathlib4概念映射索引](00-Mathlib4概念映射索引.md) 了解FormalMath概念与Mathlib4代码的对应关系。

### 2. 学习路径

按照 [从FormalMath到Mathlib4学习路径](00-从FormalMath到Mathlib4学习路径.md) 设置环境并学习。

### 3. 运行示例

```bash
cd Lean4
lake update
lake build
lean 00-Mathlib4示例集/01-群论示例.lean
```

---

## 📊 Mathlib4对齐统计

| 数学分支 | FormalMath文档数 | 概念映射数 | 代码示例 |
|---------|----------------|-----------|---------|
| 基础数学 | 50+ | 10 | 1 |
| 代数结构 | 80+ | 15 | 3 |
| 分析学 | 40+ | 12 | 1 |
| 拓扑学 | 15+ | 8 | 1 |
| 数论 | 10+ | 8 | 1 |
| 几何学 | 15+ | 5 | 1 |
| 逻辑学 | 10+ | 4 | 1 |
| **总计** | **220+** | **62** | **10** |

---

## 🔗 外部资源

### 官方资源

- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)
- [Lean4官方文档](https://lean-lang.org/doc/)

### 学习资源

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

### 社区

- [Lean Zulip](https://leanprover.zulipchat.com/)

---

## 📈 贡献指南

### 添加新的概念映射

1. 在 [Mathlib4概念映射索引](00-Mathlib4概念映射索引.md) 中添加新条目
2. 提供FormalMath文档路径和Mathlib4模块路径
3. 添加代码示例验证映射关系

### 添加新的代码示例

1. 在 [Lean4/00-Mathlib4示例集/](Lean4/00-Mathlib4示例集/) 创建新的`.lean`文件
2. 遵循现有示例文件的结构
3. 确保代码在Lean 4.29.0 + Mathlib4 v4.29.0下可编译
4. 更新 [Lean4/README.md](Lean4/README.md)

---

**最后更新**: 2026年4月3日
