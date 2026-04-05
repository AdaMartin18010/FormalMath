---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 🔍 搜索指南

> 如何高效地在 FormalMath-Enhanced 中找到你需要的内容

---

## 📑 目录

- [🔍 搜索指南](#-搜索指南)
  - [📑 目录](#目录)
  - [🎯 快速查找策略](#-快速查找策略)
    - [1. 确定搜索范围](#1-确定搜索范围)
    - [2. 使用导航索引](#2-使用导航索引)
    - [3. 查找决策树](#3-查找决策树)
  - [🔎 按内容类型搜索](#-按内容类型搜索)
    - [搜索 MSC 编码](#搜索-msc-编码)
    - [搜索定理注释](#搜索定理注释)
    - [搜索 IMO 题目](#搜索-imo-题目)
    - [搜索国际课程对齐](#搜索国际课程对齐)
    - [搜索 AI 形式化内容](#搜索-ai-形式化内容)
    - [搜索前沿专题](#搜索前沿专题)
  - [🔤 关键词搜索建议](#-关键词搜索建议)
    - [通用搜索技巧](#通用搜索技巧)
    - [分领域关键词](#分领域关键词)
      - [代数学](#代数学)
      - [分析学](#分析学)
      - [几何学](#几何学)
      - [数论](#数论)
    - [组合搜索](#组合搜索)
  - [🔗 交叉引用使用](#-交叉引用使用)
    - [文档内引用](#文档内引用)
    - [模块间引用](#模块间引用)
    - [引用示例](#引用示例)
  - [🚀 高级搜索技巧](#-高级搜索技巧)
    - [使用文件路径模式](#使用文件路径模式)
    - [使用 GitHub/GitLab 搜索](#使用-githubgitlab-搜索)
    - [使用 IDE 搜索](#使用-ide-搜索)
  - [❓ 常见问题](#-常见问题)
  - [🔗 相关索引](#-相关索引)

---

## 🎯 快速查找策略

### 1. 确定搜索范围

首先判断你要找的内容属于哪个模块：

| 内容类型 | 所在模块 | 快速入口 |
|----------|----------|----------|
| MSC 编码 | 01-MSC-Coding | [MSC 索引](./01-MSC-Coding/README.md) |
| 定理注释 | 02-Mathlib4-Annotations | [定理索引](./02-Mathlib4-Annotations/INDEX.md) |
| IMO 题目 | 03-IMO-Competition | [题目索引](./03-IMO-Competition/题目统计与索引.md) |
| 课程对齐 | 04-International-Alignment | [课程映射](./04-International-Alignment/README.md) |
| AI 形式化 | 05-AI-Formalization | [AI 总览](./05-AI-Formalization/00-README.md) |
| 前沿专题 | 06-Modern-Frontiers | [前沿总览](./06-Modern-Frontiers/00-现代数学前沿总览.md) |

### 2. 使用导航索引

我们提供了多个维度的索引文件：

- 🏷️ **按主题**: [BY-TOPIC.md](./BY-TOPIC.md) - 代数学、分析学、几何学、数论、拓扑学、组合数学
- 📊 **按难度**: [BY-LEVEL.md](./BY-LEVEL.md) - 入门级、中级、高级、研究级
- 🎓 **按路径**: [LEARNING-PATHS.md](./LEARNING-PATHS.md) - 代数路径、分析路径、几何路径、竞赛路径、形式化路径

### 3. 查找决策树

```
你想找什么？
│
├─ 特定定理/概念
│  ├─ 有 MSC 编码？ → 01-MSC-Coding
│  ├─ 有 Lean4 代码？ → 02-Mathlib4-Annotations
│  └─ IMO 相关？ → 03-IMO-Competition
│
├─ 学习课程/教材
│  └─ 04-International-Alignment
│
├─ 前沿研究/AI 工具
│  ├─ 数学前沿 → 06-Modern-Frontiers
│  └─ AI 形式化 → 05-AI-Formalization
│
└─ 快速参考
   └─ QUICK-REF.md
```

---

## 🔎 按内容类型搜索

### 搜索 MSC 编码

**场景**: 需要为数学文档标注 MSC 编码

**方法**:

1. 确定数学分支（代数/分析/几何/拓扑/基础）
2. 打开对应索引文件：
   - [01-基础数学-MSC索引.md](./01-MSC-Coding/01-基础数学-MSC索引.md)
   - [02-代数结构-MSC索引.md](./01-MSC-Coding/02-代数结构-MSC索引.md)
   - [03-分析学-MSC索引.md](./01-MSC-Coding/03-分析学-MSC索引.md)
   - [04-几何学-MSC索引.md](./01-MSC-Coding/04-几何学-MSC索引.md)
   - [05-拓扑学-MSC索引.md](./01-MSC-Coding/05-拓扑学-MSC索引.md)
3. 使用 Ctrl+F 搜索关键词
4. 参考 [99-示例文档-MSC标注格式.md](./01-MSC-Coding/99-示例文档-MSC标注格式.md) 了解标注格式

**常用编码速查**: 参见 [QUICK-REF.md#msc-编码速查](./QUICK-REF.md#msc-编码速查)

### 搜索定理注释

**场景**: 查找特定定理的 Mathlib4 教育注释

**方法**:

1. 打开 [02-Mathlib4-Annotations/INDEX.md](./02-Mathlib4-Annotations/INDEX.md)
2. 按领域浏览表格，或使用以下关键词搜索：

| 搜索关键词 | 对应内容 |
|------------|----------|
| "拉格朗日" / "Lagrange" | 拉格朗日定理 |
| "西罗" / "Sylow" | 西罗定理 |
| "柯西积分" / "Cauchy" | 柯西积分公式 |
| "留数" / "Residue" | 留数定理 |
| "谱定理" / "Spectral" | 谱定理 |
| "素数" / "Prime" | 素数定理 |
| "费马" / "Fermat" | 费马小定理 |

### 搜索 IMO 题目

**场景**: 查找特定 IMO 题目或相关主题

**方法**:

1. 打开 [03-IMO-Competition/题目统计与索引.md](./03-IMO-Competition/题目统计与索引.md)
2. 可按以下维度搜索：

| 维度 | 搜索示例 |
|------|----------|
| 年份 | "2007" "P5" |
| 领域 | "代数" "几何" "数论" "组合" |
| 难度 | "6分" "7分" |
| 技巧 | "Vieta" "Ravi" "Schur" |

1. 题目文件命名格式: `[年份]/Problem-[题号].md`
   - 示例: [2007/Problem-05.md](./03-IMO-Competition/2007/Problem-05.md)

### 搜索国际课程对齐

**场景**: 查找 FormalMath 与 MIT/Stanford/Harvard 课程的对应关系

**方法**:

1. 打开 [04-International-Alignment/README.md](./04-International-Alignment/README.md)
2. 按学校浏览：
   - MIT: [02-MIT-Course18-详细对照表.md](./04-International-Alignment/02-MIT-Course18-详细对照表.md)
   - Stanford: [03-Stanford-FOAG-章节对照.md](./04-International-Alignment/03-Stanford-FOAG-章节对照.md)
   - Harvard: [04-Harvard-课程映射.md](./04-International-Alignment/04-Harvard-课程映射.md)
3. 搜索课程代码或名称：
   - "18.725" (MIT 代数几何)
   - "Math 232br" (Harvard 凝聚层)
   - "FOAG" (Stanford 代数几何)

### 搜索 AI 形式化内容

**场景**: 查找 AI 形式化数学项目或工具

**方法**:

1. 打开 [05-AI-Formalization/00-README.md](./05-AI-Formalization/00-README.md)
2. 项目快速链接：

| 项目 | 关键词 | 文件 |
|------|--------|------|
| KELPS | 多语言、自动形式化 | [01-KELPS.md](./05-AI-Formalization/01-KELPS.md) |
| DeepSeek-Math | 大模型、数学推理 | [02-DeepSeek-Math.md](./05-AI-Formalization/02-DeepSeek-Math.md) |
| LeanAgent | 终身学习、证明器 | [03-LeanAgent.md](./05-AI-Formalization/03-LeanAgent.md) |
| IMO Lean | IMO、形式化库 | [04-IMO-Lean.md](./05-AI-Formalization/04-IMO-Lean.md) |
| AlphaProof | DeepMind、自动证明 | [05-AlphaProof.md](./05-AI-Formalization/05-AlphaProof.md) |

1. 代码示例: [07-Code-Examples.md](./05-AI-Formalization/07-Code-Examples.md)

### 搜索前沿专题

**场景**: 查找现代数学前沿研究内容

**方法**:

1. 打开 [06-Modern-Frontiers/00-现代数学前沿总览.md](./06-Modern-Frontiers/00-现代数学前沿总览.md)
2. 专题快速链接：

| 专题 | 关键词 | 文件 |
|------|--------|------|
| 凝聚数学 | Condensed、Scholze | [01-凝聚数学.md](./06-Modern-Frontiers/01-凝聚数学.md) |
| ∞-范畴论 | Infinity、Lurie | [02-无穷范畴论.md](./06-Modern-Frontiers/02-无穷范畴论.md) |
| 粗糙分析 | Rough Path、Lyons | [03-粗糙分析.md](./06-Modern-Frontiers/03-粗糙分析.md) |
| 科学机器学习 | SciML、PINN | [04-科学机器学习.md](./06-Modern-Frontiers/04-科学机器学习.md) |
| Langlands 纲领 | Langlands、表示论 | [05-Langlands纲领.md](./06-Modern-Frontiers/05-Langlands纲领.md) |
| 同伦类型论 | HoTT、Voevodsky | [06-同伦类型论.md](./06-Modern-Frontiers/06-同伦类型论.md) |

---

## 🔤 关键词搜索建议

### 通用搜索技巧

1. **中文关键词优先**: 大部分文档使用中文
2. **尝试英文术语**: 专业术语同时标注英文
3. **使用缩写**: 如 "MSC"、"IMO"、"FOAG"
4. **人名搜索**: "Scholze"、"Lurie"、"Voevodsky"

### 分领域关键词

#### 代数学

- 群论: "群"、"子群"、"同态"、"Sylow"、"Lagrange"
- 环论: "环"、"理想"、"素理想"、"诺特"
- 域论: "域扩张"、"Galois"、"代数闭域"

#### 分析学

- 实分析: "测度"、"积分"、"Lebesgue"、"收敛"
- 复分析: "全纯"、"解析"、"留数"、"Cauchy"
- 泛函: "Banach"、"Hilbert"、"算子"、"谱"

#### 几何学

- 微分几何: "流形"、"Riemann"、"曲率"、"测地线"
- 代数几何: "概形"、"层"、"凝聚"、"上同调"
- 拓扑: "同调"、"同伦"、"紧致"、"连通"

#### 数论

- 解析: "素数"、"ζ函数"、"L函数"、"Dirichlet"
- 代数: "类域论"、"理想类群"、"椭圆曲线"

### 组合搜索

使用多个关键词缩小范围：

- "2007 P5 Vieta" → 找到特定题目
- "MIT 18.725 概形" → 找到课程对应内容
- "Lean4 拉格朗日" → 找到定理形式化

---

## 🔗 交叉引用使用

### 文档内引用

每个文档都包含相关链接：

- **前置知识**: 需要先学习的内容
- **后续内容**: 可以进一步学习的内容
- **相关主题**: 横向关联的内容

### 模块间引用

```
MSC 编码 ────→ 定理注释 (通过主题关联)
    │
    ├───────→ IMO 题目 (通过主题关联)
    │
    └───────→ 国际课程 (通过课程大纲关联)

定理注释 ────→ AI 形式化 (通过 Lean4 代码)
    │
    └───────→ 前沿专题 (通过研究前沿)
```

### 引用示例

在 [BY-TOPIC.md](./BY-TOPIC.md) 中，每个主题都链接到：

- MSC 编码索引
- Mathlib4 定理注释
- IMO 相关题目

在 [LEARNING-PATHS.md](./LEARNING-PATHS.md) 中，每条路径都引用：

- 起始定理/概念
- 推荐课程
- 进阶专题

---

## 🚀 高级搜索技巧

### 使用文件路径模式

了解文件命名规律，可直接推断路径：

| 内容类型 | 路径模式 | 示例 |
|----------|----------|------|
| MSC 索引 | `01-MSC-Coding/XX-主题-MSC索引.md` | [02-代数结构-MSC索引.md](./01-MSC-Coding/02-代数结构-MSC索引.md) |
| 定理注释 | `02-Mathlib4-Annotations/领域/定理名.md` | [Algebra/lagrange-theorem.md](./02-Mathlib4-Annotations/Algebra/lagrange-theorem.md) |
| IMO 题目 | `03-IMO-Competition/年份/Problem-题号.md` | [2007/Problem-05.md](./03-IMO-Competition/2007/Problem-05.md) |
| 前沿专题 | `06-Modern-Frontiers/XX-专题名.md` | [01-凝聚数学.md](./06-Modern-Frontiers/01-凝聚数学.md) |

### 使用 GitHub/GitLab 搜索

如果在本地找不到，可以使用代码托管平台的搜索功能：

1. 打开项目仓库
2. 使用搜索框
3. 限定搜索范围：
   - `path:FormalMath-Enhanced/02-Mathlib4-Annotations 拉格朗日`
   - `extension:md 素数定理`

### 使用 IDE 搜索

在 VS Code 等 IDE 中：

- `Ctrl+Shift+F` (全局搜索)
- `Ctrl+P` 后输入文件名
- 使用正则表达式搜索模式

---

## ❓ 常见问题

**Q: 找不到特定定理的注释？**
A: 查看 [02-Mathlib4-Annotations/INDEX.md](./02-Mathlib4-Annotations/INDEX.md) 的"待添加定理"部分

**Q: 如何找到 MSC 编码对应的具体内容？**
A: 在 MSC 索引文件中找到编码后，查看"适用内容"列，然后搜索相关内容

**Q: 如何找到某个 IMO 题目的多种解法？**
A: 目前每个题目文件包含标准解法，可参考 AoPS 社区链接（在题目中标注）

**Q: 如何知道某个前沿专题的最新进展？**
A: 前沿专题文档包含"最新进展"部分，并链接到相关论文和项目

---

## 🔗 相关索引

- 📍 [中央索引](./INDEX.md) - 项目总览
- 🏷️ [按主题分类索引](./BY-TOPIC.md) - 主题导航
- 📊 [按难度分级索引](./BY-LEVEL.md) - 难度导航
- 📋 [快速参考卡片](./QUICK-REF.md) - 公式速查

---

*搜索指南最后更新：2026年4月3日*
