# FormalMath 贡献者指南

## 如何贡献

### 1. 选择任务

查看[知识缺口分析](00-知识缺口分析.md)选择感兴趣的方向。

### 2. 创建文档

使用以下模板：

`markdown
---
course: [课程名]
level: silver
msc_primary: "[MSC代码]"
tags: ["标签1", "标签2"]
review_status: completed
---

# [标题（中文+英文）]

**课程**: [课程名] | **层次**: 银层

---

## 一、核心定义

### 定义 1.1（[概念名]）

**严格陈述**: [LaTeX公式]

**直观解释**: [几何/物理/计算直观]

---

## 二、核心定理

**定理 1.** [定理名]

**严格陈述**: [完整陈述]

**证明思路**:
1. [步骤1]
2. [步骤2]
3. [步骤3]

---

## 三、习题

**习题 1.** [题目] (⭐)

**解答**: [详细解答]

---

## 四、Lean4形式化

\\\lean4
import Mathlib

-- [定理名]的形式化
theorem [定理名] : [类型] := by
  sorry
\\\

---

## 参考文献

1. [作者], *[书名]*, [出版社], [年份].

## 交叉引用

- [相关文档](../[路径])
`

### 3. 质量检查

运行本地检查：
`powershell
.\scripts\quality-gate.ps1
`

### 4. 提交PR

遵循GitHub PR模板。

## 质量标准

参见[银层文档质量检查清单](00-银层文档质量检查清单.md)。

## 代码规范

### Markdown
- 使用UTF-8编码
- 标题使用#层级
- LaTeX公式使用或$
- 代码块标注语言

### Lean4
- 使用import Mathlib或具体模块
- 定理命名使用camelCase
- 添加注释说明数学含义
- 使用sorry标记未完成证明

## 联系方式

- Issues: GitHub Issues
- Discussion: GitHub Discussions