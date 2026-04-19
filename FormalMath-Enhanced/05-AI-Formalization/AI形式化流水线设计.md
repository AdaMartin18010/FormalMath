---
title: "FormalMath AI形式化流水线设计"
msc_primary: 00A99
level: project
status: planning
created_at: 2026-04-18
---

# AI形式化流水线设计

## 1. 目标

建立从自然语言数学证明到 Lean4 形式化代码的半自动转换流水线，降低 FormalMath 内容生产的 Lean4 编码成本。

## 2. 系统架构

```
自然语言证明 → 语义解析 → 中间表示(IR) → Lean4代码生成 → 编译验证 → 反馈修正
```

### 2.1 语义解析模块

- 输入：FormalMath银层/金层文档中的自然语言证明段落
- 处理：NLP抽取定义、定理、证明步骤
- 输出：结构化IR（定义符号表、定理陈述、证明步骤序列）

### 2.2 Lean4代码生成模块

- 输入：结构化IR
- 处理：模板匹配 + Mathlib4 API检索
- 输出：Lean4代码草案

### 2.3 编译验证模块

- 输入：Lean4代码草案
- 处理：`lake build` 或 `lean --make`
- 输出：编译结果（成功/错误信息）

### 2.4 反馈修正模块

- 输入：编译错误
- 处理：错误分类 → 自动修复（类型不匹配、缺失import等）→ 人工复核
- 输出：修正后的代码

## 3. 与现有内容的对接

| 层级 | 当前Lean4状态 | AI增强目标 |
|------|--------------|-----------|
| 银层 | 61/61 文档含Lean4块 | 提升代码质量，确保可编译 |
| 金层 | 50/50 文档含Lean4块 | 深度形式化核心定理证明 |
| 铜层 | 无系统覆盖 | 选择性形式化基础概念 |

## 4. 技术栈

- **语义解析**：OpenAI GPT-4 / Claude 3.5 Sonnet（数学专用prompt）
- **IR格式**：自定义JSON Schema（与Lean AST兼容）
- **代码生成**：Lean4 Template Engine + Mathlib4 API知识库
- **验证环境**：Dockerized Lean4 + Mathlib4
- **反馈循环**：CI/CD pipeline（GitHub Actions）

## 5. 里程碑

| 阶段 | 目标 | 时间 |
|------|------|------|
| M1 | 建立IR格式和prompt模板 | 2周 |
| M2 | 银层Ch01-Ch05自动形式化原型 | 4周 |
| M3 | 编译通过率>80% | 6周 |
| M4 | 金层核心定理深度形式化 | 8周 |
| M5 | 集成到FormalMath-Interactive前端 | 10周 |
