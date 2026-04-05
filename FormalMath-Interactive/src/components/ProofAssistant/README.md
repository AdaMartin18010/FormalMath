---
title: 定理证明助手系统 (Theorem Proof Assistant)
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 定理证明助手系统 (Theorem Proof Assistant)

基于 Lean4 的交互式定理证明辅助系统，提供直观的可视化界面和智能策略推荐。

## 功能特性

### 1. 证明策略推荐 (Proof Strategy Recommendation)
- **智能分析**：根据当前证明状态自动分析目标结构
- **策略库**：包含 40+ 种常用 Lean4 证明策略
  - 引入规则 (intro, intros, constructor, split, left, right, exists)
  - 消去规则 (apply, exact, refine, cases, destruct)
  - 重写简化 (rw, simp, simp_all)
  - 自动化 (tauto, aesop, linarith, ring, field)
  - 归纳法 (induction)
  - 算术求解 (linarith, nlinarith, omega, norm_num)
  - 等式处理 (rfl, symm, trans, calc)
  - 逻辑推理 (by_contra, by_cases, contradiction, exfalso)
- **置信度评分**：每个建议都包含适用性评分和推荐理由
- **分类浏览**：按类别浏览所有可用策略

### 2. 证明状态可视化 (Proof State Visualization)
- **目标展示**：清晰显示当前证明目标、假设列表
- **状态标识**：
  - 🔵 蓝色：当前目标
  - 🟢 绿色：已完成目标
  - 🟡 黄色：待证明目标
- **上下文显示**：变量、常量、定义列表
- **交互式操作**：点击假设查看详情，切换当前目标

### 3. 交互式证明构造 (Interactive Proof Construction)
- **分步构建**：一步一步构建证明
- **撤销重做**：支持撤销上一步操作
- **分支管理**：支持多分支证明
- **检查点**：保存和恢复证明状态
- **进度追踪**：实时显示证明进度

### 4. Lean4 代码生成 (Lean4 Code Generation)
- **自动生成**：根据证明步骤自动生成 Lean4 代码
- **多种风格**：
  - 紧凑风格 (compact)
  - 详细风格 (verbose) - 带注释
  - 结构化风格 (structured) - 推荐
- **代码导出**：支持复制和下载 `.lean` 文件
- **语法高亮**：编辑器支持 Lean4 语法高亮

### 5. 证明验证 (Proof Verification)
- **语法检查**：验证 Lean4 代码语法
- **逻辑验证**：检查证明步骤的合理性
- **完整性检查**：确保所有目标都被证明
- **错误提示**：详细的错误信息和修复建议

## 使用方法

### 基本用法

```tsx
import { ProofAssistant } from '@components/ProofAssistant';

function MyComponent() {
  return (
    <ProofAssistant
      initialTheorem="add_comm"
      initialStatement="∀ (m n : ℕ), m + n = n + m"
      onProofComplete={(proof) => console.log('完成!', proof)}
      onStepChange={(step) => console.log('步骤:', step)}
      enableSuggestions={true}
      enableAutoVerify={false}
    />
  );
}
```

### 使用服务 API

```tsx
import { 
  proofStrategyEngine,
  leanCodeGenerator,
  proofVerifier,
  ProofConstructionService 
} from '@services';

// 创建证明
const service = ProofConstructionService.create('my_theorem', '∀ x, x = x');

// 获取策略建议
const suggestions = proofStrategyEngine.getSuggestions(service.getCurrentState());

// 应用策略
await service.applyTactic(suggestions[0].tactic, {});

// 生成 Lean4 代码
const code = leanCodeGenerator.generate(service.getConstruction());

// 验证证明
const result = await proofVerifier.verifyProof(service.getConstruction());
```

## 组件架构

```
ProofAssistant (主组件)
├── ProofStateView (证明状态视图)
│   ├── GoalDisplay (目标展示)
│   ├── HypothesisList (假设列表)
│   └── ContextPanel (上下文面板)
├── TacticPanel (策略面板)
│   ├── SearchBar (搜索栏)
│   ├── CategoryFilter (分类过滤器)
│   ├── SuggestionList (建议列表)
│   └── TacticDetail (策略详情)
└── LeanCodeEditor (代码编辑器)
    ├── CodeDisplay (代码显示)
    ├── VerificationPanel (验证面板)
    └── ExportButtons (导出按钮)
```

## 服务层

```
services/
├── proofStrategy.ts      # 策略推荐引擎
├── leanCodeGenerator.ts  # Lean4 代码生成器
├── proofVerifier.ts      # 证明验证器
└── proofConstruction.ts  # 证明构造服务
```

## 类型定义

```
types/
└── proofAssistant.ts     # 所有证明相关类型
```

## 预设定理示例

系统内置以下预设示例供练习：

1. **add_comm**: 自然数加法交换律 `∀ (m n : ℕ), m + n = n + m`
2. **mul_assoc**: 自然数乘法结合律 `∀ (a b c : ℕ), (a * b) * c = a * (b * c)`
3. **true_intro**: 真命题证明 `True`
4. **and_comm**: 合取交换律 `∀ (P Q : Prop), P ∧ Q → Q ∧ P`
5. **or_elim**: 析取消去 `∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R`

## 技术栈

- React 18
- TypeScript 5
- Tailwind CSS
- Lean4 (代码生成)

## 未来扩展

- [ ] 集成 Lean4 Language Server 进行实时代码验证
- [ ] 支持更多证明策略和自动化工具
- [ ] 添加证明树可视化
- [ ] 支持协作证明（多人同时编辑）
- [ ] 添加证明示例库和教程
- [ ] 支持导入/导出 Lean4 项目
