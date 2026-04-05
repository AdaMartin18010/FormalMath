---
title: FormalMath 交互式练习系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 交互式练习系统

## 概述

交互式练习系统是 FormalMath 项目的核心学习功能模块，提供完整的在线数学练习体验，支持多种题型、智能验证、逐步提示和错题管理。

## 功能特性

### 1. 多样化题型支持

- **单选题**：标准选择题，支持 LaTeX 数学公式
- **多选题**：支持部分得分机制
- **填空题**：多填空支持，替代答案配置
- **计算题**：数值容差处理，分步解答
- **证明题**：结构化证明输入，关键知识点检查
- **判断题**：正确/错误二元选择

### 2. 智能答案验证

- **即时反馈**：答题后立即显示结果
- **部分得分**：多选题按正确选项比例计分
- **容差处理**：计算题支持数值误差范围
- **智能分析**：自动推断错误类型

### 3. 逐步提示系统

- **分层提示**：最多 5 级逐步提示
- **题型定制**：针对不同题型提供特定提示
- **动态生成**：根据用户答题情况生成提示
- **错误针对性**：根据错误类型给出专门提示

### 4. 进度追踪

- **实时统计**：正确率、用时、连对记录
- **进度可视化**：进度条、题目状态点
- **会话管理**：支持练习会话的暂停和恢复
- **历史记录**：完整的答题历史

### 5. 错题本功能

- **自动记录**：答错的题目自动加入错题本
- **错误分类**：7 种错误类型自动识别
- **掌握度追踪**：4 级掌握度评估（薄弱/提升中/已掌握/已遗忘）
- **间隔重复**：基于艾宾浩斯遗忘曲线的复习提醒
- **统计分析**：错误类型分布、掌握度统计

## 技术架构

### 文件结构

```
src/
├── types/
│   └── exercise.ts          # 练习系统类型定义
├── services/
│   ├── exerciseValidator.ts  # 答案验证服务
│   ├── hintService.ts        # 提示生成服务
│   └── mistakeBookService.ts # 错题本服务
├── hooks/
│   └── useExercise.ts        # 练习系统 Hooks
├── components/
│   └── Exercises/
│       ├── SingleChoice.tsx      # 单选题组件
│       ├── MultipleChoice.tsx    # 多选题组件
│       ├── FillBlank.tsx         # 填空题组件
│       ├── Calculation.tsx       # 计算题组件
│       ├── TrueFalse.tsx         # 判断题组件
│       ├── Proof.tsx             # 证明题组件
│       ├── ExerciseFeedback.tsx  # 反馈组件
│       ├── HintPanel.tsx         # 提示面板
│       ├── SolutionPanel.tsx     # 解答面板
│       ├── ProgressTracker.tsx   # 进度追踪
│       ├── MistakeBook.tsx       # 错题本
│       └── index.ts              # 组件导出
└── pages/
    └── Exercise/
        ├── index.tsx         # 练习页面
        ├── MistakeBookPage.tsx # 错题本页面
        └── sampleData.ts     # 示例数据
```

### 核心类型

```typescript
// 练习题型
ExerciseType = 'single_choice' | 'multiple_choice' | 'fill_blank' 
             | 'calculation' | 'proof' | 'matching' | 'ordering' | 'true_false'

// 难度等级
DifficultyLevel = 'beginner' | 'intermediate' | 'advanced' | 'expert'

// 错误类型
ErrorType = 'concept_misunderstanding' | 'calculation_error' | 'formula_misapplication'
          | 'logic_error' | 'careless_mistake' | 'knowledge_gap' | 'other'

// 掌握度
MasteryLevel = 'weak' | 'developing' | 'mastered' | 'forgotten'
```

### Hooks API

#### useExercise

```typescript
const {
  exercise,           // 当前练习
  userAnswer,         // 用户答案
  validationResult,   // 验证结果
  hints,              // 已揭示的提示
  timeSpent,          // 用时
  attempts,           // 尝试次数
  loadExercise,       // 加载练习
  setAnswer,          // 设置答案
  submitAnswer,       // 提交答案
  requestHint,        // 请求提示
  showSolution,       // 显示解答
  skipExercise,       // 跳过练习
  resetExercise,      // 重置练习
} = useExercise({ userId, settings });
```

#### useMistakeBook

```typescript
const {
  mistakes,           // 所有错题
  overview,           // 统计概览
  getPendingReviews,  // 获取待复习错题
  recordReview,       // 记录复习结果
  getRecommendedMistakes, // 获取推荐复习
  deleteMistake,      // 删除错题
} = useMistakeBook(userId);
```

## 使用示例

### 基础练习

```tsx
import { useExercise } from '@hooks/useExercise';
import { ExerciseComponent, ExerciseFeedback } from '@components/Exercises';

function ExercisePage() {
  const { 
    exercise, 
    userAnswer, 
    validationResult,
    setAnswer, 
    submitAnswer 
  } = useExercise({ userId: 'user-1' });

  return (
    <div>
      <ExerciseComponent
        exercise={exercise}
        userAnswer={userAnswer}
        onAnswer={setAnswer}
        disabled={!!validationResult}
      />
      {validationResult && (
        <ExerciseFeedback result={validationResult} />
      )}
      <button onClick={submitAnswer}>提交</button>
    </div>
  );
}
```

### 错题本集成

```tsx
import { useMistakeBook } from '@hooks/useExercise';
import { MistakeBook, MistakeOverview } from '@components/Exercises';

function MistakeBookPage() {
  const { mistakes, overview, recordReview } = useMistakeBook('user-1');

  return (
    <div>
      <MistakeOverview {...overview} />
      <MistakeBook 
        mistakes={mistakes} 
        onReview={(mistake) => {
          // 导航到练习页面复习
        }}
      />
    </div>
  );
}
```

## 配置选项

### ExerciseSettings

```typescript
interface ExerciseSettings {
  showHintButton: boolean;        // 显示提示按钮
  showSolutionButton: boolean;    // 显示解答按钮
  autoShowSolution: boolean;      // 自动显示解答
  autoAdvance: boolean;           // 自动进入下一题
  allowSkip: boolean;             // 允许跳过
  requireExplanation: boolean;    // 需要解释
  timeLimitPerExercise?: number;  // 单题时间限制
  immediateFeedback: boolean;     // 即时反馈
  showCorrectAnswer: boolean;     // 显示正确答案
  showDetailedFeedback: boolean;  // 显示详细反馈
  adaptiveDifficulty: boolean;    // 自适应难度
  spacedRepetition: boolean;      // 间隔重复
  dailyGoal: number;              // 每日目标
}
```

## 扩展开发

### 添加新题型

1. 在 `types/exercise.ts` 中添加新题型
2. 在 `services/exerciseValidator.ts` 中添加验证逻辑
3. 在 `services/hintService.ts` 中添加提示生成器
4. 在 `components/Exercises/` 中创建题型组件
5. 在 `components/Exercises/index.ts` 中注册组件

### 自定义验证规则

```typescript
import { ExerciseValidator } from '@services/exerciseValidator';

const validator = new ExerciseValidator({
  caseSensitive: false,
  ignoreWhitespace: true,
  numericalTolerance: 0.001,
  partialCreditEnabled: true,
});

const result = validator.validate(exercise, userAnswer);
```

## 数据持久化

错题本数据使用 `localStorage` 进行本地持久化，键名为 `formalmath_mistake_book`。

## 后续优化方向

1. **AI 辅助**：集成 AI 进行证明题评分
2. **LaTeX 支持**：完整的数学公式渲染
3. **图表交互**：支持几何题的画图作答
4. **多端同步**：云同步错题本数据
5. **学习报告**：生成详细的学习分析报告

## 许可证

MIT License
