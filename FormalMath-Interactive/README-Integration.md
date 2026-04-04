# FormalMath 智能学习系统集成文档

## 第十一批任务：前端与智能学习系统集成

本文档描述 FormalMath 前端与 T2.1/T2.2/T3.1 智能学习系统的集成实现。

## 📁 目录结构

```
FormalMath-Interactive/src/
├── api/                          # API客户端
│   ├── client.ts                 # HTTP客户端基类
│   ├── diagnosis.ts              # T2.1 认知诊断API
│   ├── evaluation.ts             # T2.2 评估系统API
│   ├── adaptive.ts               # T3.1 自适应学习API
│   └── index.ts                  # API模块统一导出
├── types/                        # TypeScript类型定义
│   └── learning.ts               # 所有学习系统类型
├── integrations/                 # 数据整合逻辑
│   ├── personalizedGraph.ts      # 个性化知识图谱
│   ├── learningPath.ts           # 学习路径可视化
│   ├── progressTracker.ts        # 进度追踪与成就
│   └── index.ts                  # 整合模块统一导出
├── hooks/                        # React Hooks
│   ├── useDiagnosis.ts           # 诊断系统Hook
│   ├── useEvaluation.ts          # 评估系统Hook
│   ├── useAdaptive.ts            # 自适应学习Hook
│   ├── useProgressTracking.ts    # 进度追踪Hook
│   └── index.ts                  # Hooks统一导出
├── components/visualization/     # 可视化组件
│   ├── PersonalizedGraph.tsx     # 个性化知识图谱
│   ├── LearningPathView.tsx      # 学习路径视图
│   ├── ProgressDashboard.tsx     # 进度仪表盘
│   └── index.ts                  # 组件统一导出
└── utils/                        # 工具函数
    ├── colorCoding.ts            # 颜色编码工具
    └── index.ts                  # 工具统一导出
```

## 🔌 API 接口

### T2.1 认知诊断系统

```typescript
// 获取诊断结果
GET /api/diagnosis/{userId}

// 提交诊断答案
POST /api/diagnosis/submit
{
  answers: Answer[];
  metadata?: { totalTime, device, version };
}

// 其他接口
- getWeakPoints(userId)
- getRecommendations(userId)
- getDiagnosisHistory(userId)
```

### T2.2 评估系统

```typescript
// 获取评估报告
GET /api/evaluation/{userId}

// 能力维度
GET /api/evaluation/{userId}/dimensions

// 成长曲线
GET /api/evaluation/{userId}/growth

// 徽章/成就
GET /api/evaluation/{userId}/badges
GET /api/evaluation/{userId}/achievements
```

### T3.1 自适应学习系统

```typescript
// 获取学习路径
GET /api/adaptive/path/{userId}

// 更新进度
POST /api/adaptive/progress
{
  userId: string;
  conceptId: string;
  mastery: number;
}

// 完成节点
POST /api/adaptive/node/{nodeId}/complete
```

## 🪝 React Hooks 使用示例

### 使用诊断系统

```tsx
import { useDiagnosis } from './hooks';

function DiagnosisComponent({ userId }: { userId: string }) {
  const {
    diagnosis,
    weakPoints,
    recommendations,
    loading,
    submitDiagnosis,
  } = useDiagnosis({ userId });

  if (loading) return <div>加载中...</div>;

  return (
    <div>
      <h2>薄弱点</h2>
      {weakPoints.map(wp => (
        <div key={wp.conceptId}>{wp.conceptName}</div>
      ))}
    </div>
  );
}
```

### 使用评估系统

```tsx
import { useEvaluation } from './hooks';

function EvaluationComponent({ userId }: { userId: string }) {
  const {
    evaluation,
    dimensions,
    radarData,
    badges,
    achievements,
  } = useEvaluation({ userId });

  return (
    <div>
      <RadarChart data={radarData} />
      <BadgeGallery badges={badges} />
    </div>
  );
}
```

### 使用自适应学习

```tsx
import { useAdaptive } from './hooks';

function LearningComponent({ userId }: { userId: string }) {
  const {
    learningPath,
    currentNode,
    updateProgress,
    completeNode,
  } = useAdaptive({ userId });

  const handleComplete = async () => {
    await completeNode(currentNode!.id, {
      timeSpent: 30,
      exercisesCompleted: 5,
      correctRate: 0.8,
    });
  };

  return (
    <div>
      <h2>当前学习: {currentNode?.conceptName}</h2>
      <button onClick={handleComplete}>完成学习</button>
    </div>
  );
}
```

## 📊 可视化组件使用

### 个性化知识图谱

```tsx
import { PersonalizedGraph } from './components/visualization';

function GraphPage({ userId }: { userId: string }) {
  const conceptGraph = {
    nodes: [...],
    edges: [...],
  };

  return (
    <PersonalizedGraph
      userId={userId}
      conceptGraph={conceptGraph}
      width={1000}
      height={600}
      onNodeClick={(node) => console.log('Clicked:', node)}
    />
  );
}
```

**功能特性：**

- 根据掌握度用颜色编码节点（L0红色-L4蓝色）
- 薄弱概念高亮显示（深红色）
- 推荐概念特殊标记（青色）
- 已掌握概念淡化显示
- 支持点击和悬停交互

### 学习路径视图

```tsx
import { LearningPathView } from './components/visualization';

function PathPage({ userId }: { userId: string }) {
  return (
    <LearningPathView
      userId={userId}
      width={900}
      height={500}
      showTimeEstimate={true}
      showComparison={true}
    />
  );
}
```

**功能特性：**

- 路径节点显示预计学习时间
- 进度实时更新
- 支持路径对比视图
- 里程碑节点特殊标记

### 进度仪表盘

```tsx
import { ProgressDashboard } from './components/visualization';

function DashboardPage({ userId }: { userId: string }) {
  return <ProgressDashboard userId={userId} />;
}
```

**功能特性：**

- 掌握度分布图表
- 成就进度追踪
- 徽章展示
- 技能增长趋势
- 学习速度统计

## 🎨 颜色编码系统

### 掌握度颜色

| 等级 | 名称 | 颜色 | 用途 |
|------|------|------|------|
| L0 | 未掌握 | 红色 #ef4444 | 需要优先学习 |
| L1 | 初学 | 橙色 #f97316 | 刚开始学习 |
| L2 | 理解 | 黄色 #eab308 | 基础理解 |
| L3 | 熟练 | 绿色 #22c55e | 熟练掌握 |
| L4 | 精通 | 蓝色 #3b82f6 | 精通可教学 |

### 特殊标记

| 类型 | 颜色 | 说明 |
|------|------|------|
| 薄弱点 | 深红色 #dc2626 | 诊断出的薄弱概念 |
| 当前焦点 | 紫色 #8b5cf6 | 正在学习的概念 |
| 推荐学习 | 青色 #06b6d4 | 系统推荐的概念 |

## 📈 数据整合逻辑

### 个性化知识图谱

1. **数据流：**
   - 获取诊断结果 → 获取学习路径 → 整合图谱数据

2. **个性化逻辑：**
   - 根据 `knowledgeLevels` 设置节点颜色
   - 根据 `weakPoints` 高亮薄弱概念
   - 根据 `recommendations` 标记推荐概念
   - 根据学习路径状态设置当前焦点

3. **视觉编码：**
   - 节点大小：掌握度越低，节点越大（提示关注）
   - 节点透明度：掌握度越高，越淡化
   - 特殊标记：薄弱点和推荐概念有光晕效果

### 学习路径可视化

1. **布局算法：**
   - 基于依赖关系的层级布局
   - 蛇形排列减少视觉混乱
   - 里程碑节点突出显示

2. **时间整合：**
   - 每个节点显示 `estimatedTime`
   - 汇总计算总剩余时间
   - 根据用户学习速度调整预估

### 进度追踪

1. **成就系统：**
   - 预定义成就条件
   - 实时检查完成情况
   - 新成就触发通知

2. **徽章系统：**
   - 基于稀有度分级
   - 学习统计驱动解锁
   - 最近获得优先展示

## 🔧 环境配置

### 环境变量

```bash
# API 基础 URL
REACT_APP_API_URL=http://localhost:3001/api

# 可选：WebSocket URL（实时更新）
REACT_APP_WS_URL=ws://localhost:3001/ws
```

### 安装依赖

```bash
npm install
# 或
yarn install
```

### 类型依赖

```bash
npm install --save-dev @types/react @types/react-dom
```

## 🚀 快速开始

1. **启动开发服务器：**

   ```bash
   npm start
   ```

2. **构建生产版本：**

   ```bash
   npm run build
   ```

3. **运行测试：**

   ```bash
   npm test
   ```

## 📚 类型定义索引

详见 `src/types/learning.ts`

核心类型：

- `DiagnosisReport` - 诊断报告
- `EvaluationReport` - 评估报告
- `LearningPath` - 学习路径
- `PersonalizedGraphData` - 个性化图谱
- `RealtimeProgress` - 实时进度

## 🔐 认证说明

API 客户端自动处理：

- JWT Token 管理
- Token 自动刷新
- 401 错误重试

Token 存储在 `localStorage`：

- `formalmath_access_token`
- `formalmath_refresh_token`

## 📞 支持与反馈

如有问题，请通过以下方式联系：

- 提交 Issue
- 发送邮件至 support@formalmath.org

---

**生成日期：** 2026年4月4日
**版本：** 1.0.0
**作者：** FormalMath 开发团队
