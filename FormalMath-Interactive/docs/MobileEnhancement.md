---
title: FormalMath 移动端功能增强
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 移动端功能增强

本文档介绍 FormalMath-Interactive 项目的移动端功能增强模块。

## 功能概览

### 1. 离线学习支持 (Offline Learning)

通过 IndexedDB 实现内容缓存和离线数据同步。

#### 核心功能

- **内容缓存**: 缓存学习内容（概念、定理、证明、练习等）供离线访问
- **进度同步**: 自动同步学习进度，离线时保存到本地队列
- **后台同步**: 使用 Service Worker 实现后台数据同步
- **缓存管理**: 自动清理过期缓存，限制缓存大小（默认 100MB）

#### 使用示例

```typescript
import { offlineService, useOfflineContent, useOfflineProgress } from '@/services';
import { useOfflineContent, useOfflineProgress } from '@/hooks';

// 使用 Hook
const { cacheContent, getContent, stats } = useOfflineContent();
const { saveProgress, syncProgress, isOnline } = useOfflineProgress(userId);

// 缓存内容
await cacheContent({
  id: 'concept-1',
  type: 'concept',
  title: '极限的定义',
  content: '...',
  metadata: { difficulty: 'beginner' },
});

// 保存学习进度
await saveProgress('concept-1', {
  progress: 75,
  completed: false,
});
```

#### 组件位置

- 服务: `src/services/offlineService.ts`
- Hooks: `src/hooks/useOffline.ts`

---

### 2. 语音交互 (Voice Interaction)

使用 Web Speech API 实现语音识别和语音合成。

#### 核心功能

- **语音识别**: 实时语音转文字，支持连续识别
- **语音合成**: 文本转语音，可调节语速、音调、音量
- **数学公式朗读**: 自动转换数学符号为可读文本
- **语音命令**: 支持自定义语音命令（如"打开知识图谱"）

#### 组件

##### VoiceAssistant - 语音助手组件

完整的语音交互界面，包含录音按钮、设置面板、文本显示。

```tsx
import { VoiceAssistant, mathVoiceCommands } from '@/components/VoiceInteraction';

<VoiceAssistant
  onCommand={(command, params) => console.log(command, params)}
  onTranscript={(text) => console.log(text)}
  commands={mathVoiceCommands}
  language="zh-CN"
/>
```

##### VoiceControl - 语音控制组件

简洁的语音输入控件，带音频波形可视化。

```tsx
import { VoiceControl } from '@/components/VoiceInteraction';

<VoiceControl
  onTranscript={(text) => setInputText(text)}
  showWaveform={true}
/>
```

##### MathVoiceReader - 数学语音朗读器

专门用于朗读数学内容的组件，支持高亮当前朗读位置。

```tsx
import { MathVoiceReader } from '@/components/VoiceInteraction';

<MathVoiceReader
  content="极限 lim(x→∞) 1/x = 0"
  title="极限概念"
  autoRead={false}
/>
```

#### Hooks

```typescript
import { useSpeechSynthesis, useSpeechRecognition, useMathReader } from '@/hooks';

// 语音合成
const { speak, stop, isSpeaking } = useSpeechSynthesis();

// 语音识别
const { startListening, transcript, isListening } = useSpeechRecognition();

// 数学朗读
const { readMath, stop } = useMathReader();
```

#### 组件位置

- 组件: `src/components/VoiceInteraction/`
- Hooks: `src/hooks/useVoice.ts`

---

### 3. AR 可视化 (AR Visualization)

使用 WebXR API 实现增强现实可视化。

#### 核心功能

- **AR 查看器**: 在现实空间中放置 3D 数学模型
- **3D 知识图谱**: 三维展示概念关系网络
- **函数可视化**: 3D 函数曲面绘制
- **几何预览**: 2D 几何图形预览

#### 组件

##### ARViewer - AR 查看器

完整的 AR 体验组件，支持模型选择、放置、缩放。

```tsx
import { ARViewer, sampleARModels } from '@/components/ARVisualization';

<ARViewer
  models={sampleARModels}
  onModelSelect={(model) => console.log(model)}
/>
```

##### ARGraph3D - 3D 知识图谱

使用 Three.js 渲染的交互式 3D 图谱。

```tsx
import { ARGraph3D, generateSampleGraph } from '@/components/ARVisualization';

const data = generateSampleGraph();

<ARGraph3D
  data={data}
  width={800}
  height={600}
  interactive={true}
  onNodeClick={(node) => console.log(node)}
/>
```

##### FunctionPlot3D - 3D 函数绘图

绘制数学函数的 3D 曲面。

```tsx
import { FunctionPlot3D, presetFunctions } from '@/components/ARVisualization';

<FunctionPlot3D
  functions={presetFunctions}
  width={800}
  height={600}
/>
```

#### Hooks

```typescript
import { useARSupport } from '@/hooks';

const { isSupported, isChecking } = useARSupport();
```

#### 组件位置

- 组件: `src/components/ARVisualization/`

---

### 4. 智能提醒 (Smart Reminders)

基于学习行为和目标的智能提醒系统。

#### 核心功能

- **学习提醒**: 每日学习目标、复习提醒、连续学习提醒
- **目标追踪**: 设定和追踪学习目标
- **智能建议**: 基于学习数据提供个性化建议
- **通知管理**: 浏览器推送通知

#### 服务

```typescript
import { reminderService, reminderTemplates } from '@/services';

// 创建提醒
const reminder = await reminderService.createReminder({
  userId: 'user-1',
  type: 'daily_goal',
  title: '今日学习目标',
  message: '该开始学习了！',
  schedule: {
    time: '09:00',
    frequency: 'daily',
  },
});

// 使用模板
const dailyReminder = await reminderService.createReminder({
  ...reminderTemplates.dailyStudy('09:00'),
  userId: 'user-1',
});

// 创建目标
const goal = await reminderService.createGoal({
  userId: 'user-1',
  title: '本周学习目标',
  type: 'weekly',
  target: {
    studyMinutes: 300,
    problemsSolved: 50,
  },
});
```

#### Hooks

```typescript
import {
  useReminders,
  useLearningGoals,
  useLearningStats,
  useSmartSuggestions,
  useLearningTracker
} from '@/hooks';

// 提醒管理
const { reminders, createReminder, toggleReminder } = useReminders(userId);

// 目标管理
const { goals, createGoal, updateGoalProgress } = useLearningGoals(userId);

// 学习统计
const { todayStats, weeklyStats, recordStudy } = useLearningStats(userId);

// 智能建议
const { suggestions } = useSmartSuggestions(userId);

// 一站式追踪
const { reminders, goals, stats, suggestions } = useLearningTracker(userId);
```

#### 组件位置

- 服务: `src/services/reminderService.ts`
- Hooks: `src/hooks/useReminder.ts`

---

### 5. 社交功能 (Social Features)

学习社区和社交互动功能。

#### 核心功能

- **社交分享**: 分享到微信、微博、Twitter 等平台
- **学习小组**: 创建和加入学习小组，共同学习
- **排行榜**: 查看学习排行，激发学习动力
- **好友动态**: 查看好友学习进展
- **协作邀请**: 邀请他人加入协作

#### 组件

##### SocialShare - 社交分享

```tsx
import { SocialShare, ShareButton } from '@/components/SocialFeatures';

<SocialShare
  data={{
    title: '我完成了今日学习目标',
    description: '学习了 2 小时，解决了 10 道题目',
    url: 'https://formalmath.com/share/xxx[需更新]',
    image: '/share-image.png',
  }}
/>

// 快速分享按钮
<ShareButton
  data={shareData}
  variant="button"
  size="md"
>
  分享成就
</ShareButton>
```

##### StudyGroup - 学习小组

```tsx
import { StudyGroup } from '@/components/SocialFeatures';

<StudyGroup
  group={groupData}
  members={members}
  currentUserId="user-1"
  onInvite={() => openInviteModal()}
  onMessage={(userId) => openChat(userId)}
/>
```

##### Leaderboard - 排行榜

```tsx
import { Leaderboard, MiniLeaderboard } from '@/components/SocialFeatures';

<Leaderboard
  type="weekly"
  scope="global"
  entries={leaderboardData}
/>

<MiniLeaderboard
  title="好友排行"
  entries={friendsData}
/>
```

##### FriendActivity - 好友动态

```tsx
import { FriendActivity, ActiveUsers } from '@/components/SocialFeatures';

<FriendActivity
  activities={activities}
  requests={friendRequests}
  onAcceptRequest={(id) => acceptRequest(id)}
/>

<ActiveUsers
  users={activeUsers}
  onStartChat={(userId) => openChat(userId)}
/>
```

##### CollaborationInvite - 协作邀请

```tsx
import { CollaborationInvite, QuickInviteButton } from '@/components/SocialFeatures';

<CollaborationInvite
  groupId="group-1"
  groupName="数学分析学习组"
  inviteLink="https://formalmath.com/invite/xxx[需更新]"
/>

<QuickInviteButton
  memberCount={10}
  maxMembers={50}
/>
```

#### Hooks

```typescript
import { useSocialShare } from '@/hooks';

const { share, copyToClipboard } = useSocialShare();

// 原生分享
await share({
  title: '我的学习成果',
  text: '今天学习了 2 小时',
  url: 'https://formalmath.com[需更新]',
});
```

#### 组件位置

- 组件: `src/components/SocialFeatures/`

---

## 浏览器兼容性

| 功能 | Chrome | Firefox | Safari | Edge | 移动端 |
|------|--------|---------|--------|------|--------|
| 离线学习 | ✅ | ✅ | ✅ | ✅ | ✅ |
| 语音识别 | ✅ | ❌ | ✅ (部分) | ✅ | ✅ (Android) |
| 语音合成 | ✅ | ✅ | ✅ | ✅ | ✅ |
| AR (WebXR) | ✅ | ❌ | ❌ | ✅ | ✅ (Android) |
| 推送通知 | ✅ | ✅ | ✅ | ✅ | ✅ |

---

## 安装依赖

```bash
# 核心依赖（已包含在项目中）
npm install idb  # IndexedDB 封装
npm install @react-three/fiber @react-three/drei three  # 3D 渲染
npm install lucide-react  # 图标
```

---

## 快速开始

1. **初始化服务**

```typescript
import { offlineService, reminderService } from '@/services';

// 在应用启动时初始化
await offlineService.init();
// reminderService 会在首次使用时自动初始化
```

1. **使用组件**

```tsx
import { VoiceAssistant, ARViewer, SocialShare } from '@/components';

function App() {
  return (
    <div>
      <VoiceAssistant />
      <ARViewer />
      <SocialShare data={shareData} />
    </div>
  );
}
```

1. **使用 Hooks**

```tsx
import { useLearningTracker } from '@/hooks';

function Dashboard() {
  const { goals, stats, suggestions } = useLearningTracker(userId);

  return (
    <div>
      <h1>今日学习: {stats.todayStats?.studyMinutes || 0} 分钟</h1>
      <p>建议: {suggestions[0]}</p>
    </div>
  );
}
```

---

## 文件结构

```
src/
├── components/
│   ├── VoiceInteraction/      # 语音交互组件
│   │   ├── VoiceAssistant.tsx
│   │   ├── VoiceControl.tsx
│   │   └── MathVoiceReader.tsx
│   ├── ARVisualization/       # AR 可视化组件
│   │   ├── ARViewer.tsx
│   │   ├── ARGraph3D.tsx
│   │   └── FunctionPlot3D.tsx
│   └── SocialFeatures/        # 社交功能组件
│       ├── SocialShare.tsx
│       ├── StudyGroup.tsx
│       ├── Leaderboard.tsx
│       └── FriendActivity.tsx
├── hooks/
│   ├── useVoice.ts           # 语音相关 Hooks
│   ├── useOffline.ts         # 离线学习 Hooks
│   └── useReminder.ts        # 智能提醒 Hooks
└── services/
    ├── offlineService.ts     # 离线学习服务
    └── reminderService.ts    # 智能提醒服务
```

---

## 性能优化

1. **离线缓存**
   - 限制缓存大小（默认 100MB）
   - LRU 策略自动清理
   - 内容过期机制

2. **语音合成**
   - 复用 SpeechSynthesis 实例
   - 批量朗读时预加载

3. **3D 渲染**
   - 使用 React Three Fiber 的优化渲染
   - 按需加载模型
   - 自适应分辨率

---

## 贡献指南

欢迎提交 Issue 和 PR！请确保：

1. 代码遵循项目 ESLint 规则
2. 添加必要的类型定义
3. 更新相关文档
4. 测试新功能

---

## License

MIT
