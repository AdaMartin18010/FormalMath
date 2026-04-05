---
title: FormalMath 游戏化模块
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 游戏化模块

## 概述

游戏化模块为 FormalMath 平台提供了完整的数学学习游戏化体验，包含解谜游戏、对战模式、探索模式、成就系统和虚拟导师五大核心功能。

## 功能模块

### 1. 解谜游戏 (Puzzle Game)

#### 支持的谜题类型
- **数学谜题** (math_riddle) - 经典数学逻辑谜题
- **证明构造** (proof_construct) - 拖拽式数学证明构建
- **概念连线** (concept_match) - 概念与定义匹配
- **方程求解** (equation_solve) - 交互式方程求解
- **模式识别** (pattern_recognize) - 数列与图形模式识别
- **逻辑推导** (logic_deduction) - 逻辑推理题

#### 难度等级
- 简单 (easy) - 基础概念题
- 中等 (medium) - 需要一定数学基础
- 困难 (hard) - 综合性难题
- 专家 (expert) - 挑战性难题

#### 核心组件
- `PuzzleCard` - 谜题卡片展示
- `PuzzleSolver` - 谜题解答界面
- `usePuzzle` Hook - 谜题状态管理

### 2. 对战模式 (Battle Mode)

#### 对战类型
- **速度挑战** (speed_challenge) - 限时快速答题
- **证明竞速** (proof_race) - 抢先完成数学证明
- **知识问答** (quiz_duel) - 多轮知识PK
- **团队对战** (team_battle) - 多人团队竞技

#### 核心组件
- `BattleLobby` - 对战大厅
- `BattleArena` - 对战界面
- `useBattle` Hook - 对战状态管理

### 3. 探索模式 (Exploration Mode)

#### 探索内容
- **数学世界** - 主题化数学领域探索
- **历史时间线** - 数学发展史时间旅行
- **概念收集** - 收集解锁数学概念卡片

#### 核心组件
- `WorldMap` - 世界地图
- `Timeline` - 历史时间线
- `Collection` - 概念收集册
- `useExploration` Hook - 探索状态管理

### 4. 成就系统 (Achievement System)

#### 徽章系统
- 学习成就 - 学习里程碑
- 解谜成就 - 解谜相关成就
- 对战成就 - 对战相关成就
- 探索成就 - 探索相关成就
- 社交成就 - 社交互动成就
- 特殊成就 - 限时/隐藏成就

#### 技能树
- 逻辑推理分支
- 收集专家分支
- 快速计算分支
- 证明大师分支

#### 等级系统
- 1-100级进阶
- 经验值积累
- 等级特权解锁

#### 排行榜
- 全球排行榜
- 周榜/日榜
- 好友排行榜

#### 核心组件
- `BadgeDisplay` - 徽章展示
- `SkillTree` - 技能树界面
- `Leaderboard` - 排行榜
- `useAchievements` Hook - 成就状态管理

### 5. 虚拟导师 (Virtual Tutor)

#### 导师性格
- 鼓励型 (encouraging) - 积极鼓励学习
- 严格型 (strict) - 严格要求标准
- 友好型 (friendly) - 亲切友好互动
- 学者型 (scholarly) - 学术严谨风格
- 神秘型 (mysterious) - 引导式启发

#### 指导类型
- 提示 (hint) - 解题提示
- 解释 (explanation) - 概念解释
- 反馈 (feedback) - 答题反馈
- 激励 (motivation) - 学习激励
- 挑战 (challenge) - 额外挑战

#### 核心组件
- `TutorWidget` - 导师悬浮窗
- `TutorChat` - 对话界面
- `useTutor` Hook - 导师状态管理

## 技术架构

### 状态管理
```typescript
// 使用 Zustand 进行全局状态管理
useGameStore
  ├── userGameData      // 用户游戏数据
  ├── currentSession    // 当前游戏会话
  ├── settings          // 游戏设置
  └── game data cache   // 游戏数据缓存
```

### 自定义 Hooks
```typescript
usePuzzle          // 解谜游戏逻辑
useBattle          // 对战模式逻辑
useExploration     // 探索模式逻辑
useAchievements    // 成就系统逻辑
useTutor           // 虚拟导师逻辑
```

### 服务层
```typescript
gameService
  ├── Puzzle Service      // 谜题相关API
  ├── Battle Service      // 对战相关API
  ├── Exploration Service // 探索相关API
  ├── Achievement Service // 成就相关API
  └── Tutor Service       // 导师相关API
```

## 使用指南

### 1. 初始化游戏系统

```typescript
import { useGameStore } from './stores/gameStore';

function App() {
  const initialize = useGameStore(state => state.initialize);
  
  useEffect(() => {
    initialize();
  }, []);
}
```

### 2. 解谜游戏

```typescript
import { usePuzzle } from './hooks/game';

function PuzzlePage() {
  const { 
    puzzles, 
    startPuzzle, 
    submitAnswer,
    timeSpent,
    hintsUsed 
  } = usePuzzle();

  return (
    // 渲染谜题界面
  );
}
```

### 3. 对战模式

```typescript
import { useBattle } from './hooks/game';

function BattlePage() {
  const { 
    createBattle, 
    joinBattle,
    submitAnswer,
    battle 
  } = useBattle();

  return (
    // 渲染对战界面
  );
}
```

### 4. 成就系统

```typescript
import { useAchievements } from './hooks/game';

function AchievementPage() {
  const { 
    level, 
    badges, 
    skillTree,
    unlockSkill 
  } = useAchievements();

  return (
    // 渲染成就界面
  );
}
```

### 5. 虚拟导师

```typescript
import { useTutor } from './hooks/game';

function GamePage() {
  const { 
    isEnabled, 
    getHint,
    getMotivation 
  } = useTutor();

  return (
    // 渲染导师组件
  );
}
```

## 奖励系统

### 经验值 (XP)
- 解谜成功：基础难度分数
- 时间奖励：快速解答额外经验
- 连胜奖励：连续正确经验加成

### 金币 (Coins)
- 完成谜题奖励
- 成就解锁奖励
- 每日登录奖励

### 徽章 (Badges)
- 里程碑徽章
- 难度徽章
- 特殊事件徽章

### 收集品 (Collection)
- 概念卡片
- 数学家卡片
- 定理卡片

## 数据持久化

游戏数据通过 Zustand 的 persist 中间件自动持久化到 localStorage：

```typescript
{
  userGameData: {
    level,           // 等级系统
    coins,           // 金币
    badges,          // 徽章
    achievements,    // 成就
    skillTree,       // 技能树
    collection,      // 收集
    stats            // 统计
  },
  settings: {
    soundEnabled,    // 音效开关
    tutorEnabled,    // 导师开关
    // ...其他设置
  }
}
```

## 扩展开发

### 添加新谜题类型

1. 在 `types/gamification.ts` 添加类型定义
2. 在 `gameService.ts` 添加验证逻辑
3. 在 `PuzzleSolver.tsx` 添加渲染组件

### 添加新徽章

1. 在 `gameService.ts` MOCK_BADGES 中添加徽章定义
2. 在 `gameService.checkBadgeUnlock` 中添加解锁条件
3. 徽章将自动显示在徽章展示界面

### 自定义导师回复

1. 在 `gameService.getTutorMessage` 中添加新的回复模板
2. 根据 personality 和 context 定制回复内容

## 性能优化

1. **懒加载** - 游戏组件按需加载
2. **数据缓存** - 游戏数据本地缓存
3. **防抖节流** - 频繁操作防抖处理
4. **虚拟列表** - 大量数据虚拟滚动

## 注意事项

1. 游戏状态需要及时保存，防止数据丢失
2. 对战模式需要考虑网络延迟处理
3. 导师回复需要人性化，避免重复
4. 成就解锁需要动画反馈

## 未来规划

1. 多人实时对战服务器
2. AI生成个性化谜题
3. 跨平台游戏进度同步
4. 社交功能和好友系统
5. 虚拟现实探索模式
