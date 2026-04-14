// @ts-nocheck
/**
 * 智能提醒服务
 * 提供学习提醒、目标追踪、智能通知等功能
 */

import { openDB, DBSchema, IDBPDatabase } from 'idb';

// 提醒类型
export type ReminderType = 
  | 'daily_goal'      // 每日学习目标
  | 'study_time'      // 学习时间安排
  | 'review'          // 复习提醒
  | 'achievement'     // 成就提醒
  | 'streak'          // 连续学习提醒
  | 'custom';         // 自定义提醒

// 提醒频率
export type ReminderFrequency = 
  | 'once'           // 一次性
  | 'daily'          // 每天
  | 'weekly'         // 每周
  | 'weekdays'       // 工作日
  | 'weekends'       // 周末
  | 'custom';        // 自定义

// 提醒数据
export interface Reminder {
  id: string;
  userId: string;
  type: ReminderType;
  title: string;
  message: string;
  schedule: {
    time: string;           // HH:mm 格式
    frequency: ReminderFrequency;
    customDays?: number[];  // 0-6, 0 = 周日
    startDate?: number;     // 开始日期时间戳
    endDate?: number;       // 结束日期时间戳
  };
  target?: {
    conceptId?: string;     // 关联的概念ID
    goalMinutes?: number;   // 目标学习时长（分钟）
    goalProblems?: number;  // 目标解题数量
  };
  conditions?: {
    minStreak?: number;     // 最小连续天数
    maxStreak?: number;     // 最大连续天数
    lastStudyBefore?: number; // 上次学习距今最大小时数
    progressBelow?: number; // 进度低于百分比
  };
  isActive: boolean;
  createdAt: number;
  updatedAt: number;
  lastTriggered?: number;
  triggerCount: number;
}

// 提醒记录
export interface ReminderLog {
  id: string;
  reminderId: string;
  userId: string;
  triggeredAt: number;
  acknowledgedAt?: number;
  dismissedAt?: number;
  actionTaken?: 'opened' | 'dismissed' | 'snoozed';
  snoozeDuration?: number; // 分钟
}

// 学习目标
export interface LearningGoal {
  id: string;
  userId: string;
  title: string;
  description?: string;
  type: 'daily' | 'weekly' | 'monthly' | 'custom';
  target: {
    studyMinutes?: number;
    problemsSolved?: number;
    conceptsLearned?: number;
    streakDays?: number;
  };
  current: {
    studyMinutes: number;
    problemsSolved: number;
    conceptsLearned: number;
    streakDays: number;
  };
  startDate: number;
  endDate?: number;
  isCompleted: boolean;
  completedAt?: number;
  reminders: string[]; // 关联的提醒ID
}

// 学习统计
export interface LearningStats {
  userId: string;
  date: string; // YYYY-MM-DD
  studyMinutes: number;
  problemsSolved: number;
  conceptsLearned: number;
  streakDay: number;
  lastStudyAt?: number;
}

// IndexedDB Schema
interface ReminderDB extends DBSchema {
  reminders: {
    key: string;
    value: Reminder;
    indexes: { 'by-user': string; 'by-active': string; 'by-type': string };
  };
  reminderLogs: {
    key: string;
    value: ReminderLog;
    indexes: { 'by-reminder': string; 'by-user': string; 'by-date': number };
  };
  goals: {
    key: string;
    value: LearningGoal;
    indexes: { 'by-user': string; 'by-active': string };
  };
  stats: {
    key: string;
    value: LearningStats;
    indexes: { 'by-user': string; 'by-date': string };
  };
}

const DB_NAME = 'FormalMathReminderDB';
const DB_VERSION = 1;

class ReminderService {
  private db: IDBPDatabase<ReminderDB> | null = null;
  private checkInterval: NodeJS.Timeout | null = null;
  private notificationPermission: NotificationPermission = 'default';

  async init(): Promise<void> {
    this.db = await openDB<ReminderDB>(DB_NAME, DB_VERSION, {
      upgrade(db) {
        // 提醒存储
        const reminderStore = db.createObjectStore('reminders', { keyPath: 'id' });
        reminderStore.createIndex('by-user', 'userId');
        reminderStore.createIndex('by-active', 'isActive');
        reminderStore.createIndex('by-type', 'type');

        // 提醒记录存储
        const logStore = db.createObjectStore('reminderLogs', { keyPath: 'id' });
        logStore.createIndex('by-reminder', 'reminderId');
        logStore.createIndex('by-user', 'userId');
        logStore.createIndex('by-date', 'triggeredAt');

        // 目标存储
        const goalStore = db.createObjectStore('goals', { keyPath: 'id' });
        goalStore.createIndex('by-user', 'userId');
        goalStore.createIndex('by-active', 'isCompleted');

        // 统计存储
        const statsStore = db.createObjectStore('stats', { keyPath: 'id' });
        statsStore.createIndex('by-user', 'userId');
        statsStore.createIndex('by-date', 'date');
      },
    });

    // 请求通知权限
    await this.requestNotificationPermission();

    // 启动定时检查
    this.startReminderCheck();
  }

  // ========== 通知权限 ==========

  async requestNotificationPermission(): Promise<NotificationPermission> {
    if (!('Notification' in window)) {
      return 'denied';
    }

    if (Notification.permission === 'granted') {
      this.notificationPermission = 'granted';
      return 'granted';
    }

    if (Notification.permission !== 'denied') {
      const permission = await Notification.requestPermission();
      this.notificationPermission = permission;
      return permission;
    }

    return 'denied';
  }

  // ========== 提醒管理 ==========

  async createReminder(reminder: Omit<Reminder, 'id' | 'createdAt' | 'updatedAt' | 'triggerCount'>): Promise<Reminder> {
    if (!this.db) throw new Error('Database not initialized');

    const newReminder: Reminder = {
      ...reminder,
      id: `reminder-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      createdAt: Date.now(),
      updatedAt: Date.now(),
      triggerCount: 0,
    };

    await this.db.put('reminders', newReminder);
    return newReminder;
  }

  async updateReminder(id: string, updates: Partial<Reminder>): Promise<Reminder> {
    if (!this.db) throw new Error('Database not initialized');

    const existing = await this.db.get('reminders', id);
    if (!existing) throw new Error('Reminder not found');

    const updated: Reminder = {
      ...existing,
      ...updates,
      id,
      updatedAt: Date.now(),
    };

    await this.db.put('reminders', updated);
    return updated;
  }

  async deleteReminder(id: string): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');
    await this.db.delete('reminders', id);
  }

  async getReminder(id: string): Promise<Reminder | undefined> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.get('reminders', id);
  }

  async getUserReminders(userId: string, activeOnly = false): Promise<Reminder[]> {
    if (!this.db) throw new Error('Database not initialized');

    if (activeOnly) {
      const allReminders = await this.db.getAllFromIndex('reminders', 'by-user', userId);
      return allReminders.filter(r => r.isActive);
    }

    return this.db.getAllFromIndex('reminders', 'by-user', userId);
  }

  // ========== 智能提醒检查 ==========

  private startReminderCheck(): void {
    // 每分钟检查一次
    this.checkInterval = setInterval(() => {
      this.checkAndTriggerReminders();
    }, 60000);

    // 立即检查一次
    this.checkAndTriggerReminders();
  }

  private async checkAndTriggerReminders(): Promise<void> {
    if (!this.db) return;

    const now = new Date();
    const currentTime = `${String(now.getHours()).padStart(2, '0')}:${String(now.getMinutes()).padStart(2, '0')}`;
    const currentDay = now.getDay();
    const currentTimestamp = now.getTime();

    const activeReminders = await this.db.getAllFromIndex('reminders', 'by-active', 1);

    for (const reminder of activeReminders) {
      if (!reminder.isActive) continue;

      const schedule = reminder.schedule;
      
      // 检查时间
      if (schedule.time !== currentTime) continue;

      // 检查频率
      if (!this.shouldTriggerToday(schedule, currentDay, currentTimestamp)) continue;

      // 检查条件
      if (reminder.conditions && !(await this.checkConditions(reminder.conditions, reminder.userId))) continue;

      // 检查是否已经触发过今天
      if (await this.hasTriggeredToday(reminder.id)) continue;

      // 触发提醒
      await this.triggerReminder(reminder);
    }
  }

  private shouldTriggerToday(
    schedule: Reminder['schedule'], 
    currentDay: number, 
    currentTimestamp: number
  ): boolean {
    // 检查日期范围
    if (schedule.startDate && currentTimestamp < schedule.startDate) return false;
    if (schedule.endDate && currentTimestamp > schedule.endDate) return false;

    switch (schedule.frequency) {
      case 'once':
        return true;
      case 'daily':
        return true;
      case 'weekly':
        // 假设每周日触发，或者根据创建时间计算
        return currentDay === 0;
      case 'weekdays':
        return currentDay >= 1 && currentDay <= 5;
      case 'weekends':
        return currentDay === 0 || currentDay === 6;
      case 'custom':
        return schedule.customDays?.includes(currentDay) ?? false;
      default:
        return false;
    }
  }

  private async checkConditions(conditions: Reminder['conditions'], userId: string): Promise<boolean> {
    const today = new Date().toISOString().split('T')[0];
    const stats = await this.getStats(userId, today);

    if (conditions.minStreak !== undefined && (stats?.streakDay || 0) < conditions.minStreak) {
      return false;
    }

    if (conditions.maxStreak !== undefined && (stats?.streakDay || 0) > conditions.maxStreak) {
      return false;
    }

    if (conditions.lastStudyBefore !== undefined && stats?.lastStudyAt) {
      const hoursSinceLastStudy = (Date.now() - stats.lastStudyAt) / (1000 * 60 * 60);
      if (hoursSinceLastStudy < conditions.lastStudyBefore) {
        return false;
      }
    }

    return true;
  }

  private async hasTriggeredToday(reminderId: string): Promise<boolean> {
    if (!this.db) return false;

    const today = new Date();
    today.setHours(0, 0, 0, 0);
    const tomorrow = new Date(today);
    tomorrow.setDate(tomorrow.getDate() + 1);

    const logs = await this.db.getAllFromIndex('reminderLogs', 'by-reminder', reminderId);
    
    return logs.some(log => 
      log.triggeredAt >= today.getTime() && log.triggeredAt < tomorrow.getTime()
    );
  }

  private async triggerReminder(reminder: Reminder): Promise<void> {
    // 显示通知
    await this.showNotification(reminder);

    // 记录触发
    await this.logReminderTrigger(reminder);

    // 更新触发次数
    reminder.triggerCount++;
    reminder.lastTriggered = Date.now();
    await this.db?.put('reminders', reminder);

    // 如果是一次性提醒，标记为非活跃
    if (reminder.schedule.frequency === 'once') {
      reminder.isActive = false;
      await this.db?.put('reminders', reminder);
    }
  }

  private async showNotification(reminder: Reminder): Promise<void> {
    if (this.notificationPermission !== 'granted') return;

    const notification = new Notification(reminder.title, {
      body: reminder.message,
      icon: '/icons/icon-192x192.png',
      badge: '/icons/icon-72x72.png',
      tag: reminder.id,
      requireInteraction: reminder.type === 'study_time',
      data: {
        reminderId: reminder.id,
        type: reminder.type,
        target: reminder.target,
      },
    });

    notification.onclick = () => {
      window.focus();
      notification.close();
      // 可以在这里添加导航逻辑
    };
  }

  private async logReminderTrigger(reminder: Reminder): Promise<void> {
    if (!this.db) return;

    const log: ReminderLog = {
      id: `log-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      reminderId: reminder.id,
      userId: reminder.userId,
      triggeredAt: Date.now(),
    };

    await this.db.put('reminderLogs', log);
  }

  // ========== 提醒响应 ==========

  async acknowledgeReminder(logId: string): Promise<void> {
    if (!this.db) return;

    const log = await this.db.get('reminderLogs', logId);
    if (log) {
      log.acknowledgedAt = Date.now();
      log.actionTaken = 'opened';
      await this.db.put('reminderLogs', log);
    }
  }

  async dismissReminder(logId: string): Promise<void> {
    if (!this.db) return;

    const log = await this.db.get('reminderLogs', logId);
    if (log) {
      log.dismissedAt = Date.now();
      log.actionTaken = 'dismissed';
      await this.db.put('reminderLogs', log);
    }
  }

  async snoozeReminder(logId: string, minutes: number): Promise<void> {
    if (!this.db) return;

    const log = await this.db.get('reminderLogs', logId);
    if (log) {
      log.actionTaken = 'snoozed';
      log.snoozeDuration = minutes;
      await this.db.put('reminderLogs', log);

      // 可以在这里设置延迟再次提醒
    }
  }

  // ========== 目标管理 ==========

  async createGoal(goal: Omit<LearningGoal, 'id' | 'current' | 'isCompleted' | 'completedAt'>): Promise<LearningGoal> {
    if (!this.db) throw new Error('Database not initialized');

    const newGoal: LearningGoal = {
      ...goal,
      id: `goal-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      current: {
        studyMinutes: 0,
        problemsSolved: 0,
        conceptsLearned: 0,
        streakDays: 0,
      },
      isCompleted: false,
    };

    await this.db.put('goals', newGoal);
    return newGoal;
  }

  async updateGoalProgress(
    goalId: string, 
    progress: Partial<LearningGoal['current']>
  ): Promise<LearningGoal> {
    if (!this.db) throw new Error('Database not initialized');

    const goal = await this.db.get('goals', goalId);
    if (!goal) throw new Error('Goal not found');

    goal.current = { ...goal.current, ...progress };

    // 检查目标是否完成
    const isCompleted = this.checkGoalCompletion(goal);
    if (isCompleted && !goal.isCompleted) {
      goal.isCompleted = true;
      goal.completedAt = Date.now();
      
      // 发送完成通知
      await this.showGoalCompletionNotification(goal);
    }

    await this.db.put('goals', goal);
    return goal;
  }

  private checkGoalCompletion(goal: LearningGoal): boolean {
    const { target, current } = goal;
    
    if (target.studyMinutes && current.studyMinutes < target.studyMinutes) return false;
    if (target.problemsSolved && current.problemsSolved < target.problemsSolved) return false;
    if (target.conceptsLearned && current.conceptsLearned < target.conceptsLearned) return false;
    if (target.streakDays && current.streakDays < target.streakDays) return false;
    
    return true;
  }

  private async showGoalCompletionNotification(goal: LearningGoal): Promise<void> {
    if (this.notificationPermission !== 'granted') return;

    new Notification('🎉 目标达成！', {
      body: `恭喜！你已完成目标：${goal.title}`,
      icon: '/icons/icon-192x192.png',
    });
  }

  // ========== 统计管理 ==========

  async recordStudySession(
    userId: string, 
    minutes: number, 
    problemsSolved = 0, 
    conceptsLearned = 0
  ): Promise<void> {
    if (!this.db) return;

    const today = new Date().toISOString().split('T')[0];
    const id = `${userId}-${today}`;

    let stats = await this.db.get('stats', id);
    
    if (!stats) {
      stats = {
        userId,
        date: today,
        studyMinutes: 0,
        problemsSolved: 0,
        conceptsLearned: 0,
        streakDay: await this.calculateStreakDay(userId),
      };
    }

    stats.studyMinutes += minutes;
    stats.problemsSolved += problemsSolved;
    stats.conceptsLearned += conceptsLearned;
    stats.lastStudyAt = Date.now();

    await this.db.put('stats', stats);

    // 更新活跃目标
    await this.updateActiveGoals(userId, stats);
  }

  private async calculateStreakDay(userId: string): Promise<number> {
    if (!this.db) return 1;

    const yesterday = new Date();
    yesterday.setDate(yesterday.getDate() - 1);
    const yesterdayStr = yesterday.toISOString().split('T')[0];
    const yesterdayId = `${userId}-${yesterdayStr}`;

    const yesterdayStats = await this.db.get('stats', yesterdayId);
    return (yesterdayStats?.streakDay || 0) + 1;
  }

  private async updateActiveGoals(userId: string, stats: LearningStats): Promise<void> {
    if (!this.db) return;

    const goals = await this.db.getAllFromIndex('goals', 'by-user', userId);
    const activeGoals = goals.filter(g => !g.isCompleted);

    for (const goal of activeGoals) {
      await this.updateGoalProgress(goal.id, {
        studyMinutes: stats.studyMinutes,
        problemsSolved: stats.problemsSolved,
        conceptsLearned: stats.conceptsLearned,
        streakDays: stats.streakDay,
      });
    }
  }

  async getStats(userId: string, date: string): Promise<LearningStats | undefined> {
    if (!this.db) return undefined;
    return this.db.get('stats', `${userId}-${date}`);
  }

  async getStatsRange(userId: string, startDate: string, endDate: string): Promise<LearningStats[]> {
    if (!this.db) return [];

    const allStats = await this.db.getAllFromIndex('stats', 'by-user', userId);
    return allStats.filter(s => s.date >= startDate && s.date <= endDate);
  }

  // ========== 智能建议 ==========

  async getSmartSuggestions(userId: string): Promise<string[]> {
    const suggestions: string[] = [];
    const today = new Date().toISOString().split('T')[0];
    const stats = await this.getStats(userId, today);

    // 基于今天学习情况的建议
    if (!stats || stats.studyMinutes === 0) {
      suggestions.push('今天还没有学习，开始你的学习之旅吧！');
    } else if (stats.studyMinutes < 30) {
      suggestions.push(`今天已学习 ${stats.studyMinutes} 分钟，再坚持一下就能达到每日目标！`);
    }

    // 基于连续学习天数的建议
    if (stats?.streakDay && stats.streakDay >= 7) {
      suggestions.push(`太棒了！你已经连续学习 ${stats.streakDay} 天，继续保持！`);
    }

    // 基于目标完成情况的建议
    const goals = await this.getActiveGoals(userId);
    for (const goal of goals) {
      const progress = this.calculateGoalProgress(goal);
      if (progress > 0.8) {
        suggestions.push(`目标"${goal.title}"即将完成，再努力一下！`);
      }
    }

    return suggestions;
  }

  private async getActiveGoals(userId: string): Promise<LearningGoal[]> {
    if (!this.db) return [];
    const goals = await this.db.getAllFromIndex('goals', 'by-user', userId);
    return goals.filter(g => !g.isCompleted);
  }

  private calculateGoalProgress(goal: LearningGoal): number {
    const { target, current } = goal;
    let totalProgress = 0;
    let count = 0;

    if (target.studyMinutes) {
      totalProgress += current.studyMinutes / target.studyMinutes;
      count++;
    }
    if (target.problemsSolved) {
      totalProgress += current.problemsSolved / target.problemsSolved;
      count++;
    }
    if (target.conceptsLearned) {
      totalProgress += current.conceptsLearned / target.conceptsLearned;
      count++;
    }
    if (target.streakDays) {
      totalProgress += current.streakDays / target.streakDays;
      count++;
    }

    return count > 0 ? totalProgress / count : 0;
  }

  // ========== 清理 ==========

  stopReminderCheck(): void {
    if (this.checkInterval) {
      clearInterval(this.checkInterval);
      this.checkInterval = null;
    }
  }
}

// 单例实例
export const reminderService = new ReminderService();

// 预设提醒模板
export const reminderTemplates = {
  dailyStudy: (time: string): Partial<Reminder> => ({
    type: 'daily_goal',
    title: '今日学习目标',
    message: '该开始学习啦！完成今天的学习目标，保持学习 streak。',
    schedule: {
      time,
      frequency: 'daily',
    },
    target: {
      goalMinutes: 30,
    },
    isActive: true,
  }),

  review: (time: string): Partial<Reminder> => ({
    type: 'review',
    title: '复习时间',
    message: '温故而知新，是时候复习一下之前学过的内容了。',
    schedule: {
      time,
      frequency: 'weekdays',
    },
    isActive: true,
  }),

  streak: (time: string): Partial<Reminder> => ({
    type: 'streak',
    title: '连续学习提醒',
    message: '别忘了今天的学习，保持你的连续学习记录！',
    schedule: {
      time,
      frequency: 'daily',
    },
    conditions: {
      lastStudyBefore: 20, // 20小时未学习
    },
    isActive: true,
  }),
};

export default reminderService;
