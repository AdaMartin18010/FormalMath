// ==================== 错题本服务 ====================

import type {
  MistakeRecord,
  ErrorType,
  MasteryLevel,
  ReviewRecord,
  Exercise,
  ValidationResult,
} from '../types/exercise';

/**
 * 存储键名
 */
const STORAGE_KEY = 'formalmath_mistake_book';

/**
 * 掌握度阈值
 */
const MASTERY_THRESHOLDS = {
  weak: { max: 30, reviews: 0 },
  developing: { min: 30, max: 70, reviews: 1 },
  mastered: { min: 70, reviews: 3 },
  forgotten: { max: 40, daysSinceReview: 14 },
};

/**
 * 间隔重复间隔（天）
 */
const SPACED_REPETITION_INTERVALS = [1, 3, 7, 14, 30];

/**
 * 错题本服务
 */
export class MistakeBookService {
  private mistakes: Map<string, MistakeRecord> = new Map();

  constructor() {
    this.loadFromStorage();
  }

  /**
   * 添加错题记录
   */
  addMistake(
    exerciseId: string,
    userId: string,
    wrongAnswer: unknown,
    errorType: ErrorType,
    validationResult: ValidationResult
  ): MistakeRecord {
    const existingMistake = this.getMistakeByExercise(exerciseId, userId);
    
    if (existingMistake) {
      // 更新已有记录
      return this.updateExistingMistake(existingMistake, wrongAnswer, errorType);
    }

    // 创建新记录
    const newMistake: MistakeRecord = {
      id: this.generateId(),
      exerciseId,
      userId,
      wrongAnswer,
      errorType,
      errorAnalysis: validationResult.detailedFeedback,
      firstWrongAt: new Date().toISOString(),
      lastWrongAt: new Date().toISOString(),
      reviewCount: 0,
      reviewHistory: [],
      masteryLevel: 'weak',
      nextReviewDate: this.calculateNextReviewDate(0),
      isResolved: false,
    };

    this.mistakes.set(newMistake.id, newMistake);
    this.saveToStorage();

    return newMistake;
  }

  /**
   * 更新已有错题记录
   */
  private updateExistingMistake(
    mistake: MistakeRecord,
    wrongAnswer: unknown,
    errorType: ErrorType
  ): MistakeRecord {
    mistake.wrongAnswer = wrongAnswer;
    mistake.errorType = errorType;
    mistake.lastWrongAt = new Date().toISOString();
    mistake.isResolved = false;
    
    // 降低掌握度
    if (mistake.masteryLevel === 'mastered') {
      mistake.masteryLevel = 'developing';
    } else if (mistake.masteryLevel === 'developing') {
      mistake.masteryLevel = 'weak';
    }

    // 重置复习日期
    mistake.nextReviewDate = this.calculateNextReviewDate(0);

    this.mistakes.set(mistake.id, mistake);
    this.saveToStorage();

    return mistake;
  }

  /**
   * 记录复习结果
   */
  recordReview(
    mistakeId: string,
    isCorrect: boolean,
    timeSpent: number,
    hintsUsed: number
  ): MistakeRecord | null {
    const mistake = this.mistakes.get(mistakeId);
    if (!mistake) return null;

    const reviewRecord: ReviewRecord = {
      timestamp: new Date().toISOString(),
      isCorrect,
      timeSpent,
      hintsUsed,
    };

    mistake.reviewHistory.push(reviewRecord);
    mistake.reviewCount++;
    mistake.lastWrongAt = reviewRecord.timestamp;

    // 更新掌握度
    mistake.masteryLevel = this.calculateMasteryLevel(mistake);
    
    // 更新下次复习日期
    mistake.nextReviewDate = this.calculateNextReviewDate(mistake.reviewCount);
    
    // 检查是否已解决
    if (mistake.masteryLevel === 'mastered' && mistake.reviewCount >= 3) {
      mistake.isResolved = true;
    }

    this.mistakes.set(mistakeId, mistake);
    this.saveToStorage();

    return mistake;
  }

  /**
   * 获取所有错题
   */
  getAllMistakes(userId: string): MistakeRecord[] {
    return Array.from(this.mistakes.values())
      .filter(m => m.userId === userId)
      .sort((a, b) => new Date(b.lastWrongAt).getTime() - new Date(a.lastWrongAt).getTime());
  }

  /**
   * 获取待复习的错题
   */
  getPendingReviews(userId: string): MistakeRecord[] {
    const now = new Date().toISOString();
    return this.getAllMistakes(userId)
      .filter(m => !m.isResolved && m.nextReviewDate <= now);
  }

  /**
   * 根据练习ID获取错题
   */
  getMistakeByExercise(exerciseId: string, userId: string): MistakeRecord | undefined {
    return Array.from(this.mistakes.values()).find(
      m => m.exerciseId === exerciseId && m.userId === userId
    );
  }

  /**
   * 按错误类型统计
   */
  getStatisticsByErrorType(userId: string): Record<ErrorType, number> {
    const stats: Record<ErrorType, number> = {
      concept_misunderstanding: 0,
      calculation_error: 0,
      formula_misapplication: 0,
      logic_error: 0,
      careless_mistake: 0,
      knowledge_gap: 0,
      other: 0,
    };

    this.getAllMistakes(userId).forEach(mistake => {
      stats[mistake.errorType]++;
    });

    return stats;
  }

  /**
   * 按掌握度统计
   */
  getStatisticsByMastery(userId: string): Record<MasteryLevel, number> {
    const stats: Record<MasteryLevel, number> = {
      weak: 0,
      developing: 0,
      mastered: 0,
      forgotten: 0,
    };

    this.getAllMistakes(userId).forEach(mistake => {
      stats[mistake.masteryLevel]++;
    });

    return stats;
  }

  /**
   * 获取错题统计概览
   */
  getMistakeOverview(userId: string) {
    const allMistakes = this.getAllMistakes(userId);
    const pendingReviews = this.getPendingReviews(userId);
    const resolvedMistakes = allMistakes.filter(m => m.isResolved);

    return {
      totalMistakes: allMistakes.length,
      resolvedMistakes: resolvedMistakes.length,
      pendingReviews: pendingReviews.length,
      resolutionRate: allMistakes.length > 0 
        ? Math.round((resolvedMistakes.length / allMistakes.length) * 100) 
        : 0,
      byErrorType: this.getStatisticsByErrorType(userId),
      byMastery: this.getStatisticsByMastery(userId),
    };
  }

  /**
   * 获取推荐的复习错题
   */
  getRecommendedMistakes(userId: string, limit: number = 5): MistakeRecord[] {
    const pendingReviews = this.getPendingReviews(userId);
    
    // 按优先级排序
    return pendingReviews
      .sort((a, b) => {
        // 优先复习掌握度低的
        const masteryPriority = this.getMasteryPriority(a.masteryLevel) - 
                               this.getMasteryPriority(b.masteryLevel);
        if (masteryPriority !== 0) return masteryPriority;
        
        // 其次按复习次数少的
        return a.reviewCount - b.reviewCount;
      })
      .slice(0, limit);
  }

  /**
   * 删除错题记录
   */
  deleteMistake(mistakeId: string): boolean {
    const deleted = this.mistakes.delete(mistakeId);
    if (deleted) {
      this.saveToStorage();
    }
    return deleted;
  }

  /**
   * 清空用户的所有错题
   */
  clearUserMistakes(userId: string): void {
    for (const [id, mistake] of this.mistakes.entries()) {
      if (mistake.userId === userId) {
        this.mistakes.delete(id);
      }
    }
    this.saveToStorage();
  }

  /**
   * 计算掌握度
   */
  private calculateMasteryLevel(mistake: MistakeRecord): MasteryLevel {
    const recentReviews = mistake.reviewHistory.slice(-5);
    if (recentReviews.length === 0) return 'weak';

    const correctCount = recentReviews.filter(r => r.isCorrect).length;
    const accuracy = correctCount / recentReviews.length;

    // 检查是否遗忘
    const daysSinceLastReview = this.getDaysSince(mistake.reviewHistory[mistake.reviewHistory.length - 1]?.timestamp);
    if (accuracy > 0.8 && daysSinceLastReview > 14) {
      return 'forgotten';
    }

    if (accuracy >= 0.8 && mistake.reviewCount >= 3) {
      return 'mastered';
    } else if (accuracy >= 0.5) {
      return 'developing';
    }

    return 'weak';
  }

  /**
   * 计算下次复习日期
   */
  private calculateNextReviewDate(reviewCount: number): string {
    const interval = SPACED_REPETITION_INTERVALS[Math.min(reviewCount, SPACED_REPETITION_INTERVALS.length - 1)];
    const nextDate = new Date();
    nextDate.setDate(nextDate.getDate() + interval);
    return nextDate.toISOString();
  }

  /**
   * 获取掌握度优先级（数值越小优先级越高）
   */
  private getMasteryPriority(level: MasteryLevel): number {
    const priorities: Record<MasteryLevel, number> = {
      weak: 0,
      developing: 1,
      mastered: 3,
      forgotten: 2, // 遗忘的需要优先复习
    };
    return priorities[level];
  }

  /**
   * 获取距离某天的天数
   */
  private getDaysSince(dateString: string): number {
    if (!dateString) return 0;
    const date = new Date(dateString);
    const now = new Date();
    return Math.floor((now.getTime() - date.getTime()) / (1000 * 60 * 60 * 24));
  }

  /**
   * 生成唯一ID
   */
  private generateId(): string {
    return `mistake_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }

  /**
   * 从本地存储加载
   */
  private loadFromStorage(): void {
    try {
      const data = localStorage.getItem(STORAGE_KEY);
      if (data) {
        const parsed = JSON.parse(data) as MistakeRecord[];
        parsed.forEach(mistake => {
          this.mistakes.set(mistake.id, mistake);
        });
      }
    } catch (error) {
      console.error('Failed to load mistake book from storage:', error);
    }
  }

  /**
   * 保存到本地存储
   */
  private saveToStorage(): void {
    try {
      const data = Array.from(this.mistakes.values());
      localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
    } catch (error) {
      console.error('Failed to save mistake book to storage:', error);
    }
  }
}

/** 导出单例实例 */
export const mistakeBookService = new MistakeBookService();

/** 错误类型标签 */
export const ERROR_TYPE_LABELS: Record<ErrorType, string> = {
  concept_misunderstanding: '概念理解错误',
  calculation_error: '计算错误',
  formula_misapplication: '公式误用',
  logic_error: '逻辑错误',
  careless_mistake: '粗心错误',
  knowledge_gap: '知识漏洞',
  other: '其他错误',
};

/** 掌握度标签 */
export const MASTERY_LEVEL_LABELS: Record<MasteryLevel, string> = {
  weak: '薄弱',
  developing: '提升中',
  mastered: '已掌握',
  forgotten: '已遗忘',
};

/** 掌握度颜色 */
export const MASTERY_LEVEL_COLORS: Record<MasteryLevel, string> = {
  weak: 'text-red-500 bg-red-50',
  developing: 'text-yellow-500 bg-yellow-50',
  mastered: 'text-green-500 bg-green-50',
  forgotten: 'text-gray-500 bg-gray-50',
};

export default MistakeBookService;
