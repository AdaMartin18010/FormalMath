// ==================== 答案验证服务 ====================

import type {
  Exercise,
  ExerciseType,
  ValidationResult,
  ValidatorConfig,
  BlankItem,
  ExerciseOption,
} from '../types/exercise';

/** 默认验证器配置 */
const defaultConfig: ValidatorConfig = {
  caseSensitive: false,
  ignoreWhitespace: true,
  numericalTolerance: 0.01,
  partialCreditEnabled: true,
};

/**
 * 答案验证服务
 * 提供各种题型的答案验证逻辑
 */
export class ExerciseValidator {
  private config: ValidatorConfig;

  constructor(config: Partial<ValidatorConfig> = {}) {
    this.config = { ...defaultConfig, ...config };
  }

  /**
   * 验证答案
   */
  validate(exercise: Exercise, userAnswer: unknown): ValidationResult {
    switch (exercise.type) {
      case 'single_choice':
        return this.validateSingleChoice(exercise, userAnswer);
      case 'multiple_choice':
        return this.validateMultipleChoice(exercise, userAnswer);
      case 'fill_blank':
        return this.validateFillBlank(exercise, userAnswer);
      case 'calculation':
        return this.validateCalculation(exercise, userAnswer);
      case 'proof':
        return this.validateProof(exercise, userAnswer);
      case 'matching':
        return this.validateMatching(exercise, userAnswer);
      case 'ordering':
        return this.validateOrdering(exercise, userAnswer);
      case 'true_false':
        return this.validateTrueFalse(exercise, userAnswer);
      default:
        return {
          isCorrect: false,
          score: 0,
          feedback: '不支持的题型',
        };
    }
  }

  /**
   * 验证单选题
   */
  private validateSingleChoice(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctAnswer = exercise.correctAnswer as string;
    const selectedOption = userAnswer as string;

    const isCorrect = this.normalizeString(selectedOption) === this.normalizeString(correctAnswer);

    return {
      isCorrect,
      score: isCorrect ? 100 : 0,
      feedback: isCorrect ? '回答正确！' : '回答错误。',
      correctAnswer: isCorrect ? undefined : correctAnswer,
    };
  }

  /**
   * 验证多选题
   */
  private validateMultipleChoice(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctAnswers = (exercise.correctAnswer as string[]).map(a => this.normalizeString(a));
    const selectedAnswers = (userAnswer as string[]).map(a => this.normalizeString(a));

    const correctCount = selectedAnswers.filter(a => correctAnswers.includes(a)).length;
    const wrongCount = selectedAnswers.filter(a => !correctAnswers.includes(a)).length;
    const missedCount = correctAnswers.filter(a => !selectedAnswers.includes(a)).length;

    const totalCorrect = correctAnswers.length;
    
    // 计算得分
    let score = 0;
    if (this.config.partialCreditEnabled) {
      // 部分得分：选对得分，选错扣分
      const pointsPerOption = 100 / totalCorrect;
      score = Math.max(0, (correctCount * pointsPerOption) - (wrongCount * pointsPerOption * 0.5));
    } else {
      score = (correctCount === totalCorrect && wrongCount === 0) ? 100 : 0;
    }

    const isCorrect = score >= 100;

    let feedback = '';
    if (isCorrect) {
      feedback = '回答正确！';
    } else if (score > 0) {
      feedback = `部分正确。您选对了 ${correctCount}/${totalCorrect} 个选项。`;
    } else {
      feedback = '回答错误。';
    }

    return {
      isCorrect,
      score: Math.round(score),
      feedback,
      correctAnswer: isCorrect ? undefined : correctAnswers,
      partialCredit: score > 0 && score < 100 ? score : undefined,
    };
  }

  /**
   * 验证填空题
   */
  private validateFillBlank(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const blanks = exercise.blanks || [];
    const userAnswers = userAnswer as Record<string, string>;

    let totalScore = 0;
    const blankResults: { id: string; isCorrect: boolean; userAnswer: string; correctAnswer: string }[] = [];

    for (const blank of blanks) {
      const userValue = this.normalizeString(userAnswers[blank.id] || '');
      const correctValue = this.normalizeString(blank.answer);
      
      let isBlankCorrect = false;
      
      // 检查主答案
      if (userValue === correctValue) {
        isBlankCorrect = true;
      } else if (blank.alternatives) {
        // 检查替代答案
        isBlankCorrect = blank.alternatives.some(alt => 
          this.normalizeString(alt) === userValue
        );
      }

      blankResults.push({
        id: blank.id,
        isCorrect: isBlankCorrect,
        userAnswer: userValue,
        correctAnswer: correctValue,
      });

      if (isBlankCorrect) {
        totalScore += 100 / blanks.length;
      }
    }

    const isCorrect = totalScore >= 100;
    const score = Math.round(totalScore);

    // 生成反馈
    let feedback = '';
    if (isCorrect) {
      feedback = '所有填空都正确！';
    } else {
      const wrongBlanks = blankResults.filter(r => !r.isCorrect);
      feedback = `有 ${wrongBlanks.length} 个填空错误。`;
    }

    return {
      isCorrect,
      score,
      feedback,
      correctAnswer: isCorrect ? undefined : blankResults.reduce((acc, r) => {
        acc[r.id] = r.correctAnswer;
        return acc;
      }, {} as Record<string, string>),
      partialCredit: score > 0 && score < 100 ? score : undefined,
    };
  }

  /**
   * 验证计算题
   */
  private validateCalculation(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctValue = parseFloat(exercise.correctAnswer as string);
    const userValue = parseFloat(userAnswer as string);

    if (isNaN(userValue)) {
      return {
        isCorrect: false,
        score: 0,
        feedback: '请输入有效的数值。',
      };
    }

    const tolerance = exercise.blanks?.[0]?.tolerance || this.config.numericalTolerance;
    const isCorrect = Math.abs(userValue - correctValue) <= tolerance * Math.abs(correctValue);

    // 计算得分（根据误差）
    let score = 0;
    if (isCorrect) {
      score = 100;
    } else {
      const error = Math.abs(userValue - correctValue) / Math.abs(correctValue);
      score = Math.max(0, 100 - error * 100);
    }

    return {
      isCorrect,
      score: Math.round(score),
      feedback: isCorrect ? '计算正确！' : '计算结果有误，请检查您的计算过程。',
      correctAnswer: isCorrect ? undefined : correctValue,
      partialCredit: score > 0 && score < 100 ? Math.round(score) : undefined,
    };
  }

  /**
   * 验证证明题
   */
  private validateProof(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    // 证明题通常需要人工评审或AI评估
    // 这里提供基础的结构验证
    const proofText = (userAnswer as string) || '';
    const minLength = 50; // 最小字数要求

    if (proofText.length < minLength) {
      return {
        isCorrect: false,
        score: 0,
        feedback: `证明过程太短，请提供更详细的证明（至少 ${minLength} 字符）。`,
      };
    }

    // 检查是否包含关键步骤
    const keyPoints = exercise.keyPoints || [];
    const mentionedPoints = keyPoints.filter(point => 
      proofText.toLowerCase().includes(point.toLowerCase())
    );

    const coverage = mentionedPoints.length / keyPoints.length;
    const score = Math.min(100, Math.round(coverage * 100));

    return {
      isCorrect: score >= 80,
      score,
      feedback: score >= 80 
        ? '证明结构完整，涵盖了主要的关键点。' 
        : `证明可以进一步完善，建议包含以下关键点：${keyPoints.filter(p => !mentionedPoints.includes(p)).join('、')}`,
      partialCredit: score > 0 && score < 100 ? score : undefined,
    };
  }

  /**
   * 验证配对题
   */
  private validateMatching(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctPairs = exercise.correctAnswer as Record<string, string>;
    const userPairs = userAnswer as Record<string, string>;

    const totalPairs = Object.keys(correctPairs).length;
    let correctCount = 0;

    for (const [key, value] of Object.entries(correctPairs)) {
      if (this.normalizeString(userPairs[key] || '') === this.normalizeString(value)) {
        correctCount++;
      }
    }

    const score = Math.round((correctCount / totalPairs) * 100);
    const isCorrect = score === 100;

    return {
      isCorrect,
      score,
      feedback: isCorrect 
        ? '所有配对都正确！' 
        : `您正确配对了 ${correctCount}/${totalPairs} 项。`,
      correctAnswer: isCorrect ? undefined : correctPairs,
      partialCredit: score > 0 && score < 100 ? score : undefined,
    };
  }

  /**
   * 验证排序题
   */
  private validateOrdering(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctOrder = exercise.correctAnswer as string[];
    const userOrder = userAnswer as string[];

    // 检查完全匹配
    const isPerfectMatch = correctOrder.every((item, index) => 
      this.normalizeString(item) === this.normalizeString(userOrder[index] || '')
    );

    if (isPerfectMatch) {
      return {
        isCorrect: true,
        score: 100,
        feedback: '排序完全正确！',
      };
    }

    // 计算相邻正确率
    let adjacentCorrect = 0;
    for (let i = 0; i < correctOrder.length - 1; i++) {
      const correctIndex1 = userOrder.findIndex(item => 
        this.normalizeString(item) === this.normalizeString(correctOrder[i])
      );
      const correctIndex2 = userOrder.findIndex(item => 
        this.normalizeString(item) === this.normalizeString(correctOrder[i + 1])
      );
      
      if (correctIndex1 !== -1 && correctIndex2 !== -1 && correctIndex2 === correctIndex1 + 1) {
        adjacentCorrect++;
      }
    }

    const score = Math.round((adjacentCorrect / (correctOrder.length - 1)) * 100);

    return {
      isCorrect: false,
      score,
      feedback: `排序部分正确，有 ${adjacentCorrect}/${correctOrder.length - 1} 对相邻关系正确。`,
      correctAnswer: correctOrder,
      partialCredit: score,
    };
  }

  /**
   * 验证判断题
   */
  private validateTrueFalse(
    exercise: Exercise,
    userAnswer: unknown
  ): ValidationResult {
    const correctAnswer = exercise.correctAnswer as boolean;
    const userSelection = userAnswer as boolean;

    const isCorrect = userSelection === correctAnswer;

    return {
      isCorrect,
      score: isCorrect ? 100 : 0,
      feedback: isCorrect ? '判断正确！' : '判断错误。',
      correctAnswer: isCorrect ? undefined : correctAnswer,
    };
  }

  /**
   * 字符串规范化
   */
  private normalizeString(str: string): string {
    if (!str) return '';
    
    let normalized = str.trim();
    
    if (!this.config.caseSensitive) {
      normalized = normalized.toLowerCase();
    }
    
    if (this.config.ignoreWhitespace) {
      normalized = normalized.replace(/\s+/g, ' ');
    }
    
    return normalized;
  }

  /**
   * 更新配置
   */
  updateConfig(newConfig: Partial<ValidatorConfig>): void {
    this.config = { ...this.config, ...newConfig };
  }

  /**
   * 获取当前配置
   */
  getConfig(): ValidatorConfig {
    return { ...this.config };
  }
}

/** 导出单例实例 */
export const exerciseValidator = new ExerciseValidator();

/** 便捷验证函数 */
export function validateAnswer(
  exercise: Exercise,
  userAnswer: unknown,
  config?: Partial<ValidatorConfig>
): ValidationResult {
  const validator = config ? new ExerciseValidator(config) : exerciseValidator;
  return validator.validate(exercise, userAnswer);
}

export default ExerciseValidator;
