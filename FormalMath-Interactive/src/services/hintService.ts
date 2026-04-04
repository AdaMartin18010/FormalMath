// ==================== 逐步提示服务 ====================

import type { Exercise, StepHint, MistakeRecord, ErrorType } from '../types/exercise';

/**
 * 提示生成器接口
 */
interface HintGenerator {
  generate(exercise: Exercise, step: number, previousHints: StepHint[]): StepHint;
}

/**
 * 单选题提示生成器
 */
class SingleChoiceHintGenerator implements HintGenerator {
  generate(exercise: Exercise, step: number): StepHint {
    const options = exercise.options || [];
    const correctOption = options.find(o => o.id === exercise.correctAnswer);
    
    switch (step) {
      case 0:
        return {
          step: 0,
          title: '理解题目',
          content: '仔细阅读题目，理解问题的核心要求。这道题考查的是：' + exercise.keyPoints[0],
          revealed: false,
        };
      case 1:
        // 排除明显错误的选项
        const wrongOptions = options.filter(o => o.id !== exercise.correctAnswer);
        const eliminateCount = Math.min(2, wrongOptions.length);
        return {
          step: 1,
          title: '排除法',
          content: `有 ${eliminateCount} 个选项明显不符合题意，可以尝试排除。`,
          revealed: false,
        };
      case 2:
        return {
          step: 2,
          title: '正确答案范围',
          content: `正确答案在选项 ${correctOption ? String.fromCharCode(65 + options.indexOf(correctOption)) : '?'} 中。`,
          revealed: false,
        };
      default:
        return {
          step,
          title: '最终提示',
          content: `正确答案是：${correctOption?.content || exercise.correctAnswer}`,
          revealed: false,
        };
    }
  }
}

/**
 * 填空题提示生成器
 */
class FillBlankHintGenerator implements HintGenerator {
  generate(exercise: Exercise, step: number): StepHint {
    const blanks = exercise.blanks || [];
    
    switch (step) {
      case 0:
        return {
          step: 0,
          title: '分析题意',
          content: `这道题需要填写 ${blanks.length} 个空。首先理解题目要求，确定需要求解的量。`,
          revealed: false,
        };
      case 1:
        return {
          step: 1,
          title: '关键知识点',
          content: `本题涉及的关键概念：${exercise.keyPoints.join('、')}`,
          revealed: false,
        };
      case 2:
        // 提示第一个空
        if (blanks.length > 0) {
          const firstBlank = blanks[0];
          return {
            step: 2,
            title: '第一个空的提示',
            content: `第一个空需要填写与"${firstBlank.answer.substring(0, 2)}..."相关的内容。`,
            revealed: false,
          };
        }
        break;
      case 3:
        // 给出答案类型
        return {
          step: 3,
          title: '答案类型',
          content: '填空答案可以是：数值、公式、概念名称或简短描述。',
          revealed: false,
        };
    }
    
    return {
      step,
      title: '最终提示',
      content: `参考答案是：${blanks.map(b => b.answer).join(', ')}`,
      revealed: false,
    };
  }
}

/**
 * 计算题提示生成器
 */
class CalculationHintGenerator implements HintGenerator {
  generate(exercise: Exercise, step: number): StepHint {
    switch (step) {
      case 0:
        return {
          step: 0,
          title: '识别已知条件',
          content: '列出题目中给出的所有已知条件和待求量。',
          revealed: false,
        };
      case 1:
        return {
          step: 1,
          title: '选择公式',
          content: `本题可能用到的公式或定理：${exercise.keyPoints.join('、')}`,
          revealed: false,
        };
      case 2:
        return {
          step: 2,
          title: '解题思路',
          content: exercise.solution.substring(0, 50) + '...',
          revealed: false,
        };
      case 3:
        return {
          step: 3,
          title: '检查计算',
          content: '注意单位换算和数值精度，检查计算过程中的符号。',
          revealed: false,
        };
    }
    
    return {
      step,
      title: '最终提示',
      content: `正确答案是：${exercise.correctAnswer}`,
      revealed: false,
    };
  }
}

/**
 * 证明题提示生成器
 */
class ProofHintGenerator implements HintGenerator {
  generate(exercise: Exercise, step: number): StepHint {
    switch (step) {
      case 0:
        return {
          step: 0,
          title: '理解命题',
          content: '明确命题的条件（已知）和结论（求证）。',
          revealed: false,
        };
      case 1:
        return {
          step: 1,
          title: '证明方法',
          content: `可以考虑的证明方法：直接证明、反证法、数学归纳法等。`,
          revealed: false,
        };
      case 2:
        return {
          step: 2,
          title: '关键步骤',
          content: `证明中需要用到的关键知识点：${exercise.keyPoints.slice(0, 2).join('、')}`,
          revealed: false,
        };
      case 3:
        return {
          step: 3,
          title: '证明框架',
          content: exercise.solution.substring(0, 80) + '...',
          revealed: false,
        };
    }
    
    return {
      step,
      title: '完整证明',
      content: exercise.solution,
      revealed: false,
    };
  }
}

/**
 * 通用提示生成器
 */
class GenericHintGenerator implements HintGenerator {
  generate(exercise: Exercise, step: number): StepHint {
    switch (step) {
      case 0:
        return {
          step: 0,
          title: '审题',
          content: '仔细阅读题目，理解题目要求和限制条件。',
          revealed: false,
        };
      case 1:
        return {
          step: 1,
          title: '关联知识',
          content: `本题涉及的知识点：${exercise.keyPoints.join('、')}`,
          revealed: false,
        };
      case 2:
        return {
          step: 2,
          title: '解题思路',
          content: exercise.solution.substring(0, 100) + '...',
          revealed: false,
        };
    }
    
    return {
      step,
      title: '参考答案',
      content: `正确答案是：${JSON.stringify(exercise.correctAnswer)}`,
      revealed: false,
    };
  }
}

/**
 * 提示服务
 */
export class HintService {
  private generators: Map<string, HintGenerator> = new Map();

  constructor() {
    // 注册各题型的提示生成器
    this.generators.set('single_choice', new SingleChoiceHintGenerator());
    this.generators.set('fill_blank', new FillBlankHintGenerator());
    this.generators.set('calculation', new CalculationHintGenerator());
    this.generators.set('proof', new ProofHintGenerator());
  }

  /**
   * 获取提示
   */
  getHint(exercise: Exercise, revealedCount: number): StepHint | null {
    if (revealedCount >= exercise.maxHints) {
      return null;
    }

    const generator = this.generators.get(exercise.type) || new GenericHintGenerator();
    const revealedHints = exercise.hints.filter(h => h.revealed);
    
    return generator.generate(exercise, revealedCount, revealedHints);
  }

  /**
   * 获取所有预设提示
   */
  getAllHints(exercise: Exercise): StepHint[] {
    const hints: StepHint[] = [];
    const generator = this.generators.get(exercise.type) || new GenericHintGenerator();
    
    for (let i = 0; i < exercise.maxHints; i++) {
      const hint = generator.generate(exercise, i, hints);
      hints.push(hint);
    }
    
    return hints;
  }

  /**
   * 根据错误类型生成针对性提示
   */
  getErrorSpecificHint(errorType: ErrorType, exercise: Exercise): string {
    const hints: Record<ErrorType, string> = {
      concept_misunderstanding: `概念提示：${exercise.keyPoints[0]} 的核心含义是...`,
      calculation_error: '计算提示：请仔细检查每一步的运算，特别是符号和数值。',
      formula_misapplication: `公式提示：使用 ${exercise.keyPoints[0]} 时需要注意适用条件。`,
      logic_error: '逻辑提示：请检查推理过程的严密性，确保每一步都有依据。',
      careless_mistake: '细心提示：建议重新审题，注意题目中的细节和限制条件。',
      knowledge_gap: `知识提示：本题涉及 ${exercise.prerequisites[0]}，建议先复习相关内容。`,
      other: '提示：请再仔细思考一下，有问题可以查看相关知识点的讲解。',
    };

    return hints[errorType] || hints.other;
  }

  /**
   * 生成动态提示
   * 根据用户的部分答案给出针对性提示
   */
  generateDynamicHint(
    exercise: Exercise,
    partialAnswer: unknown,
    errorPattern?: string
  ): string {
    // 根据用户的部分答案分析可能的困难点
    const dynamicHints: string[] = [];

    if (errorPattern) {
      dynamicHints.push(`您似乎在"${errorPattern}"方面遇到了困难。`);
    }

    // 根据题型添加特定提示
    switch (exercise.type) {
      case 'calculation':
        dynamicHints.push('建议：分步计算，每一步都检查是否正确。');
        break;
      case 'proof':
        dynamicHints.push('建议：先写出已知条件和要证明的结论，然后寻找连接它们的路径。');
        break;
      case 'single_choice':
        dynamicHints.push('建议：尝试排除明显错误的选项。');
        break;
    }

    return dynamicHints.join('\n');
  }
}

/** 导出单例实例 */
export const hintService = new HintService();

export default HintService;
