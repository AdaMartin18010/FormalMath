/**
 * 证明验证系统
 * Proof Verification System
 */

import type {
  ProofConstruction,
  ProofStep,
  ProofState,
  VerificationResult,
  ProofError,
  ProofWarning,
  CodeLocation,
  Lean4Code,
  ProofGoal,
} from '../types/proofAssistant';

// 验证配置
interface VerificationConfig {
  timeout: number;
  maxSteps: number;
  strictMode: boolean;
  checkCompleteness: boolean;
  checkTermination: boolean;
}

const DEFAULT_CONFIG: VerificationConfig = {
  timeout: 30000,
  maxSteps: 1000,
  strictMode: false,
  checkCompleteness: true,
  checkTermination: true,
};

// 模拟的 Lean 内核验证器
// 在实际应用中，这将连接到 Lean4 服务器或使用 WASM 版本的 Lean
export class ProofVerifier {
  private config: VerificationConfig;
  private verificationQueue: Map<string, VerificationTask> = new Map();

  constructor(config: Partial<VerificationConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * 验证完整证明
   */
  async verifyProof(proof: ProofConstruction): Promise<VerificationResult> {
    const startTime = Date.now();
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    try {
      // 1. 语法验证
      const syntaxErrors = this.verifySyntax(proof);
      errors.push(...syntaxErrors);

      // 2. 结构验证
      const structureErrors = this.verifyStructure(proof);
      errors.push(...structureErrors);

      // 3. 逻辑验证（模拟）
      if (errors.length === 0) {
        const logicResult = await this.verifyLogic(proof);
        errors.push(...logicResult.errors);
        warnings.push(...logicResult.warnings);
      }

      // 4. 完整性验证
      if (this.config.checkCompleteness) {
        const completenessErrors = this.verifyCompleteness(proof);
        errors.push(...completenessErrors);
      }

      // 5. 步骤验证
      const stepsResult = await this.verifySteps(proof.currentState.proofSteps);
      errors.push(...stepsResult.errors);
      warnings.push(...stepsResult.warnings);

      const elapsed = Date.now() - startTime;

      return {
        success: errors.length === 0,
        proofState: proof.currentState,
        errors,
        warnings,
        elapsed,
        stepsVerified: proof.currentState.proofSteps.length,
      };

    } catch (error) {
      const elapsed = Date.now() - startTime;
      errors.push({
        type: 'runtime',
        message: `验证过程中发生错误: ${error instanceof Error ? error.message : String(error)}`,
      });

      return {
        success: false,
        proofState: proof.currentState,
        errors,
        warnings,
        elapsed,
        stepsVerified: 0,
      };
    }
  }

  /**
   * 验证 Lean4 代码
   */
  async verifyLeanCode(code: Lean4Code): Promise<VerificationResult> {
    const startTime = Date.now();
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    // 1. 基本语法检查
    const syntaxCheck = this.checkBasicSyntax(code.complete);
    if (!syntaxCheck.valid) {
      errors.push({
        type: 'syntax',
        message: syntaxCheck.error || '语法错误',
        location: syntaxCheck.location,
      });
    }

    // 2. 检查常见的 Lean4 代码问题
    const commonIssues = this.checkCommonIssues(code);
    errors.push(...commonIssues.errors);
    warnings.push(...commonIssues.warnings);

    // 3. 模拟类型检查
    const typeCheck = await this.simulateTypeCheck(code);
    errors.push(...typeCheck.errors);
    warnings.push(...typeCheck.warnings);

    const elapsed = Date.now() - startTime;

    return {
      success: errors.length === 0,
      proofState: this.createMockProofState(),
      errors,
      warnings,
      elapsed,
      stepsVerified: this.countProofSteps(code.proof),
    };
  }

  /**
   * 验证单个步骤
   */
  async verifyStep(step: ProofStep, previousState: ProofState): Promise<VerificationResult> {
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    // 检查策略是否适用
    const applicabilityCheck = this.checkTacticApplicability(step.tactic, previousState);
    if (!applicabilityCheck.valid) {
      errors.push({
        type: 'logic',
        message: applicabilityCheck.reason || '策略在当前状态下不适用',
        stepNumber: step.stepNumber,
      });
    }

    // 检查目标转换是否合理
    const transitionCheck = this.checkGoalTransition(
      step.goalBefore,
      step.goalsAfter,
      step.tactic
    );
    if (!transitionCheck.valid) {
      warnings.push({
        stepNumber: step.stepNumber,
        message: transitionCheck.message || '目标转换可能需要检查',
      });
    }

    return {
      success: errors.length === 0,
      proofState: { ...previousState, proofSteps: [...previousState.proofSteps, step] },
      errors,
      warnings,
      elapsed: 0,
      stepsVerified: 1,
    };
  }

  /**
   * 增量验证
   */
  async incrementalVerify(
    previousResult: VerificationResult,
    newStep: ProofStep
  ): Promise<VerificationResult> {
    const lastState = previousResult.proofState;
    const stepResult = await this.verifyStep(newStep, lastState);

    // 合并结果
    return {
      success: previousResult.success && stepResult.success,
      proofState: stepResult.proofState,
      errors: [...previousResult.errors, ...stepResult.errors],
      warnings: [...previousResult.warnings, ...stepResult.warnings],
      elapsed: previousResult.elapsed + stepResult.elapsed,
      stepsVerified: previousResult.stepsVerified + 1,
    };
  }

  // ==================== 私有验证方法 ====================

  /**
   * 语法验证
   */
  private verifySyntax(proof: ProofConstruction): ProofError[] {
    const errors: ProofError[] = [];

    // 检查定理名称
    if (!proof.theoremName || !/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(proof.theoremName)) {
      errors.push({
        type: 'syntax',
        message: `定理名称 "${proof.theoremName}" 不符合命名规范`,
        suggestions: ['定理名称必须以字母或下划线开头，只能包含字母、数字和下划线'],
      });
    }

    // 检查定理声明
    if (!proof.theoremStatement || proof.theoremStatement.trim() === '') {
      errors.push({
        type: 'syntax',
        message: '定理声明不能为空',
      });
    }

    // 检查步骤
    proof.currentState.proofSteps.forEach((step, index) => {
      if (!step.leanCode || step.leanCode.trim() === '') {
        errors.push({
          type: 'syntax',
          message: `步骤 ${step.stepNumber} 没有生成有效的 Lean 代码`,
          stepNumber: step.stepNumber,
        });
      }

      // 检查策略名称
      if (!step.tactic.name || step.tactic.name.trim() === '') {
        errors.push({
          type: 'syntax',
          message: `步骤 ${step.stepNumber} 缺少策略名称`,
          stepNumber: step.stepNumber,
        });
      }
    });

    return errors;
  }

  /**
   * 结构验证
   */
  private verifyStructure(proof: ProofConstruction): ProofError[] {
    const errors: ProofError[] = [];
    const steps = proof.currentState.proofSteps;

    // 检查步骤连续性
    for (let i = 0; i < steps.length; i++) {
      if (steps[i].stepNumber !== i + 1) {
        errors.push({
          type: 'logic',
          message: `步骤编号不连续: 期望 ${i + 1}, 实际 ${steps[i].stepNumber}`,
          stepNumber: steps[i].stepNumber,
        });
      }
    }

    // 检查目标一致性
    for (let i = 1; i < steps.length; i++) {
      const prevStep = steps[i - 1];
      const currStep = steps[i];

      // 当前步骤的目标应该来自前一步骤的目标转换
      const prevGoals = prevStep.goalsAfter;
      const currGoal = currStep.goalBefore;

      const goalExists = prevGoals.some(g => g.id === currGoal.id);
      if (!goalExists && prevGoals.length > 0) {
        errors.push({
          type: 'logic',
          message: `步骤 ${currStep.stepNumber} 的目标与前一步骤的结果不一致`,
          stepNumber: currStep.stepNumber,
        });
      }
    }

    return errors;
  }

  /**
   * 逻辑验证（模拟）
   */
  private async verifyLogic(proof: ProofConstruction): Promise<{ errors: ProofError[]; warnings: ProofWarning[] }> {
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    // 模拟异步验证
    await this.simulateDelay(100);

    // 检查明显的逻辑错误
    const steps = proof.currentState.proofSteps;

    for (const step of steps) {
      // 检查是否使用了未定义的变量
      const undefinedVars = this.findUndefinedVariables(step, proof.currentState);
      if (undefinedVars.length > 0) {
        errors.push({
          type: 'logic',
          message: `步骤 ${step.stepNumber} 使用了未定义的变量: ${undefinedVars.join(', ')}`,
          stepNumber: step.stepNumber,
        });
      }

      // 检查是否应用了错误的策略
      const wrongTactic = this.checkWrongTacticUsage(step);
      if (wrongTactic) {
        warnings.push({
          stepNumber: step.stepNumber,
          message: wrongTactic.message,
          suggestion: wrongTactic.suggestion,
        });
      }
    }

    return { errors, warnings };
  }

  /**
   * 完整性验证
   */
  private verifyCompleteness(proof: ProofConstruction): ProofError[] {
    const errors: ProofError[] = [];

    const incompleteGoals = proof.currentState.goals.filter(g => !g.isCompleted);
    
    if (incompleteGoals.length > 0) {
      errors.push({
        type: 'logic',
        message: `证明未完成: 还有 ${incompleteGoals.length} 个目标需要证明`,
        suggestions: incompleteGoals.map(g => `完成目标: ${g.conclusion.substring(0, 50)}...`),
      });
    }

    // 检查是否有悬空的分支
    const branches = proof.branches;
    const danglingBranches = branches.filter(b => b.isActive && b.goals.length > 0);
    
    if (danglingBranches.length > 0) {
      errors.push({
        type: 'logic',
        message: `有 ${danglingBranches.length} 个未完成的证明分支`,
      });
    }

    return errors;
  }

  /**
   * 验证步骤序列
   */
  private async verifySteps(steps: ProofStep[]): Promise<{ errors: ProofError[]; warnings: ProofWarning[] }> {
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    for (const step of steps) {
      // 检查策略代码格式
      const codeCheck = this.checkTacticCode(step.leanCode);
      if (!codeCheck.valid) {
        errors.push({
          type: 'syntax',
          message: codeCheck.error || '策略代码格式错误',
          stepNumber: step.stepNumber,
          location: codeCheck.location,
        });
      }

      // 检查是否有重复的策略
      const duplicate = steps.find(s => 
        s.stepNumber < step.stepNumber && 
        s.leanCode === step.leanCode &&
        s.goalBefore.conclusion === step.goalBefore.conclusion
      );
      
      if (duplicate && this.config.strictMode) {
        warnings.push({
          stepNumber: step.stepNumber,
          message: '可能存在冗余的步骤',
          suggestion: '检查是否可以简化证明',
        });
      }
    }

    return { errors, warnings };
  }

  // ==================== 辅助检查方法 ====================

  private checkBasicSyntax(code: string): { valid: boolean; error?: string; location?: CodeLocation } {
    // 检查括号匹配
    const brackets = { '(': ')', '[': ']', '{': '}' };
    const stack: string[] = [];
    
    for (let i = 0; i < code.length; i++) {
      const char = code[i];
      if (char in brackets) {
        stack.push(char);
      } else if (Object.values(brackets).includes(char)) {
        const last = stack.pop();
        if (!last || brackets[last as keyof typeof brackets] !== char) {
          return {
            valid: false,
            error: '括号不匹配',
            location: { line: this.getLineNumber(code, i), column: this.getColumnNumber(code, i) },
          };
        }
      }
    }

    if (stack.length > 0) {
      return {
        valid: false,
        error: '括号不匹配: 有未闭合的括号',
      };
    }

    // 检查关键字
    const invalidKeywords = ['sorry', 'admit'];
    for (const keyword of invalidKeywords) {
      if (code.includes(keyword) && this.config.strictMode) {
        return {
          valid: false,
          error: `代码中包含 ${keyword}，这可能表示不完整的证明`,
        };
      }
    }

    return { valid: true };
  }

  private checkCommonIssues(code: Lean4Code): { errors: ProofError[]; warnings: ProofWarning[] } {
    const errors: ProofError[] = [];
    const warnings: ProofWarning[] = [];

    // 检查是否缺少导入
    if (!code.imports.some(i => i.includes('Mathlib') || i.includes('Std'))) {
      warnings.push({
        message: '建议添加 Mathlib 或 Std 导入以获得更好的支持',
      });
    }

    // 检查证明是否为空
    if (!code.proof || code.proof.trim() === '' || code.proof.includes('sorry')) {
      errors.push({
        type: 'logic',
        message: '证明体为空或包含 sorry',
        suggestions: ['完成证明', '使用 admit 标记待证明的部分'],
      });
    }

    return { errors, warnings };
  }

  private async simulateTypeCheck(code: Lean4Code): Promise<{ errors: ProofError[]; warnings: ProofWarning[] }> {
    // 模拟类型检查 - 实际应用中会调用 Lean 内核
    await this.simulateDelay(50);
    return { errors: [], warnings: [] };
  }

  private checkTacticApplicability(tactic: any, state: ProofState): { valid: boolean; reason?: string } {
    // 检查策略是否适用于当前状态
    if (!tactic || !tactic.name) {
      return { valid: false, reason: '无效的策略' };
    }

    // 特定策略的检查
    switch (tactic.name) {
      case 'intro':
      case 'intros': {
        // 检查目标是否允许引入
        const currentGoal = state.goals.find(g => g.id === state.currentGoalId);
        if (currentGoal && !currentGoal.conclusion.includes('→') && !currentGoal.conclusion.includes('∀')) {
          return { valid: false, reason: '当前目标不支持引入操作' };
        }
        break;
      }
    }

    return { valid: true };
  }

  private checkGoalTransition(
    before: ProofGoal,
    after: ProofGoal[],
    tactic: any
  ): { valid: boolean; message?: string } {
    // 检查目标转换是否合理
    // 这是一个简化的检查，实际应用需要更复杂的逻辑
    return { valid: true };
  }

  private findUndefinedVariables(step: ProofStep, state: ProofState): string[] {
    const undefinedVars: string[] = [];
    const definedVars = new Set([
      ...state.context.variables.map(v => v.name),
      ...state.context.constants.map(c => c.name),
      ...step.goalBefore.hypotheses.map(h => h.name),
    ]);

    // 简单检查策略中使用的变量
    const code = step.leanCode;
    const words = code.split(/\s+/);
    
    // 这里应该进行更精确的解析
    // 简化版本：假设策略参数可能包含变量引用

    return undefinedVars;
  }

  private checkWrongTacticUsage(step: ProofStep): { message: string; suggestion: string } | null {
    // 检查策略误用
    const { tactic, goalBefore } = step;

    // 示例检查：对简单等式使用 induction
    if (tactic.name === 'induction' && goalBefore.conclusion.includes('=') && !goalBefore.conclusion.includes('∀')) {
      return {
        message: '对简单等式使用 induction 可能不是最佳选择',
        suggestion: '考虑使用 ring、field 或 rw 策略',
      };
    }

    return null;
  }

  private checkTacticCode(code: string): { valid: boolean; error?: string; location?: CodeLocation } {
    if (!code || code.trim() === '') {
      return { valid: false, error: '策略代码为空' };
    }

    // 检查策略名称是否有效
    const firstWord = code.trim().split(/\s+/)[0];
    const validTactics = [
      'intro', 'intros', 'apply', 'exact', 'refine', 'constructor', 'split',
      'left', 'right', 'exists', 'cases', 'induction', 'rw', 'rewrite',
      'simp', 'simp_all', 'linarith', 'nlinarith', 'omega', 'ring', 'field',
      'norm_num', 'rfl', 'tauto', 'itauto', 'aesop', 'by_contra', 'exfalso',
      'calc', 'done', 'advice', 'sorry', 'admit', 'have', 'let', 'show',
      'by_cases', 'by_contra', 'contradiction', 'assumption', 'clear',
      'rename', 'revert', 'generalize', 'specialize', 'use', 'trivial',
    ];

    if (!validTactics.includes(firstWord)) {
      return {
        valid: false,
        error: `未知策略: ${firstWord}`,
      };
    }

    return { valid: true };
  }

  // ==================== 工具方法 ====================

  private getLineNumber(code: string, index: number): number {
    return code.substring(0, index).split('\n').length;
  }

  private getColumnNumber(code: string, index: number): number {
    const lines = code.substring(0, index).split('\n');
    return lines[lines.length - 1].length + 1;
  }

  private async simulateDelay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  private createMockProofState(): ProofState {
    return {
      goals: [],
      currentGoalId: null,
      completedGoals: [],
      proofSteps: [],
      context: {
        variables: [],
        constants: [],
        definitions: [],
        theorems: [],
      },
    };
  }

  private countProofSteps(proofCode: string): number {
    // 简单计数非空行
    return proofCode.split('\n').filter(line => line.trim() !== '' && !line.trim().startsWith('--')).length;
  }
}

// 验证任务接口
interface VerificationTask {
  id: string;
  proof: ProofConstruction;
  startTime: number;
  status: 'pending' | 'running' | 'completed' | 'error';
  result?: VerificationResult;
}

// 导出单例
export const proofVerifier = new ProofVerifier();
