/**
 * 交互式证明构造服务
 * Interactive Proof Construction Service
 */

import type {
  ProofConstruction,
  ProofState,
  ProofGoal,
  ProofStep,
  ProofBranch,
  ProofCheckpoint,
  Tactic,
  Hypothesis,
  ProofContext,
  ProofAssistantProps,
} from '../types/proofAssistant';
import { proofStrategyEngine } from './proofStrategy';
import { leanCodeGenerator } from './leanCodeGenerator';
import { proofVerifier } from './proofVerifier';

// 证明状态管理
export class ProofConstructionService {
  private construction: ProofConstruction;
  private checkpoints: Map<string, ProofCheckpoint> = new Map();
  private listeners: Set<(construction: ProofConstruction) => void> = new Set();

  constructor(
    theoremName: string,
    theoremStatement: string,
    initialContext?: ProofContext
  ) {
    const initialGoal: ProofGoal = {
      id: this.generateId('goal'),
      conclusion: theoremStatement,
      hypotheses: [],
      isCompleted: false,
    };

    const initialState: ProofState = {
      goals: [initialGoal],
      currentGoalId: initialGoal.id,
      completedGoals: [],
      proofSteps: [],
      context: initialContext || {
        variables: [],
        constants: [],
        definitions: [],
        theorems: [],
      },
    };

    this.construction = {
      id: this.generateId('proof'),
      theoremName,
      theoremStatement,
      currentState: initialState,
      history: [initialState],
      branches: [{
        id: this.generateId('branch'),
        name: 'main',
        goals: [initialGoal],
        isActive: true,
      }],
    };

    // 创建初始检查点
    this.createCheckpoint('initial', initialState, '初始状态');
  }

  // ==================== 核心操作方法 ====================

  /**
   * 应用策略
   */
  async applyTactic(tactic: Tactic, params: Record<string, string> = {}): Promise<boolean> {
    const currentGoal = this.getCurrentGoal();
    if (!currentGoal) {
      console.warn('没有当前目标');
      return false;
    }

    // 生成策略代码
    const leanCode = this.generateTacticCode(tactic, params);

    // 创建新步骤
    const newStep: ProofStep = {
      id: this.generateId('step'),
      stepNumber: this.construction.currentState.proofSteps.length + 1,
      tactic,
      goalBefore: { ...currentGoal },
      goalsAfter: [], // 将在模拟执行后填充
      description: this.generateStepDescription(tactic, params),
      timestamp: Date.now(),
      leanCode,
    };

    // 模拟策略执行（实际应用中会调用 Lean）
    const newGoals = await this.simulateTacticExecution(tactic, currentGoal, params);
    newStep.goalsAfter = newGoals;

    // 更新状态
    const newState = this.updateStateAfterTactic(newStep, newGoals);
    this.saveState(newState);

    // 记录策略使用
    proofStrategyEngine.recordUsage(tactic.id, newGoals.length >= 0);

    // 通知监听器
    this.notifyListeners();

    return true;
  }

  /**
   * 撤销最后一步
   */
  undo(): boolean {
    if (this.construction.history.length <= 1) {
      return false;
    }

    // 移除最后一步
    this.construction.history.pop();
    
    // 恢复到之前的状态
    const previousState = this.construction.history[this.construction.history.length - 1];
    this.construction.currentState = { ...previousState };

    this.notifyListeners();
    return true;
  }

  /**
   * 重做（如果支持）
   */
  redo(): boolean {
    // 暂不支持完整的重做功能
    // 可以通过保存未来的状态列表来实现
    return false;
  }

  /**
   * 切换到指定目标
   */
  switchGoal(goalId: string): boolean {
    const goal = this.construction.currentState.goals.find(g => g.id === goalId);
    if (!goal || goal.isCompleted) {
      return false;
    }

    this.construction.currentState.currentGoalId = goalId;
    this.notifyListeners();
    return true;
  }

  /**
   * 创建分支
   */
  createBranch(name: string, fromGoalId?: string): ProofBranch {
    const parentGoal = fromGoalId 
      ? this.construction.currentState.goals.find(g => g.id === fromGoalId)
      : this.getCurrentGoal();

    const newBranch: ProofBranch = {
      id: this.generateId('branch'),
      name,
      goals: parentGoal ? [parentGoal] : [],
      parentBranchId: this.getActiveBranch()?.id,
      isActive: false,
    };

    this.construction.branches.push(newBranch);
    this.notifyListeners();
    return newBranch;
  }

  /**
   * 切换到分支
   */
  switchBranch(branchId: string): boolean {
    const branch = this.construction.branches.find(b => b.id === branchId);
    if (!branch) {
      return false;
    }

    // 停用所有分支
    this.construction.branches.forEach(b => b.isActive = false);
    
    // 激活目标分支
    branch.isActive = true;
    
    // 更新当前状态
    if (branch.goals.length > 0) {
      this.construction.currentState.currentGoalId = branch.goals[0].id;
    }

    this.notifyListeners();
    return true;
  }

  /**
   * 创建检查点
   */
  createCheckpoint(name: string, state?: ProofState, description?: string): ProofCheckpoint {
    const checkpoint: ProofCheckpoint = {
      id: this.generateId('checkpoint'),
      name,
      state: state || { ...this.construction.currentState },
      timestamp: Date.now(),
      description,
    };

    this.checkpoints.set(checkpoint.id, checkpoint);
    return checkpoint;
  }

  /**
   * 恢复到检查点
   */
  restoreCheckpoint(checkpointId: string): boolean {
    const checkpoint = this.checkpoints.get(checkpointId);
    if (!checkpoint) {
      return false;
    }

    this.construction.currentState = { ...checkpoint.state };
    this.construction.history.push({ ...checkpoint.state });
    
    this.notifyListeners();
    return true;
  }

  /**
   * 完成当前目标
   */
  completeCurrentGoal(): boolean {
    const goal = this.getCurrentGoal();
    if (!goal) {
      return false;
    }

    goal.isCompleted = true;
    this.construction.currentState.completedGoals.push(goal.id);

    // 寻找下一个未完成的目标
    const nextGoal = this.construction.currentState.goals.find(g => !g.isCompleted);
    this.construction.currentState.currentGoalId = nextGoal?.id || null;

    this.notifyListeners();
    return true;
  }

  // ==================== 查询方法 ====================

  /**
   * 获取当前构造
   */
  getConstruction(): ProofConstruction {
    return { ...this.construction };
  }

  /**
   * 获取当前状态
   */
  getCurrentState(): ProofState {
    return { ...this.construction.currentState };
  }

  /**
   * 获取当前目标
   */
  getCurrentGoal(): ProofGoal | null {
    if (!this.construction.currentState.currentGoalId) {
      return null;
    }
    return this.construction.currentState.goals.find(
      g => g.id === this.construction.currentState.currentGoalId
    ) || null;
  }

  /**
   * 获取所有未完成的目标
   */
  getPendingGoals(): ProofGoal[] {
    return this.construction.currentState.goals.filter(g => !g.isCompleted);
  }

  /**
   * 获取活跃分支
   */
  getActiveBranch(): ProofBranch | null {
    return this.construction.branches.find(b => b.isActive) || this.construction.branches[0] || null;
  }

  /**
   * 获取所有检查点
   */
  getCheckpoints(): ProofCheckpoint[] {
    return Array.from(this.checkpoints.values()).sort((a, b) => a.timestamp - b.timestamp);
  }

  /**
   * 检查证明是否完成
   */
  isComplete(): boolean {
    return this.construction.currentState.goals.every(g => g.isCompleted);
  }

  /**
   * 获取当前步骤数
   */
  getStepCount(): number {
    return this.construction.currentState.proofSteps.length;
  }

  // ==================== 订阅方法 ====================

  /**
   * 订阅状态变化
   */
  subscribe(callback: (construction: ProofConstruction) => void): () => void {
    this.listeners.add(callback);
    return () => this.listeners.delete(callback);
  }

  /**
   * 取消订阅
   */
  unsubscribe(callback: (construction: ProofConstruction) => void): void {
    this.listeners.delete(callback);
  }

  private notifyListeners(): void {
    this.listeners.forEach(callback => {
      try {
        callback({ ...this.construction });
      } catch (e) {
        console.error('监听器错误:', e);
      }
    });
  }

  // ==================== 私有辅助方法 ====================

  private generateId(prefix: string): string {
    return `${prefix}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }

  private generateTacticCode(tactic: Tactic, params: Record<string, string>): string {
    const parts: string[] = [tactic.name];

    if (tactic.parameters) {
      for (const param of tactic.parameters) {
        const value = params[param.name] || param.defaultValue;
        if (value && value.trim() !== '') {
          if (param.type === 'list') {
            parts.push(`[${value}]`);
          } else if (param.type === 'expression' && value.includes(' ')) {
            parts.push(`(${value})`);
          } else {
            parts.push(value);
          }
        }
      }
    }

    return parts.join(' ');
  }

  private generateStepDescription(tactic: Tactic, params: Record<string, string>): string {
    let description = tactic.description;
    
    // 如果有参数，添加到描述
    const paramStr = Object.entries(params)
      .filter(([_, v]) => v.trim() !== '')
      .map(([k, v]) => `${k}=${v}`)
      .join(', ');
    
    if (paramStr) {
      description += ` (${paramStr})`;
    }

    return description;
  }

  private async simulateTacticExecution(
    tactic: Tactic, 
    goal: ProofGoal, 
    params: Record<string, string>
  ): Promise<ProofGoal[]> {
    // 模拟策略执行 - 实际应用中会调用 Lean 内核
    // 这里返回模拟的目标转换结果

    switch (tactic.category) {
      case 'introduction':
        return this.simulateIntroTactic(tactic, goal, params);
      
      case 'elimination':
        return this.simulateElimTactic(tactic, goal, params);
      
      case 'rewriting':
        return this.simulateRewriteTactic(tactic, goal, params);
      
      case 'automation':
        return []; // 自动化策略通常完成目标
      
      case 'logic':
        return this.simulateLogicTactic(tactic, goal, params);
      
      default:
        // 默认行为：创建一个模拟的新目标
        return [{
          id: this.generateId('goal'),
          conclusion: `${goal.conclusion} (after ${tactic.name})`,
          hypotheses: [...goal.hypotheses],
          isCompleted: false,
        }];
    }
  }

  private simulateIntroTactic(tactic: Tactic, goal: ProofGoal, params: Record<string, string>): ProofGoal[] {
    if (tactic.name === 'intro' || tactic.name === 'intros') {
      // 模拟引入假设
      const newHypothesis: Hypothesis = {
        id: this.generateId('hyp'),
        name: params.names || 'h',
        type: 'Prop',
      };

      return [{
        id: this.generateId('goal'),
        conclusion: goal.conclusion.replace(/∀.*?,/, '').replace(/.*?→/, '').trim() || 'True',
        hypotheses: [...goal.hypotheses, newHypothesis],
        isCompleted: false,
      }];
    }

    if (tactic.name === 'constructor' || tactic.name === 'split') {
      // 分解合取
      return [
        {
          id: this.generateId('goal'),
          conclusion: `${goal.conclusion} (left)`,
          hypotheses: [...goal.hypotheses],
          isCompleted: false,
        },
        {
          id: this.generateId('goal'),
          conclusion: `${goal.conclusion} (right)`,
          hypotheses: [...goal.hypotheses],
          isCompleted: false,
        },
      ];
    }

    return [goal];
  }

  private simulateElimTactic(tactic: Tactic, goal: ProofGoal, params: Record<string, string>): ProofGoal[] {
    if (tactic.name === 'apply') {
      // 应用定理可能产生新的子目标
      return [{
        id: this.generateId('goal'),
        conclusion: `subgoal of ${params.theorem || 'applied theorem'}`,
        hypotheses: [...goal.hypotheses],
        isCompleted: false,
      }];
    }

    if (tactic.name === 'exact') {
      // exact 完成目标
      return [];
    }

    return [goal];
  }

  private simulateRewriteTactic(tactic: Tactic, goal: ProofGoal, params: Record<string, string>): ProofGoal[] {
    // 重写后目标保持不变（简化模拟）
    return [{
      ...goal,
      id: this.generateId('goal'),
    }];
  }

  private simulateLogicTactic(tactic: Tactic, goal: ProofGoal, params: Record<string, string>): ProofGoal[] {
    if (tactic.name === 'by_contra') {
      const newHypothesis: Hypothesis = {
        id: this.generateId('hyp'),
        name: params.name || 'h',
        type: `¬(${goal.conclusion})`,
      };

      return [{
        id: this.generateId('goal'),
        conclusion: 'False',
        hypotheses: [...goal.hypotheses, newHypothesis],
        isCompleted: false,
      }];
    }

    if (tactic.name === 'exfalso') {
      return [{
        ...goal,
        conclusion: 'False',
        id: this.generateId('goal'),
      }];
    }

    return [goal];
  }

  private updateStateAfterTactic(step: ProofStep, newGoals: ProofGoal[]): ProofState {
    const state = this.construction.currentState;
    
    // 更新目标列表
    const currentGoalIndex = state.goals.findIndex(g => g.id === state.currentGoalId);
    const updatedGoals = [...state.goals];
    
    if (currentGoalIndex >= 0) {
      // 移除已完成的目标
      updatedGoals.splice(currentGoalIndex, 1);
    }
    
    // 添加新产生的目标
    updatedGoals.push(...newGoals);

    const newState: ProofState = {
      goals: updatedGoals,
      currentGoalId: newGoals.length > 0 ? newGoals[0].id : null,
      completedGoals: state.completedGoals,
      proofSteps: [...state.proofSteps, step],
      context: state.context,
    };

    return newState;
  }

  private saveState(state: ProofState): void {
    this.construction.currentState = state;
    this.construction.history.push({ ...state });
  }

  // ==================== 静态工厂方法 ====================

  static create(
    theoremName: string,
    theoremStatement: string,
    initialContext?: ProofContext
  ): ProofConstructionService {
    return new ProofConstructionService(theoremName, theoremStatement, initialContext);
  }

  static fromTemplate(template: string, params: Record<string, string>): ProofConstructionService {
    // 从模板创建证明构造
    const substitutions: Record<string, string> = {
      theorem_add_comm: '∀ (m n : ℕ), m + n = n + m',
      theorem_mul_assoc: '∀ (a b c : ℕ), (a * b) * c = a * (b * c)',
      theorem_nat_induction: '∀ (P : ℕ → Prop), P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n',
    };

    const statement = substitutions[template] || params.statement || 'True';
    const name = params.name || 'theorem_name';

    return new ProofConstructionService(name, statement);
  }
}

// 导出单例工厂
export const proofConstructionService = {
  create: ProofConstructionService.create,
  fromTemplate: ProofConstructionService.fromTemplate,
};
