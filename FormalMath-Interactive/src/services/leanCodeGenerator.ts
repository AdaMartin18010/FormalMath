/**
 * Lean4 代码生成器
 * Lean4 Code Generator
 */

import type {
  ProofConstruction,
  ProofStep,
  ProofState,
  Lean4Code,
  CodeGenerationOptions,
  Tactic,
  ProofGoal,
} from '../types/proofAssistant';

// 默认代码生成选项
const DEFAULT_OPTIONS: CodeGenerationOptions = {
  style: 'structured',
  includeComments: true,
  useMathlib: true,
  indentation: 2,
};

export class LeanCodeGenerator {
  private options: CodeGenerationOptions;

  constructor(options: Partial<CodeGenerationOptions> = {}) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * 生成完整的 Lean4 代码
   */
  generate(proof: ProofConstruction): Lean4Code {
    const imports = this.generateImports();
    const statement = this.generateTheoremStatement(proof);
    const proofBody = this.generateProofBody(proof);
    
    const complete = this.assembleCompleteCode(imports, statement, proofBody, proof);

    return {
      theorem: proof.theoremName,
      statement,
      proof: proofBody,
      complete,
      imports,
    };
  }

  /**
   * 从证明步骤生成代码
   */
  generateFromSteps(
    theoremName: string,
    theoremStatement: string,
    steps: ProofStep[],
    initialState: ProofState
  ): Lean4Code {
    const imports = this.generateImports();
    const statement = `theorem ${theoremName} : ${theoremStatement}`;
    const proofBody = this.stepsToProofCode(steps);
    
    const complete = imports.join('\n') + '\n\n' + statement + ' := by\n' + proofBody;

    return {
      theorem: theoremName,
      statement,
      proof: proofBody,
      complete,
      imports,
    };
  }

  /**
   * 生成导入语句
   */
  private generateImports(): string[] {
    const imports: string[] = [];
    
    if (this.options.useMathlib) {
      imports.push('import Mathlib');
    } else {
      imports.push('import Std.Tactic.Basic');
      imports.push('import Std.Tactic.RCases');
    }

    return imports;
  }

  /**
   * 生成定理声明
   */
  private generateTheoremStatement(proof: ProofConstruction): string {
    const params = this.extractParameters(proof.theoremStatement);
    const paramsStr = params.length > 0 ? ' ' + params.join(' ') : '';
    
    return `theorem ${proof.theoremName}${paramsStr} : ${proof.theoremStatement}`;
  }

  /**
   * 提取参数
   */
  private extractParameters(statement: string): string[] {
    const params: string[] = [];
    // 简单解析: 提取 (x : T) 或 {x : T} 形式的参数
    const paramRegex = /[({]([^})]+)[})]/g;
    let match;
    while ((match = paramRegex.exec(statement)) !== null) {
      params.push(match[0]);
    }
    return params;
  }

  /**
   * 生成证明体
   */
  private generateProofBody(proof: ProofConstruction): string {
    const steps = this.collectAllSteps(proof);
    return this.stepsToProofCode(steps);
  }

  /**
   * 收集所有证明步骤
   */
  private collectAllSteps(proof: ProofConstruction): ProofStep[] {
    // 从当前状态中收集步骤
    return proof.currentState.proofSteps;
  }

  /**
   * 将步骤转换为证明代码
   */
  private stepsToProofCode(steps: ProofStep[]): string {
    if (steps.length === 0) {
      return this.indent('sorry');
    }

    const indent = ' '.repeat(this.options.indentation);
    const lines: string[] = [];

    // 根据样式生成代码
    switch (this.options.style) {
      case 'compact':
        return this.generateCompactStyle(steps);
      
      case 'verbose':
        return this.generateVerboseStyle(steps);
      
      case 'structured':
      default:
        return this.generateStructuredStyle(steps);
    }
  }

  /**
   * 紧凑风格
   */
  private generateCompactStyle(steps: ProofStep[]): string {
    const indent = ' '.repeat(this.options.indentation);
    const tacticStrings = steps.map(s => s.leanCode).filter(Boolean);
    
    if (tacticStrings.length === 0) {
      return indent + 'sorry';
    }

    // 合并相关策略
    const merged = this.mergeTactics(tacticStrings);
    return indent + merged.join('\n' + indent);
  }

  /**
   * 详细风格（带注释）
   */
  private generateVerboseStyle(steps: ProofStep[]): string {
    const indent = ' '.repeat(this.options.indentation);
    const lines: string[] = [];

    steps.forEach((step, index) => {
      if (this.options.includeComments) {
        lines.push('');
        lines.push(`${indent}-- 步骤 ${step.stepNumber}: ${step.description}`);
        lines.push(`${indent}-- 目标: ${step.goalBefore.conclusion}`);
      }
      
      // 处理多行策略
      const tacticLines = step.leanCode.split('\n');
      tacticLines.forEach((line, i) => {
        const prefix = i === 0 ? indent : indent + '  ';
        lines.push(prefix + line);
      });
    });

    if (lines.length === 0) {
      return indent + 'sorry';
    }

    return lines.join('\n');
  }

  /**
   * 结构化风格（推荐）
   */
  private generateStructuredStyle(steps: ProofStep[]): string {
    const indent = ' '.repeat(this.options.indentation);
    const lines: string[] = [];
    const currentIndent = indent;
    let indentLevel = 1;

    const pushLine = (content: string, level: number = indentLevel) => {
      lines.push(' '.repeat(this.options.indentation * level) + content);
    };

    for (let i = 0; i < steps.length; i++) {
      const step = steps[i];
      const tactic = step.tactic;
      
      // 添加空行分隔不同类别的策略
      if (i > 0) {
        const prevTactic = steps[i - 1].tactic;
        if (prevTactic.category !== tactic.category) {
          lines.push('');
        }
      }

      // 处理特殊策略的缩进
      if (this.isBlockOpener(tactic)) {
        pushLine(step.leanCode);
        indentLevel++;
      } else if (this.isBlockCloser(tactic)) {
        indentLevel = Math.max(1, indentLevel - 1);
        pushLine(step.leanCode);
      } else if (this.isBranchTactic(tactic)) {
        // 处理分支策略
        const lines_tactic = step.leanCode.split('\n');
        lines_tactic.forEach((l, idx) => {
          if (idx === 0) {
            pushLine(l);
          } else if (l.trim().startsWith('|')) {
            pushLine(l);
          } else {
            pushLine(l, indentLevel + 1);
          }
        });
      } else {
        pushLine(step.leanCode);
      }
    }

    if (lines.length === 0) {
      return indent + 'sorry';
    }

    return '\n' + lines.join('\n');
  }

  /**
   * 判断是否为块开始策略
   */
  private isBlockOpener(tactic: Tactic): boolean {
    const openers = ['calc', 'by_cases', 'induction', 'match'];
    return openers.includes(tactic.name);
  }

  /**
   * 判断是否为块结束策略
   */
  private isBlockCloser(tactic: Tactic): boolean {
    return tactic.name === 'done' || tactic.name === 'advice';
  }

  /**
   * 判断是否为分支策略
   */
  private isBranchTactic(tactic: Tactic): boolean {
    const branchers = ['cases', 'induction', 'rcases', 'obtain'];
    return branchers.includes(tactic.name);
  }

  /**
   * 合并相关策略
   */
  private mergeTactics(tactics: string[]): string[] {
    const merged: string[] = [];
    
    for (const tactic of tactics) {
      // 尝试与前一个策略合并
      if (merged.length > 0) {
        const last = merged[merged.length - 1];
        const combined = this.tryCombineTactics(last, tactic);
        if (combined) {
          merged[merged.length - 1] = combined;
          continue;
        }
      }
      merged.push(tactic);
    }

    return merged;
  }

  /**
   * 尝试合并策略
   */
  private tryCombineTactics(t1: string, t2: string): string | null {
    // 合并连续的 simp
    if (t1.startsWith('simp') && t2.startsWith('simp')) {
      const rules1 = this.extractRules(t1);
      const rules2 = this.extractRules(t2);
      const allRules = [...new Set([...rules1, ...rules2])];
      return `simp [${allRules.join(', ')}]`;
    }

    // 合并连续的 rw
    if (t1.startsWith('rw') && t2.startsWith('rw')) {
      const rules1 = this.extractRules(t1);
      const rules2 = this.extractRules(t2);
      return `rw [${[...rules1, ...rules2].join(', ')}]`;
    }

    return null;
  }

  /**
   * 提取规则
   */
  private extractRules(tactic: string): string[] {
    const match = tactic.match(/\[(.*?)\]/);
    if (match) {
      return match[1].split(',').map(s => s.trim()).filter(Boolean);
    }
    return [];
  }

  /**
   * 组装完整代码
   */
  private assembleCompleteCode(
    imports: string[],
    statement: string,
    proof: string,
    construction: ProofConstruction
  ): string {
    const lines: string[] = [];
    
    // 文件头注释
    lines.push('/-');
    lines.push(`  定理: ${construction.theoremName}`);
    lines.push(`  描述: ${construction.theoremStatement}`);
    lines.push(`  生成时间: ${new Date().toISOString()}`);
    lines.push('-/');
    lines.push('');

    // 导入
    lines.push(...imports);
    lines.push('');

    // 定理声明
    lines.push(statement + ' := by');
    
    // 证明体
    lines.push(proof);

    return lines.join('\n');
  }

  /**
   * 生成单个策略的 Lean 代码
   */
  generateTacticCode(tactic: Tactic, params: Record<string, string> = {}): string {
    const parts: string[] = [tactic.name];

    // 添加参数
    if (tactic.parameters) {
      for (const param of tactic.parameters) {
        const value = params[param.name] || param.defaultValue;
        if (value) {
          if (param.type === 'list') {
            parts.push(`[${value}]`);
          } else {
            parts.push(value);
          }
        }
      }
    }

    return parts.join(' ');
  }

  /**
   * 格式化策略代码
   */
  formatTacticCode(code: string, level: number = 0): string {
    const indent = ' '.repeat(this.options.indentation * level);
    return code.split('\n').map(line => indent + line).join('\n');
  }

  /**
   * 辅助方法：缩进
   */
  private indent(text: string, level: number = 1): string {
    const spaces = ' '.repeat(this.options.indentation * level);
    return text.split('\n').map(line => spaces + line).join('\n');
  }

  /**
   * 更新选项
   */
  setOptions(options: Partial<CodeGenerationOptions>) {
    this.options = { ...this.options, ...options };
  }

  /**
   * 获取当前选项
   */
  getOptions(): CodeGenerationOptions {
    return { ...this.options };
  }
}

// 常用代码模板
export const LEAN_TEMPLATES = {
  // 基础定理模板
  basicTheorem: (name: string, statement: string, proof: string) => `
import Mathlib

theorem ${name} : ${statement} := by
  ${proof}
`,

  // 归纳证明模板
  inductionProof: (name: string, statement: string, baseCase: string, indStep: string) => `
import Mathlib

theorem ${name} : ${statement} := by
  intro n
  induction n with
  | zero =>
    ${baseCase}
  | succ n ih =>
    ${indStep}
`,

  // 案例分析模板
  caseAnalysis: (name: string, statement: string, cases: string[]) => `
import Mathlib

theorem ${name} : ${statement} := by
  by_cases h
  · -- 情况 1
    ${cases[0] || 'sorry'}
  · -- 情况 2
    ${cases[1] || 'sorry'}
`,

  // 存在性证明模板
  existenceProof: (name: string, statement: string, witness: string, proof: string) => `
import Mathlib

theorem ${name} : ${statement} := by
  exists ${witness}
  ${proof}
`,

  // 反证法模板
  contradictionProof: (name: string, statement: string, proof: string) => `
import Mathlib

theorem ${name} : ${statement} := by
  by_contra h
  push_neg at h
  ${proof}
  contradiction
`,
};

// 导出单例
export const leanCodeGenerator = new LeanCodeGenerator();
