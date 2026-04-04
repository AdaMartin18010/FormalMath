/**
 * 定理证明助手模块导出
 * Proof Assistant Module Exports
 */

// 主组件
export { ProofAssistant } from './index';
export { default } from './index';

// 子组件
export { ProofStateView } from './ProofStateView';
export { TacticPanel } from './TacticPanel';
export { LeanCodeEditor } from './LeanCodeEditor';

// 重新导出类型
export type {
  ProofAssistantProps,
  ProofStateViewProps,
  TacticPanelProps,
  LeanCodeEditorProps,
} from '../../types/proofAssistant';
