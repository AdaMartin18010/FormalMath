// 通用 hooks
export { useD3 } from './useD3';
export { useMermaid } from './useMermaid';
export { useLocalStorage } from './useLocalStorage';
export { useGraph } from './useGraph';
export { useAdaptive } from './useAdaptive';
export { useDiagnosis } from './useDiagnosis';
export { useEvaluation } from './useEvaluation';
export { useProgressTracking } from './useProgressTracking';

// 协作 hooks
export {
  useConnectionState,
  useOnlineUsers,
  useChatMessages,
  useComments,
  useVersionHistory,
  useSharedLearningPaths,
  useTeamChallenges,
  useCollaborativeEditor,
} from './useCollaboration';

// 移动端 hooks - 重新导出
export {
  useMobileDetect,
  usePWAState,
  useTouchGesture,
  useShakeDetection,
} from './mobile/useMobileDetect';

export {
  usePushNotification,
  useStudyReminder,
} from './mobile/usePushNotification';

export {
  useDarkMode,
  useAutoDarkMode,
} from './mobile/useDarkMode';
