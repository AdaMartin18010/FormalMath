// @ts-nocheck
// 基础组件
export { Header } from './Header';
export { Footer } from './Footer';
export { Sidebar } from './Sidebar';
export { Loading } from './Loading';

// AI 助手组件
export {
  VoiceAssistant,
  VoiceControl,
  MathVoiceReader,
  mathVoiceCommands,
  type VoiceCommand,
  type VoiceAssistantProps,
} from './VoiceInteraction';

// AR 可视化组件
export {
  ARViewer,
  ARGraph3D,
  FunctionPlot3D,
  GeometryPreview,
  sampleARModels,
  generateSampleGraph,
  calculateForceLayout,
  presetFunctions,
  type ARModel,
  type ARViewerProps,
} from './ARVisualization';

// 社交功能组件
export {
  SocialShare,
  ShareButton,
  AchievementShareCard,
  StudyGroup,
  Leaderboard,
  MiniLeaderboard,
  FriendActivity,
  ActiveUsers,
  CollaborationInvite,
  QuickInviteButton,
  InvitationAccept,
  type SocialShareProps,
  type SharePlatform,
  type StudyGroupProps,
  type GroupMember,
} from './SocialFeatures';

// 可视化组件
export {
  D3Graph,
  Graph3D,
  InteractiveTree,
  MermaidChart,
  MatrixTable,
  type GraphData,
  type TreeNode,
} from './visualization';

// AI 助手
export { ChatInterface } from './AIAssistant';

// 协作组件
export {
  CollaborativeEditor,
  ChatPanel,
  UserPresence,
  VersionHistory,
} from './Collaboration';

// 游戏化组件
export {
  BadgeDisplay,
  SkillTree,
  PuzzleCard,
  PuzzleSolver,
  TutorWidget,
} from './Gamification';

// SEO 组件
export {
  SEOHead,
} from './SEO';

// 笔记系统组件
export {
  NoteEditor,
  NoteList,
  NoteSearch,
  NoteAIAssistant,
  NoteShare,
  NoteConceptGraph,
  NotesPage,
  NoteTemplates,
  defaultTemplates,
  LaTeXToolbar,
} from './Notes';

// 视频播放器组件
export {
  VideoPlayer,
  VideoPlayerContainer,
  VideoPlayerPage,
  ChapterMarker,
  SubtitleDisplay,
  SubtitleSelector,
  SubtitleSearch,
  VideoNotes,
  VideoRecommendations,
  CompactRecommendations,
  VideoControls,
  VideoProgressBar,
  VideoPlaylist,
  MiniPlaylist,
  VideoManagement,
  PlaybackStatsView,
  PlaybackHeatmap,
  RetentionCurve,
  type VideoPlayerProps,
  type VideoPlayerContainerProps,
  type ChapterMarkerProps,
  type SubtitleDisplayProps,
  type VideoNotesProps,
  type VideoRecommendationsProps,
  type VideoControlsProps,
  type VideoProgressBarProps,
  type VideoPlaylistProps,
} from './VideoPlayer';
