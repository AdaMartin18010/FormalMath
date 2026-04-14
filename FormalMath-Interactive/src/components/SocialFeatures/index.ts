// @ts-nocheck
// 社交功能模块导出

// 社交分享
export { SocialShare, ShareButton, AchievementShareCard } from './SocialShare';
export type { SocialShareProps, SharePlatform, ShareButtonProps, AchievementShareCardProps } from './SocialShare';

// Open Graph 和 Twitter Cards
export { OpenGraphMeta, mathContentMeta, generateConceptMeta, generateGraphMeta } from './OpenGraphMeta';
export type { OpenGraphMetaProps } from './OpenGraphMeta';

// 社交登录
export { SocialLogin, SocialLink } from './SocialLogin';
export type { SocialLoginProps, SocialLinkProps, SocialUser, SocialLoginError, SocialProvider } from './SocialLogin';

// 内容嵌入
export { ContentEmbed, EmbedViewer } from './ContentEmbed';
export type { ContentEmbedProps, EmbedConfig, EmbedSize, EmbedTheme, EmbedViewerProps } from './ContentEmbed';

// 现有社交功能
export { StudyGroup } from './StudyGroup';
export type { StudyGroupProps, GroupMember } from './StudyGroup';
export { Leaderboard } from './Leaderboard';
export type { LeaderboardProps, LeaderboardEntry } from './Leaderboard';
export { FriendActivity } from './FriendActivity';
export type { FriendActivityProps, ActivityItem } from './FriendActivity';
export { CollaborationInvite } from './CollaborationInvite';
export type { CollaborationInviteProps } from './CollaborationInvite';

// 社交分享按钮
export { ShareButtons, FloatingShareButton, InlineShareButtons } from './ShareButtons';
export type { ShareButtonsProps, ShareCount } from './ShareButtons';

// 社交元数据钩子
export { useSocialMeta, useShareCount } from './useSocialMeta';
export type { UseSocialMetaOptions, UseShareCountResult } from './useSocialMeta';
