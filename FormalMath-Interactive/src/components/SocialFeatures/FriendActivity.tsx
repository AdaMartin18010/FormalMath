import React from 'react';
import { 
  UserPlus, 
  Check, 
  X, 
  MoreHorizontal,
  Clock,
  BookOpen,
  Trophy,
  Target,
  MessageCircle
} from 'lucide-react';

// 活动类型
type ActivityType = 
  | 'study_start'
  | 'study_complete'
  | 'achievement_earned'
  | 'goal_reached'
  | 'streak_milestone'
  | 'concept_mastered'
  | 'problem_solved'
  | 'joined_group';

// 好友活动
interface FriendActivity {
  id: string;
  userId: string;
  userName: string;
  userAvatar?: string;
  type: ActivityType;
  timestamp: string;
  details: {
    conceptName?: string;
    achievementName?: string;
    achievementIcon?: string;
    studyMinutes?: number;
    problemsCount?: number;
    streakDays?: number;
    goalTitle?: string;
    groupName?: string;
  };
}

// 好友请求
interface FriendRequest {
  id: string;
  userId: string;
  name: string;
  avatar?: string;
  mutualFriends: number;
  sentAt: string;
}

interface FriendActivityProps {
  activities: FriendActivity[];
  requests?: FriendRequest[];
  onAcceptRequest?: (requestId: string) => void;
  onDeclineRequest?: (requestId: string) => void;
  onViewProfile?: (userId: string) => void;
  onReact?: (activityId: string, reaction: string) => void;
  onComment?: (activityId: string, comment: string) => void;
  className?: string;
}

const activityConfig: Record<ActivityType, {
  icon: React.ReactNode;
  color: string;
  bgColor: string;
  getMessage: (activity: FriendActivity) => string;
}> = {
  study_start: {
    icon: <BookOpen size={16} />,
    color: 'text-blue-500',
    bgColor: 'bg-blue-100',
    getMessage: (a) => `开始学习 ${a.details.conceptName || '新概念'}`,
  },
  study_complete: {
    icon: <Check size={16} />,
    color: 'text-green-500',
    bgColor: 'bg-green-100',
    getMessage: (a) => `完成了 ${a.details.studyMinutes} 分钟的学习`,
  },
  achievement_earned: {
    icon: <Trophy size={16} />,
    color: 'text-yellow-500',
    bgColor: 'bg-yellow-100',
    getMessage: (a) => `获得了成就「${a.details.achievementName}」`,
  },
  goal_reached: {
    icon: <Target size={16} />,
    color: 'text-purple-500',
    bgColor: 'bg-purple-100',
    getMessage: (a) => `达成了目标：${a.details.goalTitle}`,
  },
  streak_milestone: {
    icon: '🔥',
    color: 'text-orange-500',
    bgColor: 'bg-orange-100',
    getMessage: (a) => `连续学习 ${a.details.streakDays} 天！`,
  },
  concept_mastered: {
    icon: <BookOpen size={16} />,
    color: 'text-indigo-500',
    bgColor: 'bg-indigo-100',
    getMessage: (a) => `掌握了概念：${a.details.conceptName}`,
  },
  problem_solved: {
    icon: <Target size={16} />,
    color: 'text-teal-500',
    bgColor: 'bg-teal-100',
    getMessage: (a) => `解决了 ${a.details.problemsCount} 道题目`,
  },
  joined_group: {
    icon: <UserPlus size={16} />,
    color: 'text-pink-500',
    bgColor: 'bg-pink-100',
    getMessage: (a) => `加入了学习组「${a.details.groupName}」`,
  },
};

const timeAgo = (timestamp: string): string => {
  const date = new Date(timestamp);
  const now = new Date();
  const seconds = Math.floor((now.getTime() - date.getTime()) / 1000);
  
  if (seconds < 60) return '刚刚';
  if (seconds < 3600) return `${Math.floor(seconds / 60)} 分钟前`;
  if (seconds < 86400) return `${Math.floor(seconds / 3600)} 小时前`;
  if (seconds < 604800) return `${Math.floor(seconds / 86400)} 天前`;
  return date.toLocaleDateString('zh-CN');
};

export const FriendActivity: React.FC<FriendActivityProps> = ({
  activities,
  requests = [],
  onAcceptRequest,
  onDeclineRequest,
  onViewProfile,
  onReact,
  onComment,
  className = '',
}) => {
  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 好友请求 */}
      {requests.length > 0 && (
        <div className="p-4 border-b border-gray-200">
          <h3 className="font-semibold text-gray-800 mb-3">
            好友请求 ({requests.length})
          </h3>
          <div className="space-y-3">
            {requests.map((request) => (
              <div key={request.id} className="flex items-center gap-3 p-3 bg-gray-50 rounded-lg">
                {request.avatar ? (
                  <img
                    src={request.avatar}
                    alt={request.name}
                    className="w-12 h-12 rounded-full object-cover"
                  />
                ) : (
                  <div className="w-12 h-12 rounded-full bg-gray-200 flex items-center justify-center text-gray-600">
                    {request.name[0]}
                  </div>
                )}
                
                <div className="flex-1 min-w-0">
                  <p className="font-medium text-gray-800">{request.name}</p>
                  <p className="text-sm text-gray-500">
                    {request.mutualFriends} 位共同好友
                  </p>
                </div>

                <div className="flex items-center gap-2">
                  <button
                    onClick={() => onAcceptRequest?.(request.id)}
                    className="px-4 py-2 bg-blue-500 hover:bg-blue-600 text-white text-sm rounded-lg transition-colors"
                  >
                    接受
                  </button>
                  <button
                    onClick={() => onDeclineRequest?.(request.id)}
                    className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-200 rounded-lg transition-colors"
                  >
                    <X size={20} />
                  </button>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 活动列表 */}
      <div className="p-4">
        <h3 className="font-semibold text-gray-800 mb-4">好友动态</h3>
        
        <div className="space-y-4">
          {activities.map((activity) => {
            const config = activityConfig[activity.type];
            
            return (
              <div key={activity.id} className="flex gap-3">
                {/* 用户头像 */}
                <div 
                  className="flex-shrink-0 cursor-pointer"
                  onClick={() => onViewProfile?.(activity.userId)}
                >
                  {activity.userAvatar ? (
                    <img
                      src={activity.userAvatar}
                      alt={activity.userName}
                      className="w-10 h-10 rounded-full object-cover"
                    />
                  ) : (
                    <div className="w-10 h-10 rounded-full bg-gray-200 flex items-center justify-center text-gray-600">
                      {activity.userName[0]}
                    </div>
                  )}
                </div>

                {/* 内容 */}
                <div className="flex-1 min-w-0">
                  <div className="flex items-start justify-between">
                    <div>
                      <span 
                        className="font-medium text-gray-800 cursor-pointer hover:text-blue-500"
                        onClick={() => onViewProfile?.(activity.userId)}
                      >
                        {activity.userName}
                      </span>
                      <span className="text-gray-600"> {config.getMessage(activity)}</span>
                    </div>
                    <span className="text-xs text-gray-400 flex-shrink-0 ml-2">
                      {timeAgo(activity.timestamp)}
                    </span>
                  </div>

                  {/* 活动详情卡片 */}
                  {activity.type === 'achievement_earned' && activity.details.achievementIcon && (
                    <div className="mt-2 p-3 bg-gradient-to-r from-yellow-50 to-orange-50 rounded-lg flex items-center gap-3">
                      <span className="text-3xl">{activity.details.achievementIcon}</span>
                      <div>
                        <p className="font-medium text-gray-800">{activity.details.achievementName}</p>
                        <p className="text-sm text-gray-500">获得了新成就！</p>
                      </div>
                    </div>
                  )}

                  {activity.type === 'streak_milestone' && (
                    <div className="mt-2 p-3 bg-gradient-to-r from-orange-50 to-red-50 rounded-lg">
                      <div className="flex items-center gap-2">
                        <span className="text-2xl">🔥</span>
                        <span className="font-bold text-orange-600">
                          {activity.details.streakDays} 天连续学习！
                        </span>
                      </div>
                    </div>
                  )}

                  {/* 互动按钮 */}
                  <div className="flex items-center gap-4 mt-2">
                    <button
                      onClick={() => onReact?.(activity.id, 'like')}
                      className="flex items-center gap-1 text-sm text-gray-500 hover:text-red-500 transition-colors"
                    >
                      <span>👍</span>
                      <span>点赞</span>
                    </button>
                    <button
                      onClick={() => onComment?.(activity.id, '')}
                      className="flex items-center gap-1 text-sm text-gray-500 hover:text-blue-500 transition-colors"
                    >
                      <MessageCircle size={14} />
                      <span>评论</span>
                    </button>
                  </div>
                </div>
              </div>
            );
          })}
        </div>

        {activities.length === 0 && (
          <div className="text-center py-8 text-gray-500">
            <Clock size={48} className="mx-auto mb-4 opacity-30" />
            <p>暂无好友动态</p>
            <p className="text-sm mt-1">添加好友来查看他们的学习进展</p>
          </div>
        )}
      </div>
    </div>
  );
};

// 活跃用户列表
interface ActiveUser {
  id: string;
  name: string;
  avatar?: string;
  isOnline: boolean;
  currentActivity?: string;
  lastActive?: string;
}

interface ActiveUsersProps {
  users: ActiveUser[];
  onStartChat?: (userId: string) => void;
  onViewProfile?: (userId: string) => void;
  className?: string;
}

export const ActiveUsers: React.FC<ActiveUsersProps> = ({
  users,
  onStartChat,
  onViewProfile,
  className = '',
}) => {
  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      <div className="p-4 border-b border-gray-200">
        <h3 className="font-semibold text-gray-800">
          在线好友 ({users.filter(u => u.isOnline).length})
        </h3>
      </div>
      
      <div className="p-2">
        {users.map((user) => (
          <div
            key={user.id}
            className="flex items-center gap-3 p-2 hover:bg-gray-50 rounded-lg group cursor-pointer"
            onClick={() => onViewProfile?.(user.id)}
          >
            <div className="relative">
              {user.avatar ? (
                <img
                  src={user.avatar}
                  alt={user.name}
                  className="w-10 h-10 rounded-full object-cover"
                />
              ) : (
                <div className="w-10 h-10 rounded-full bg-gray-200 flex items-center justify-center text-gray-600">
                  {user.name[0]}
                </div>
              )}
              {user.isOnline ? (
                <span className="absolute bottom-0 right-0 w-3 h-3 bg-green-500 border-2 border-white rounded-full" />
              ) : (
                <span className="absolute bottom-0 right-0 w-3 h-3 bg-gray-400 border-2 border-white rounded-full" />
              )}
            </div>
            
            <div className="flex-1 min-w-0">
              <p className="font-medium text-gray-800">{user.name}</p>
              <p className="text-xs text-gray-500 truncate">
                {user.isOnline 
                  ? (user.currentActivity || '在线')
                  : (user.lastActive || '离线')
                }
              </p>
            </div>

            <button
              onClick={(e) => {
                e.stopPropagation();
                onStartChat?.(user.id);
              }}
              className="p-2 text-gray-400 hover:text-blue-500 hover:bg-blue-50 rounded-lg opacity-0 group-hover:opacity-100 transition-all"
            >
              <MessageCircle size={18} />
            </button>
          </div>
        ))}
      </div>
    </div>
  );
};

export default FriendActivity;
