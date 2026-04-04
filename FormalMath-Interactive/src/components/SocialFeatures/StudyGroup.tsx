import React, { useState, useEffect } from 'react';
import { 
  Users, 
  UserPlus, 
  Settings, 
  MessageSquare, 
  Trophy,
  Calendar,
  Clock,
  MoreVertical,
  Crown,
  LogOut,
  CheckCircle
} from 'lucide-react';

export interface GroupMember {
  id: string;
  name: string;
  avatar?: string;
  role: 'admin' | 'moderator' | 'member';
  joinedAt: string;
  studyTime: number; // 分钟
  problemsSolved: number;
  streak: number;
  isOnline?: boolean;
  lastActive?: string;
}

interface StudyGroup {
  id: string;
  name: string;
  description: string;
  avatar?: string;
  createdAt: string;
  memberCount: number;
  maxMembers: number;
  isPrivate: boolean;
  tags: string[];
  weeklyGoal: {
    studyMinutes: number;
    currentMinutes: number;
  };
}

export interface StudyGroupProps {
  group: StudyGroup;
  members: GroupMember[];
  currentUserId: string;
  onInvite?: () => void;
  onLeave?: () => void;
  onMessage?: (memberId: string) => void;
  onViewProgress?: (memberId: string) => void;
  className?: string;
}

export const StudyGroup: React.FC<StudyGroupProps> = ({
  group,
  members,
  currentUserId,
  onInvite,
  onLeave,
  onMessage,
  onViewProgress,
  className = '',
}) => {
  const [activeTab, setActiveTab] = useState<'members' | 'progress' | 'schedule'>('members');
  const [showMemberMenu, setShowMemberMenu] = useState<string | null>(null);
  const [showInviteModal, setShowInviteModal] = useState(false);

  const currentUser = members.find(m => m.id === currentUserId);
  const isAdmin = currentUser?.role === 'admin';
  const isModerator = currentUser?.role === 'moderator';

  // 排序成员：在线优先，然后是角色，然后是学习时间
  const sortedMembers = [...members].sort((a, b) => {
    if (a.isOnline !== b.isOnline) return (b.isOnline ? 1 : 0) - (a.isOnline ? 1 : 0);
    const roleOrder = { admin: 0, moderator: 1, member: 2 };
    if (roleOrder[a.role] !== roleOrder[b.role]) return roleOrder[a.role] - roleOrder[b.role];
    return b.studyTime - a.studyTime;
  });

  // 计算群组统计
  const groupStats = {
    totalStudyTime: members.reduce((sum, m) => sum + m.studyTime, 0),
    totalProblems: members.reduce((sum, m) => sum + m.problemsSolved, 0),
    avgStreak: Math.round(members.reduce((sum, m) => sum + m.streak, 0) / members.length),
    onlineCount: members.filter(m => m.isOnline).length,
  };

  const getRoleIcon = (role: GroupMember['role']) => {
    switch (role) {
      case 'admin':
        return <Crown size={14} className="text-yellow-500" />;
      case 'moderator':
        return <CheckCircle size={14} className="text-blue-500" />;
      default:
        return null;
    }
  };

  const getRoleLabel = (role: GroupMember['role']) => {
    switch (role) {
      case 'admin':
        return '群主';
      case 'moderator':
        return '管理员';
      default:
        return '成员';
    }
  };

  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 群组头部 */}
      <div className="p-6 border-b border-gray-200">
        <div className="flex items-start justify-between">
          <div className="flex gap-4">
            {group.avatar ? (
              <img
                src={group.avatar}
                alt={group.name}
                className="w-20 h-20 rounded-xl object-cover"
              />
            ) : (
              <div className="w-20 h-20 rounded-xl bg-gradient-to-br from-blue-500 to-purple-600 
                            flex items-center justify-center text-white text-3xl font-bold">
                {group.name[0]}
              </div>
            )}
            
            <div className="flex-1">
              <div className="flex items-center gap-2">
                <h2 className="text-xl font-bold text-gray-800">{group.name}</h2>
                {group.isPrivate && (
                  <span className="px-2 py-0.5 bg-gray-100 text-gray-600 text-xs rounded-full">
                    私密
                  </span>
                )}
              </div>
              <p className="text-gray-600 text-sm mt-1">{group.description}</p>
              
              <div className="flex flex-wrap items-center gap-2 mt-2">
                {group.tags.map(tag => (
                  <span key={tag} className="px-2 py-1 bg-blue-50 text-blue-600 text-xs rounded">
                    #{tag}
                  </span>
                ))}
              </div>

              <div className="flex items-center gap-4 mt-3 text-sm text-gray-500">
                <span className="flex items-center gap-1">
                  <Users size={16} />
                  {group.memberCount}/{group.maxMembers} 成员
                </span>
                <span className="flex items-center gap-1">
                  <Calendar size={16} />
                  创建于 {new Date(group.createdAt).toLocaleDateString('zh-CN')}
                </span>
              </div>
            </div>
          </div>

          <div className="flex items-center gap-2">
            {(isAdmin || isModerator) && (
              <button
                onClick={() => setShowInviteModal(true)}
                className="px-4 py-2 bg-blue-500 hover:bg-blue-600 text-white rounded-lg 
                         flex items-center gap-2 transition-colors"
              >
                <UserPlus size={18} />
                邀请
              </button>
            )}
            
            {isAdmin && (
              <button className="p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg">
                <Settings size={20} />
              </button>
            )}
            
            <button
              onClick={onLeave}
              className="p-2 text-red-500 hover:text-red-600 hover:bg-red-50 rounded-lg"
              title="退出群组"
            >
              <LogOut size={20} />
            </button>
          </div>
        </div>

        {/* 本周目标进度 */}
        <div className="mt-6 p-4 bg-gradient-to-r from-blue-50 to-purple-50 rounded-lg">
          <div className="flex items-center justify-between mb-2">
            <span className="font-medium text-gray-800">本周学习目标</span>
            <span className="text-sm text-gray-600">
              {Math.round((group.weeklyGoal.currentMinutes / group.weeklyGoal.studyMinutes) * 100)}%
            </span>
          </div>
          <div className="w-full h-2 bg-white rounded-full overflow-hidden">
            <div
              className="h-full bg-gradient-to-r from-blue-500 to-purple-500 transition-all"
              style={{
                width: `${Math.min((group.weeklyGoal.currentMinutes / group.weeklyGoal.studyMinutes) * 100, 100)}%`
              }}
            />
          </div>
          <div className="flex justify-between mt-2 text-sm text-gray-600">
            <span>已学习 {Math.floor(group.weeklyGoal.currentMinutes / 60)} 小时 {group.weeklyGoal.currentMinutes % 60} 分钟</span>
            <span>目标 {Math.floor(group.weeklyGoal.studyMinutes / 60)} 小时</span>
          </div>
        </div>
      </div>

      {/* 标签页 */}
      <div className="border-b border-gray-200">
        <div className="flex">
          {[
            { id: 'members', label: '成员', icon: Users },
            { id: 'progress', label: '进度', icon: Trophy },
            { id: 'schedule', label: '日程', icon: Calendar },
          ].map(({ id, label, icon: Icon }) => (
            <button
              key={id}
              onClick={() => setActiveTab(id as typeof activeTab)}
              className={`flex-1 flex items-center justify-center gap-2 py-3 text-sm font-medium 
                         transition-colors border-b-2
                         ${activeTab === id 
                           ? 'text-blue-500 border-blue-500' 
                           : 'text-gray-500 border-transparent hover:text-gray-700'}`}
            >
              <Icon size={18} />
              {label}
            </button>
          ))}
        </div>
      </div>

      {/* 内容区 */}
      <div className="p-4">
        {activeTab === 'members' && (
          <div className="space-y-3">
            {/* 在线人数 */}
            <div className="flex items-center gap-2 text-sm text-gray-500 mb-4">
              <span className="relative flex h-2 w-2">
                <span className="animate-ping absolute inline-flex h-full w-full rounded-full bg-green-400 opacity-75" />
                <span className="relative inline-flex rounded-full h-2 w-2 bg-green-500" />
              </span>
              {groupStats.onlineCount} 人在线
            </div>

            {/* 成员列表 */}
            {sortedMembers.map((member) => (
              <div
                key={member.id}
                className="flex items-center gap-3 p-3 hover:bg-gray-50 rounded-lg group"
              >
                <div className="relative">
                  {member.avatar ? (
                    <img
                      src={member.avatar}
                      alt={member.name}
                      className="w-10 h-10 rounded-full object-cover"
                    />
                  ) : (
                    <div className="w-10 h-10 rounded-full bg-gray-200 flex items-center justify-center text-gray-600">
                      {member.name[0]}
                    </div>
                  )}
                  {member.isOnline && (
                    <span className="absolute bottom-0 right-0 w-3 h-3 bg-green-500 border-2 border-white rounded-full" />
                  )}
                </div>

                <div className="flex-1 min-w-0">
                  <div className="flex items-center gap-2">
                    <span className="font-medium text-gray-800 truncate">{member.name}</span>
                    {getRoleIcon(member.role)}
                    <span className="text-xs text-gray-500">{getRoleLabel(member.role)}</span>
                  </div>
                  <div className="flex items-center gap-4 text-xs text-gray-500 mt-0.5">
                    <span>连续 {member.streak} 天</span>
                    <span>{member.problemsSolved} 题</span>
                    {member.lastActive && !member.isOnline && (
                      <span>最近 {member.lastActive}</span>
                    )}
                  </div>
                </div>

                {/* 操作菜单 */}
                <div className="relative">
                  {member.id !== currentUserId && (
                    <>
                      <button
                        onClick={() => onMessage?.(member.id)}
                        className="p-2 text-gray-400 hover:text-blue-500 hover:bg-blue-50 rounded-lg mr-1"
                      >
                        <MessageSquare size={18} />
                      </button>
                      
                      <button
                        onClick={() => setShowMemberMenu(showMemberMenu === member.id ? null : member.id)}
                        className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded-lg"
                      >
                        <MoreVertical size={18} />
                      </button>

                      {showMemberMenu === member.id && (
                        <div className="absolute right-0 top-full mt-1 w-40 bg-white rounded-lg shadow-lg border border-gray-200 py-1 z-10">
                          <button
                            onClick={() => {
                              onViewProgress?.(member.id);
                              setShowMemberMenu(null);
                            }}
                            className="w-full px-4 py-2 text-left text-sm hover:bg-gray-50"
                          >
                            查看进度
                          </button>
                          {(isAdmin || isModerator) && member.role === 'member' && (
                            <>
                              <button className="w-full px-4 py-2 text-left text-sm hover:bg-gray-50">
                                设为管理员
                              </button>
                              <button className="w-full px-4 py-2 text-left text-sm text-red-500 hover:bg-red-50">
                                移出群组
                              </button>
                            </>
                          )}
                        </div>
                      )}
                    </>
                  )}
                </div>
              </div>
            ))}
          </div>
        )}

        {activeTab === 'progress' && (
          <div className="space-y-4">
            {/* 排行榜 */}
            <div className="grid grid-cols-3 gap-4">
              <div className="text-center p-4 bg-yellow-50 rounded-lg">
                <Trophy className="mx-auto mb-2 text-yellow-500" size={24} />
                <p className="text-2xl font-bold text-yellow-600">
                  {Math.max(...members.map(m => m.studyTime))}
                </p>
                <p className="text-xs text-gray-600">最高学习时长(分)</p>
              </div>
              <div className="text-center p-4 bg-blue-50 rounded-lg">
                <CheckCircle className="mx-auto mb-2 text-blue-500" size={24} />
                <p className="text-2xl font-bold text-blue-600">{groupStats.totalProblems}</p>
                <p className="text-xs text-gray-600">总解题数</p>
              </div>
              <div className="text-center p-4 bg-green-50 rounded-lg">
                <Clock className="mx-auto mb-2 text-green-500" size={24} />
                <p className="text-2xl font-bold text-green-600">{groupStats.avgStreak}</p>
                <p className="text-xs text-gray-600">平均连续天数</p>
              </div>
            </div>

            {/* 个人排行 */}
            <div>
              <h4 className="font-medium text-gray-800 mb-3">学习时长排行</h4>
              <div className="space-y-2">
                {[...members]
                  .sort((a, b) => b.studyTime - a.studyTime)
                  .slice(0, 5)
                  .map((member, index) => (
                    <div key={member.id} className="flex items-center gap-3 p-2 hover:bg-gray-50 rounded">
                      <span className={`
                        w-6 h-6 rounded-full flex items-center justify-center text-xs font-bold
                        ${index === 0 ? 'bg-yellow-100 text-yellow-600' :
                          index === 1 ? 'bg-gray-100 text-gray-600' :
                          index === 2 ? 'bg-orange-100 text-orange-600' :
                          'bg-gray-50 text-gray-400'}
                      `}>
                        {index + 1}
                      </span>
                      <span className="flex-1 text-sm">{member.name}</span>
                      <span className="text-sm text-gray-500">
                        {Math.floor(member.studyTime / 60)}h {member.studyTime % 60}m
                      </span>
                    </div>
                  ))}
              </div>
            </div>
          </div>
        )}

        {activeTab === 'schedule' && (
          <div className="text-center py-8 text-gray-500">
            <Calendar size={48} className="mx-auto mb-4 opacity-30" />
            <p>群组学习日程功能即将上线</p>
            <p className="text-sm mt-2">敬请期待...</p>
          </div>
        )}
      </div>
    </div>
  );
};

export default StudyGroup;
