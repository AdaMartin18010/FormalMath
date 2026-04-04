// ==================== 在线用户列表和光标位置组件 ====================

import React, { useState, useCallback } from 'react';
import { UserPresence as UserPresenceType, UserStatus } from '@types/collaboration';
import './UserPresence.css';

// 组件Props
interface UserPresenceProps {
  users: UserPresenceType[];
  currentUserId: string;
  showAvatars?: boolean;
  showStatus?: boolean;
  showCursor?: boolean;
  maxDisplay?: number;
  onUserClick?: (user: UserPresenceType) => void;
  className?: string;
}

// 状态指示器颜色
const STATUS_COLORS: Record<UserStatus, string> = {
  online: '#22c55e',
  away: '#f59e0b',
  busy: '#ef4444',
  offline: '#9ca3af',
};

// 状态文本
const STATUS_TEXT: Record<UserStatus, string> = {
  online: '在线',
  away: '离开',
  busy: '忙碌',
  offline: '离线',
};

export const UserPresence: React.FC<UserPresenceProps> = ({
  users,
  currentUserId,
  showAvatars = true,
  showStatus = true,
  showCursor = true,
  maxDisplay = 5,
  onUserClick,
  className = '',
}) => {
  const [expanded, setExpanded] = useState(false);
  const [tooltipUser, setTooltipUser] = useState<UserPresenceType | null>(null);
  const [tooltipPosition, setTooltipPosition] = useState({ x: 0, y: 0 });

  // 过滤当前用户并按状态排序
  const sortedUsers = [...users]
    .filter((user) => user.id !== currentUserId)
    .sort((a, b) => {
      const statusOrder = { online: 0, away: 1, busy: 2, offline: 3 };
      return statusOrder[a.status] - statusOrder[b.status];
    });

  // 显示的用户和额外的用户
  const displayedUsers = expanded ? sortedUsers : sortedUsers.slice(0, maxDisplay);
  const extraCount = sortedUsers.length - maxDisplay;

  // 处理用户点击
  const handleUserClick = useCallback((user: UserPresenceType) => {
    onUserClick?.(user);
  }, [onUserClick]);

  // 处理鼠标进入显示tooltip
  const handleMouseEnter = useCallback((user: UserPresenceType, e: React.MouseEvent) => {
    const rect = (e.target as HTMLElement).getBoundingClientRect();
    setTooltipPosition({
      x: rect.left + rect.width / 2,
      y: rect.top - 8,
    });
    setTooltipUser(user);
  }, []);

  // 处理鼠标离开隐藏tooltip
  const handleMouseLeave = useCallback(() => {
    setTooltipUser(null);
  }, []);

  // 获取用户缩写
  const getUserInitials = (name: string): string => {
    return name
      .split(' ')
      .map((n) => n[0])
      .join('')
      .toUpperCase()
      .slice(0, 2);
  };

  // 格式化最后在线时间
  const formatLastSeen = (timestamp: number): string => {
    const diff = Date.now() - timestamp;
    const minutes = Math.floor(diff / 60000);
    const hours = Math.floor(diff / 3600000);
    const days = Math.floor(diff / 86400000);

    if (minutes < 1) return '刚刚';
    if (minutes < 60) return `${minutes}分钟前`;
    if (hours < 24) return `${hours}小时前`;
    return `${days}天前`;
  };

  return (
    <div className={`user-presence ${className}`}>
      {/* 用户头像列表 */}
      <div className="user-avatar-list">
        {/* 当前用户（单独显示） */}
        <div
          className="user-avatar current-user"
          style={{ borderColor: users.find(u => u.id === currentUserId)?.color || '#3b82f6' }}
          onMouseEnter={(e) => {
            const currentUser = users.find(u => u.id === currentUserId);
            if (currentUser) handleMouseEnter(currentUser, e);
          }}
          onMouseLeave={handleMouseLeave}
        >
          {showAvatars ? (
            <>
              <div className="avatar-image">
                {users.find(u => u.id === currentUserId)?.avatar ? (
                  <img
                    src={users.find(u => u.id === currentUserId)?.avatar}
                    alt="我"
                    className="avatar-img"
                  />
                ) : (
                  <span className="avatar-initials">
                    {getUserInitials(users.find(u => u.id === currentUserId)?.name || '我')}
                  </span>
                )}
              </div>
              {showStatus && (
                <span
                  className="status-indicator"
                  style={{ backgroundColor: STATUS_COLORS.online }}
                />
              )}
            </>
          ) : (
            <span className="user-name-short">我</span>
          )}
        </div>

        {/* 分隔线 */}
        {sortedUsers.length > 0 && <div className="avatar-divider" />}

        {/* 其他用户 */}
        {displayedUsers.map((user) => (
          <div
            key={user.id}
            className="user-avatar"
            style={{ borderColor: user.color }}
            onClick={() => handleUserClick(user)}
            onMouseEnter={(e) => handleMouseEnter(user, e)}
            onMouseLeave={handleMouseLeave}
          >
            {showAvatars ? (
              <>
                <div className="avatar-image">
                  {user.avatar ? (
                    <img src={user.avatar} alt={user.name} className="avatar-img" />
                  ) : (
                    <span className="avatar-initials" style={{ backgroundColor: user.color }}>
                      {getUserInitials(user.name)}
                    </span>
                  )}
                </div>
                {showStatus && (
                  <span
                    className="status-indicator"
                    style={{ backgroundColor: STATUS_COLORS[user.status] }}
                  />
                )}
              </>
            ) : (
              <span className="user-name-short">{getUserInitials(user.name)}</span>
            )}

            {/* 光标位置指示器 */}
            {showCursor && user.cursor && (
              <div
                className="cursor-indicator"
                style={{
                  backgroundColor: user.color,
                  left: `${user.cursor.x}px`,
                  top: `${user.cursor.y}px`,
                }}
              >
                <span className="cursor-label" style={{ backgroundColor: user.color }}>
                  {user.name}
                </span>
              </div>
            )}
          </div>
        ))}

        {/* 更多用户指示器 */}
        {!expanded && extraCount > 0 && (
          <button
            className="more-users-btn"
            onClick={() => setExpanded(true)}
            title={`还有${extraCount}位用户`}
          >
            +{extraCount}
          </button>
        )}

        {/* 收起按钮 */}
        {expanded && sortedUsers.length > maxDisplay && (
          <button
            className="collapse-btn"
            onClick={() => setExpanded(false)}
            title="收起"
          >
            ←
          </button>
        )}
      </div>

      {/* 在线用户数统计 */}
      <div className="user-count">
        <span className="online-count">
          {sortedUsers.filter((u) => u.status === 'online').length + 1} 人在线
        </span>
      </div>

      {/* Tooltip */}
      {tooltipUser && (
        <div
          className="user-tooltip"
          style={{
            left: tooltipPosition.x,
            top: tooltipPosition.y,
            transform: 'translate(-50%, -100%)',
          }}
        >
          <div className="tooltip-header">
            {tooltipUser.avatar ? (
              <img src={tooltipUser.avatar} alt={tooltipUser.name} className="tooltip-avatar" />
            ) : (
              <div
                className="tooltip-avatar-placeholder"
                style={{ backgroundColor: tooltipUser.color }}
              >
                {getUserInitials(tooltipUser.name)}
              </div>
            )}
            <div className="tooltip-info">
              <span className="tooltip-name">{tooltipUser.name}</span>
              <span
                className="tooltip-status"
                style={{ color: STATUS_COLORS[tooltipUser.status] }}
              >
                {STATUS_TEXT[tooltipUser.status]}
              </span>
            </div>
          </div>
          {tooltipUser.status !== 'online' && (
            <div className="tooltip-last-seen">
              最后在线: {formatLastSeen(tooltipUser.lastSeen)}
            </div>
          )}
          {tooltipUser.currentRoom && (
            <div className="tooltip-room">当前房间: {tooltipUser.currentRoom}</div>
          )}
          {tooltipUser.cursor && (
            <div className="tooltip-cursor">
              位置: 行 {tooltipUser.cursor.line || '?'}, 列 {tooltipUser.cursor.column || '?'}
            </div>
          )}
        </div>
      )}
    </div>
  );
};

// 简单版本的在线用户列表（用于紧凑显示）
export const CompactUserPresence: React.FC<Omit<UserPresenceProps, 'showCursor' | 'showStatus'>> = ({
  users,
  currentUserId,
  showAvatars = true,
  maxDisplay = 3,
  onUserClick,
  className = '',
}) => {
  const sortedUsers = [...users]
    .filter((user) => user.id !== currentUserId)
    .sort((a, b) => {
      const statusOrder = { online: 0, away: 1, busy: 2, offline: 3 };
      return statusOrder[a.status] - statusOrder[b.status];
    });

  const displayedUsers = sortedUsers.slice(0, maxDisplay);
  const extraCount = sortedUsers.length - maxDisplay;

  const getUserInitials = (name: string): string => {
    return name
      .split(' ')
      .map((n) => n[0])
      .join('')
      .toUpperCase()
      .slice(0, 2);
  };

  return (
    <div className={`compact-user-presence ${className}`}>
      {displayedUsers.map((user, index) => (
        <div
          key={user.id}
          className="compact-avatar"
          style={{
            backgroundColor: user.color,
            zIndex: displayedUsers.length - index,
            marginLeft: index > 0 ? '-8px' : '0',
          }}
          onClick={() => onUserClick?.(user)}
          title={user.name}
        >
          {showAvatars ? (
            user.avatar ? (
              <img src={user.avatar} alt={user.name} />
            ) : (
              <span>{getUserInitials(user.name)}</span>
            )
          ) : (
            <span>{getUserInitials(user.name)}</span>
          )}
        </div>
      ))}
      {extraCount > 0 && (
        <div className="compact-avatar more" style={{ marginLeft: '-8px' }}>
          <span>+{extraCount}</span>
        </div>
      )}
    </div>
  );
};

export default UserPresence;
