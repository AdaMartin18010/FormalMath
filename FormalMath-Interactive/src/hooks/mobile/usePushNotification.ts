import { useState, useEffect, useCallback } from 'react';

interface NotificationPermission {
  permission: NotificationPermission;
  isSupported: boolean;
}

interface NotificationOptions {
  title: string;
  body?: string;
  icon?: string;
  badge?: string;
  tag?: string;
  requireInteraction?: boolean;
  actions?: NotificationAction[];
  data?: any;
  vibrate?: number[];
  silent?: boolean;
}

/**
 * 推送通知 Hook
 */
export const usePushNotification = () => {
  const [state, setState] = useState<NotificationPermission>({
    permission: 'default',
    isSupported: 'Notification' in window,
  });

  useEffect(() => {
    if (!('Notification' in window)) return;

    setState(prev => ({
      ...prev,
      permission: Notification.permission,
    }));
  }, []);

  /**
   * 请求通知权限
   */
  const requestPermission = useCallback(async (): Promise<boolean> => {
    if (!('Notification' in window)) {
      console.warn('此浏览器不支持通知');
      return false;
    }

    try {
      const permission = await Notification.requestPermission();
      setState(prev => ({ ...prev, permission }));
      return permission === 'granted';
    } catch (error) {
      console.error('请求通知权限失败:', error);
      return false;
    }
  }, []);

  /**
   * 显示通知
   */
  const showNotification = useCallback((options: NotificationOptions): Notification | null => {
    if (!('Notification' in window) || Notification.permission !== 'granted') {
      console.warn('没有通知权限');
      return null;
    }

    const defaultIcon = '/FormalMath/icons/icon-192x192.png';
    const defaultBadge = '/FormalMath/icons/icon-72x72.png';

    const notification = new Notification(options.title, {
      body: options.body,
      icon: options.icon || defaultIcon,
      badge: options.badge || defaultBadge,
      tag: options.tag,
      requireInteraction: options.requireInteraction,
      actions: options.actions,
      data: options.data,
      vibrate: options.vibrate || [200, 100, 200],
      silent: options.silent,
    });

    // 自动关闭（5秒后）
    if (!options.requireInteraction) {
      setTimeout(() => notification.close(), 5000);
    }

    return notification;
  }, []);

  /**
   * 发送学习提醒
   */
  const sendStudyReminder = useCallback((content: string) => {
    return showNotification({
      title: '学习提醒 📚',
      body: content,
      tag: 'study-reminder',
      icon: '/FormalMath/icons/icon-192x192.png',
      requireInteraction: false,
      vibrate: [100, 50, 100],
    });
  }, [showNotification]);

  /**
   * 发送知识更新通知
   */
  const sendKnowledgeUpdate = useCallback((title: string, description: string) => {
    return showNotification({
      title: `新知识: ${title}`,
      body: description,
      tag: 'knowledge-update',
      icon: '/FormalMath/icons/icon-192x192.png',
      requireInteraction: false,
      actions: [
        { action: 'view', title: '查看' },
        { action: 'dismiss', title: '忽略' },
      ],
    });
  }, [showNotification]);

  /**
   * 发送成就通知
   */
  const sendAchievementNotification = useCallback((achievement: string) => {
    return showNotification({
      title: '🎉 恭喜获得成就！',
      body: achievement,
      tag: 'achievement',
      icon: '/FormalMath/icons/icon-192x192.png',
      requireInteraction: true,
      vibrate: [300, 100, 300, 100, 300],
    });
  }, [showNotification]);

  return {
    ...state,
    requestPermission,
    showNotification,
    sendStudyReminder,
    sendKnowledgeUpdate,
    sendAchievementNotification,
  };
};

/**
 * 定期学习提醒 Hook
 */
export const useStudyReminder = (options: {
  enabled?: boolean;
  interval?: number; // 分钟
  reminderContent?: string[];
}) => {
  const { enabled = false, interval = 60, reminderContent = defaultReminders } = options;
  const [isActive, setIsActive] = useState(enabled);
  const { showNotification, permission, requestPermission } = usePushNotification();

  useEffect(() => {
    if (!isActive || permission !== 'granted') return;

    const intervalId = setInterval(() => {
      const randomContent = reminderContent[Math.floor(Math.random() * reminderContent.length)];
      showNotification({
        title: '继续学习吧！📖',
        body: randomContent,
        tag: 'study-reminder-scheduled',
        icon: '/FormalMath/icons/icon-192x192.png',
      });
    }, interval * 60 * 1000);

    return () => clearInterval(intervalId);
  }, [isActive, interval, permission, reminderContent, showNotification]);

  const activate = useCallback(async () => {
    if (permission !== 'granted') {
      const granted = await requestPermission();
      if (!granted) return false;
    }
    setIsActive(true);
    return true;
  }, [permission, requestPermission]);

  const deactivate = useCallback(() => {
    setIsActive(false);
  }, []);

  return { isActive, activate, deactivate };
};

const defaultReminders = [
 '今天复习一下微积分的基本概念吧！',
  '尝试证明一个定理，锻炼逻辑思维。',
  '探索一下几何学的美妙世界。',
  '了解一下数学史上有趣的故事。',
  '做几道练习题巩固所学知识。',
  '看看今天有哪些新知识更新。',
];

export default usePushNotification;
