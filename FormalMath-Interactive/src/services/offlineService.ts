// @ts-nocheck
/**
 * 离线学习服务
 * 提供内容缓存、离线数据同步、学习进度保存等功能
 */

import { openDB, DBSchema, IDBPDatabase } from 'idb';

// 学习内容的类型定义
export interface OfflineContent {
  id: string;
  type: 'concept' | 'theorem' | 'proof' | 'exercise' | 'video' | 'article';
  title: string;
  content: string;
  metadata: {
    author?: string;
    difficulty?: 'beginner' | 'intermediate' | 'advanced';
    tags?: string[];
    estimatedTime?: number; // 分钟
  };
  cachedAt: number;
  expiresAt?: number;
  syncStatus: 'synced' | 'pending' | 'error';
}

// 学习进度类型
export interface LearningProgress {
  contentId: string;
  userId: string;
  progress: number; // 0-100
  lastPosition?: number; // 上次阅读位置
  completed: boolean;
  startedAt: number;
  lastAccessedAt: number;
  notes?: string[];
  highlights?: Array<{
    start: number;
    end: number;
    text: string;
    color: string;
  }>;
  syncStatus: 'synced' | 'pending' | 'conflict';
}

// 离线队列项
export interface OfflineQueueItem {
  id: string;
  type: 'progress_update' | 'note_add' | 'bookmark_add' | 'completion_mark';
  payload: unknown;
  timestamp: number;
  retryCount: number;
  status: 'pending' | 'processing' | 'failed';
}

// IndexedDB Schema
interface FormalMathDB extends DBSchema {
  content: {
    key: string;
    value: OfflineContent;
    indexes: { 'by-type': string; 'by-sync-status': string };
  };
  progress: {
    key: string;
    value: LearningProgress;
    indexes: { 'by-user': string; 'by-content': string };
  };
  queue: {
    key: string;
    value: OfflineQueueItem;
    indexes: { 'by-status': string; 'by-timestamp': number };
  };
  cacheMetadata: {
    key: string;
    value: {
      key: string;
      cachedAt: number;
      size: number;
      accessCount: number;
      lastAccessed: number;
    };
  };
}

const DB_NAME = 'FormalMathOfflineDB';
const DB_VERSION = 1;

class OfflineService {
  private db: IDBPDatabase<FormalMathDB> | null = null;
  private syncInterval: NodeJS.Timeout | null = null;
  private readonly MAX_CACHE_SIZE = 100 * 1024 * 1024; // 100MB
  private readonly DEFAULT_EXPIRY = 7 * 24 * 60 * 60 * 1000; // 7天

  async init(): Promise<void> {
    this.db = await openDB<FormalMathDB>(DB_NAME, DB_VERSION, {
      upgrade(db) {
        // 内容存储
        const contentStore = db.createObjectStore('content', { keyPath: 'id' });
        contentStore.createIndex('by-type', 'type');
        contentStore.createIndex('by-sync-status', 'syncStatus');

        // 进度存储
        const progressStore = db.createObjectStore('progress', { keyPath: 'contentId' });
        progressStore.createIndex('by-user', 'userId');
        progressStore.createIndex('by-content', 'contentId');

        // 离线队列
        const queueStore = db.createObjectStore('queue', { keyPath: 'id' });
        queueStore.createIndex('by-status', 'status');
        queueStore.createIndex('by-timestamp', 'timestamp');

        // 缓存元数据
        db.createObjectStore('cacheMetadata', { keyPath: 'key' });
      },
    });

    this.startAutoSync();
  }

  // ========== 内容缓存管理 ==========

  async cacheContent(content: OfflineContent): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');

    const contentToCache: OfflineContent = {
      ...content,
      cachedAt: Date.now(),
      expiresAt: Date.now() + this.DEFAULT_EXPIRY,
      syncStatus: 'synced',
    };

    await this.db.put('content', contentToCache);
    await this.updateCacheMetadata(content.id, JSON.stringify(content).length);

    // 检查缓存大小并清理
    await this.enforceCacheLimit();
  }

  async getCachedContent(id: string): Promise<OfflineContent | undefined> {
    if (!this.db) throw new Error('Database not initialized');

    const content = await this.db.get('content', id);
    
    if (content) {
      // 检查是否过期
      if (content.expiresAt && content.expiresAt < Date.now()) {
        await this.removeCachedContent(id);
        return undefined;
      }
      
      // 更新访问统计
      await this.updateAccessStats(id);
    }

    return content;
  }

  async getCachedContentsByType(type: OfflineContent['type']): Promise<OfflineContent[]> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.getAllFromIndex('content', 'by-type', type);
  }

  async removeCachedContent(id: string): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');
    await this.db.delete('content', id);
    await this.db.delete('cacheMetadata', id);
  }

  async clearExpiredCache(): Promise<number> {
    if (!this.db) throw new Error('Database not initialized');

    const allContent = await this.db.getAll('content');
    const now = Date.now();
    let clearedCount = 0;

    for (const content of allContent) {
      if (content.expiresAt && content.expiresAt < now) {
        await this.removeCachedContent(content.id);
        clearedCount++;
      }
    }

    return clearedCount;
  }

  // ========== 学习进度管理 ==========

  async saveProgress(progress: LearningProgress): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');

    const existing = await this.db.get('progress', progress.contentId);
    
    const progressToSave: LearningProgress = {
      ...progress,
      lastAccessedAt: Date.now(),
      syncStatus: navigator.onLine ? 'synced' : 'pending',
    };

    await this.db.put('progress', progressToSave);

    // 如果离线，添加到同步队列
    if (!navigator.onLine) {
      await this.addToQueue({
        id: `progress-${progress.contentId}-${Date.now()}`,
        type: 'progress_update',
        payload: progress,
        timestamp: Date.now(),
        retryCount: 0,
        status: 'pending',
      });
    }
  }

  async getProgress(contentId: string): Promise<LearningProgress | undefined> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.get('progress', contentId);
  }

  async getAllProgress(): Promise<LearningProgress[]> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.getAll('progress');
  }

  async getPendingSyncProgress(): Promise<LearningProgress[]> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.getAllFromIndex('progress', 'by-sync-status', 'pending');
  }

  // ========== 离线队列管理 ==========

  async addToQueue(item: OfflineQueueItem): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');
    await this.db.put('queue', item);
  }

  async getQueueItems(status: OfflineQueueItem['status']): Promise<OfflineQueueItem[]> {
    if (!this.db) throw new Error('Database not initialized');
    return this.db.getAllFromIndex('queue', 'by-status', status);
  }

  async removeFromQueue(id: string): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');
    await this.db.delete('queue', id);
  }

  async updateQueueItemStatus(
    id: string, 
    status: OfflineQueueItem['status'],
    retryCount?: number
  ): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');
    
    const item = await this.db.get('queue', id);
    if (item) {
      item.status = status;
      if (retryCount !== undefined) item.retryCount = retryCount;
      await this.db.put('queue', item);
    }
  }

  // ========== 同步管理 ==========

  async syncWithServer(): Promise<{
    success: number;
    failed: number;
    conflicts: number;
  }> {
    if (!this.db || !navigator.onLine) {
      return { success: 0, failed: 0, conflicts: 0 };
    }

    const pendingItems = await this.getQueueItems('pending');
    let success = 0;
    let failed = 0;
    let conflicts = 0;

    for (const item of pendingItems) {
      try {
        await this.processQueueItem(item);
        success++;
      } catch (error) {
        if (item.retryCount >= 3) {
          item.status = 'failed';
          conflicts++;
        } else {
          item.retryCount++;
          failed++;
        }
        await this.db.put('queue', item);
      }
    }

    // 同步进度数据
    const pendingProgress = await this.getPendingSyncProgress();
    for (const progress of pendingProgress) {
      try {
        // 发送到服务器
        await this.sendProgressToServer(progress);
        progress.syncStatus = 'synced';
        await this.db.put('progress', progress);
        success++;
      } catch (error) {
        progress.syncStatus = 'error';
        await this.db.put('progress', progress);
        failed++;
      }
    }

    return { success, failed, conflicts };
  }

  private async processQueueItem(item: OfflineQueueItem): Promise<void> {
    switch (item.type) {
      case 'progress_update':
        await this.sendProgressToServer(item.payload as LearningProgress);
        break;
      case 'note_add':
        await this.sendNoteToServer(item.payload);
        break;
      case 'bookmark_add':
        await this.sendBookmarkToServer(item.payload);
        break;
      case 'completion_mark':
        await this.sendCompletionToServer(item.payload);
        break;
    }
    
    await this.removeFromQueue(item.id);
  }

  private async sendProgressToServer(progress: LearningProgress): Promise<void> {
    const response = await fetch('/api/progress', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(progress),
    });

    if (!response.ok) {
      throw new Error(`Failed to sync progress: ${response.statusText}`);
    }
  }

  private async sendNoteToServer(payload: unknown): Promise<void> {
    const response = await fetch('/api/notes', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      throw new Error(`Failed to sync note: ${response.statusText}`);
    }
  }

  private async sendBookmarkToServer(payload: unknown): Promise<void> {
    const response = await fetch('/api/bookmarks', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      throw new Error(`Failed to sync bookmark: ${response.statusText}`);
    }
  }

  private async sendCompletionToServer(payload: unknown): Promise<void> {
    const response = await fetch('/api/completions', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      throw new Error(`Failed to sync completion: ${response.statusText}`);
    }
  }

  // ========== 后台同步 ==========

  async registerBackgroundSync(tag: string): Promise<void> {
    if ('serviceWorker' in navigator && 'sync' in ServiceWorkerRegistration.prototype) {
      const registration = await navigator.serviceWorker.ready;
      try {
        await registration.sync.register(tag);
      } catch (error) {
        console.warn('Background sync registration failed:', error);
      }
    }
  }

  // ========== 缓存管理 ==========

  private async updateCacheMetadata(key: string, size: number): Promise<void> {
    if (!this.db) return;
    
    await this.db.put('cacheMetadata', {
      key,
      cachedAt: Date.now(),
      size,
      accessCount: 1,
      lastAccessed: Date.now(),
    });
  }

  private async updateAccessStats(key: string): Promise<void> {
    if (!this.db) return;
    
    const metadata = await this.db.get('cacheMetadata', key);
    if (metadata) {
      metadata.accessCount++;
      metadata.lastAccessed = Date.now();
      await this.db.put('cacheMetadata', metadata);
    }
  }

  private async enforceCacheLimit(): Promise<void> {
    if (!this.db) return;

    const allMetadata = await this.db.getAll('cacheMetadata');
    const totalSize = allMetadata.reduce((sum, m) => sum + m.size, 0);

    if (totalSize > this.MAX_CACHE_SIZE) {
      // 按最后访问时间排序，删除最旧的
      const sorted = allMetadata.sort((a, b) => a.lastAccessed - b.lastAccessed);
      let sizeToFree = totalSize - this.MAX_CACHE_SIZE * 0.8; // 释放到80%

      for (const metadata of sorted) {
        if (sizeToFree <= 0) break;
        await this.removeCachedContent(metadata.key);
        sizeToFree -= metadata.size;
      }
    }
  }

  // ========== 自动同步 ==========

  private startAutoSync(): void {
    // 每5分钟尝试同步一次
    this.syncInterval = setInterval(() => {
      if (navigator.onLine) {
        this.syncWithServer();
      }
    }, 5 * 60 * 1000);

    // 监听网络状态变化
    window.addEventListener('online', () => {
      this.syncWithServer();
      this.registerBackgroundSync('sync-learning-data');
    });
  }

  stopAutoSync(): void {
    if (this.syncInterval) {
      clearInterval(this.syncInterval);
      this.syncInterval = null;
    }
  }

  // ========== 统计信息 ==========

  async getCacheStats(): Promise<{
    totalItems: number;
    totalSize: number;
    pendingSync: number;
    expiredItems: number;
  }> {
    if (!this.db) {
      return { totalItems: 0, totalSize: 0, pendingSync: 0, expiredItems: 0 };
    }

    const allContent = await this.db.getAll('content');
    const allMetadata = await this.db.getAll('cacheMetadata');
    const pendingItems = await this.getQueueItems('pending');
    const now = Date.now();

    return {
      totalItems: allContent.length,
      totalSize: allMetadata.reduce((sum, m) => sum + m.size, 0),
      pendingSync: pendingItems.length,
      expiredItems: allContent.filter(c => c.expiresAt && c.expiresAt < now).length,
    };
  }

  // ========== 导出/导入 ==========

  async exportLearningData(): Promise<string> {
    if (!this.db) throw new Error('Database not initialized');

    const data = {
      progress: await this.db.getAll('progress'),
      queue: await this.db.getAll('queue'),
      exportedAt: Date.now(),
    };

    return JSON.stringify(data);
  }

  async importLearningData(jsonData: string): Promise<void> {
    if (!this.db) throw new Error('Database not initialized');

    const data = JSON.parse(jsonData);
    
    if (data.progress) {
      for (const progress of data.progress) {
        await this.db.put('progress', progress);
      }
    }

    if (data.queue) {
      for (const item of data.queue) {
        await this.db.put('queue', item);
      }
    }
  }
}

// 单例实例
export const offlineService = new OfflineService();

// 辅助函数：预加载内容以供离线使用
export async function preloadForOffline(contentIds: string[]): Promise<{
  success: string[];
  failed: string[];
}> {
  const success: string[] = [];
  const failed: string[] = [];

  for (const id of contentIds) {
    try {
      const response = await fetch(`/api/content/${id}`);
      if (response.ok) {
        const content = await response.json();
        await offlineService.cacheContent(content);
        success.push(id);
      } else {
        failed.push(id);
      }
    } catch (error) {
      failed.push(id);
    }
  }

  return { success, failed };
}

// 辅助函数：检查内容是否可离线访问
export async function isContentAvailableOffline(contentId: string): Promise<boolean> {
  const content = await offlineService.getCachedContent(contentId);
  return !!content;
}

export default offlineService;
