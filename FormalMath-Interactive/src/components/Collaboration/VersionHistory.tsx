// ==================== 版本历史组件 ====================

import React, { useState, useEffect, useCallback } from 'react';
import { collaborationService } from '@services/collaborationService';
import { DocumentVersion, VersionChange } from '@types/collaboration';
import './VersionHistory.css';

// 组件Props
interface VersionHistoryProps {
  documentId: string;
  currentContent?: string;
  onVersionSelect?: (version: DocumentVersion) => void;
  onVersionRestore?: (versionId: string) => void;
  onCompare?: (v1: DocumentVersion, v2: DocumentVersion) => void;
  className?: string;
}

// 视图模式
type ViewMode = 'list' | 'timeline' | 'compare';

export const VersionHistory: React.FC<VersionHistoryProps> = ({
  documentId,
  currentContent,
  onVersionSelect,
  onVersionRestore,
  onCompare,
  className = '',
}) => {
  // State
  const [versions, setVersions] = useState<DocumentVersion[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [viewMode, setViewMode] = useState<ViewMode>('list');
  const [selectedVersion, setSelectedVersion] = useState<DocumentVersion | null>(null);
  const [compareVersions, setCompareVersions] = useState<[string, string] | null>(null);
  const [showPreview, setShowPreview] = useState(false);
  const [restoring, setRestoring] = useState<string | null>(null);

  // 加载版本历史
  const loadVersions = useCallback(async () => {
    try {
      setIsLoading(true);
      setError(null);
      const history = await collaborationService.getVersions(documentId);
      setVersions(history.sort((a, b) => b.createdAt - a.createdAt));
    } catch (err) {
      setError(err instanceof Error ? err.message : '加载版本历史失败');
      console.error('Failed to load versions:', err);
    } finally {
      setIsLoading(false);
    }
  }, [documentId]);

  // 初始加载和监听
  useEffect(() => {
    loadVersions();

    // 监听新版本创建
    const unsubscribe = collaborationService.on('version:created', (version) => {
      if (version.documentId === documentId) {
        setVersions((prev) => [version, ...prev]);
      }
    });

    return () => {
      unsubscribe();
    };
  }, [documentId, loadVersions]);

  // 创建新版本
  const handleCreateVersion = useCallback(async (comment?: string) => {
    try {
      const newVersion = await collaborationService.createVersion(comment);
      setVersions((prev) => [newVersion, ...prev]);
    } catch (err) {
      console.error('Failed to create version:', err);
    }
  }, []);

  // 恢复到指定版本
  const handleRestore = useCallback(async (version: DocumentVersion) => {
    if (!window.confirm(`确定要恢复到版本 "${version.comment || `版本 ${version.version}`}" 吗？当前内容将被覆盖。`)) {
      return;
    }

    try {
      setRestoring(version.id);
      await collaborationService.restoreVersion(version.id);
      onVersionRestore?.(version.id);
      
      // 刷新版本列表
      await loadVersions();
    } catch (err) {
      console.error('Failed to restore version:', err);
      alert('恢复版本失败');
    } finally {
      setRestoring(null);
    }
  }, [loadVersions, onVersionRestore]);

  // 选择版本进行预览
  const handleSelectVersion = useCallback((version: DocumentVersion) => {
    setSelectedVersion(version);
    setShowPreview(true);
    onVersionSelect?.(version);
  }, [onVersionSelect]);

  // 添加到对比
  const handleAddToCompare = useCallback((versionId: string) => {
    setCompareVersions((prev) => {
      if (!prev) return [versionId, ''];
      if (prev[0] === versionId || prev[1] === versionId) {
        return prev[0] === versionId ? ['', prev[1]] : [prev[0], ''];
      }
      if (!prev[0]) return [versionId, prev[1]];
      if (!prev[1]) return [prev[0], versionId];
      return [versionId, prev[1]];
    });
  }, []);

  // 执行对比
  const handleCompare = useCallback(() => {
    if (!compareVersions || !compareVersions[0] || !compareVersions[1]) return;
    
    const v1 = versions.find((v) => v.id === compareVersions[0]);
    const v2 = versions.find((v) => v.id === compareVersions[1]);
    
    if (v1 && v2) {
      onCompare?.(v1, v2);
    }
  }, [compareVersions, versions, onCompare]);

  // 格式化时间
  const formatTime = useCallback((timestamp: number): string => {
    const date = new Date(timestamp);
    const now = new Date();
    const diff = now.getTime() - date.getTime();
    
    // 小于1小时
    if (diff < 3600000) {
      const minutes = Math.floor(diff / 60000);
      return minutes < 1 ? '刚刚' : `${minutes}分钟前`;
    }
    
    // 小于24小时
    if (diff < 86400000) {
      const hours = Math.floor(diff / 3600000);
      return `${hours}小时前`;
    }
    
    // 小于7天
    if (diff < 604800000) {
      const days = Math.floor(diff / 86400000);
      return `${days}天前`;
    }
    
    return date.toLocaleDateString('zh-CN', {
      year: 'numeric',
      month: 'short',
      day: 'numeric',
      hour: '2-digit',
      minute: '2-digit',
    });
  }, []);

  // 格式化文件大小
  const formatSize = useCallback((content: unknown): string => {
    const size = JSON.stringify(content).length;
    if (size < 1024) return `${size} B`;
    if (size < 1024 * 1024) return `${(size / 1024).toFixed(1)} KB`;
    return `${(size / (1024 * 1024)).toFixed(1)} MB`;
  }, []);

  // 渲染变更摘要
  const renderChangeSummary = (changes: VersionChange[]): React.ReactNode => {
    if (!changes || changes.length === 0) return <span className="no-changes">无变更记录</span>;
    
    const insertions = changes.filter((c) => c.type === 'insert').length;
    const deletions = changes.filter((c) => c.type === 'delete').length;
    const updates = changes.filter((c) => c.type === 'update').length;
    
    return (
      <span className="change-summary">
        {insertions > 0 && <span className="change-insert">+{insertions}</span>}
        {deletions > 0 && <span className="change-delete">-{deletions}</span>}
        {updates > 0 && <span className="change-update">~{updates}</span>}
      </span>
    );
  };

  // 渲染列表视图
  const renderListView = () => (
    <div className="versions-list">
      {versions.map((version, index) => {
        const isSelected = selectedVersion?.id === version.id;
        const isInCompare = compareVersions?.includes(version.id);
        const isCurrent = index === 0;
        
        return (
          <div
            key={version.id}
            className={`version-item ${isSelected ? 'selected' : ''} ${isCurrent ? 'current' : ''}`}
            onClick={() => handleSelectVersion(version)}
          >
            <div className="version-marker">
              <div className="version-dot" />
              {index < versions.length - 1 && <div className="version-line" />}
            </div>
            
            <div className="version-content">
              <div className="version-header">
                <span className="version-number">版本 {version.version}</span>
                {isCurrent && <span className="current-badge">当前</span>}
                {viewMode === 'compare' && (
                  <label className="compare-checkbox">
                    <input
                      type="checkbox"
                      checked={isInCompare}
                      onChange={() => handleAddToCompare(version.id)}
                      onClick={(e) => e.stopPropagation()}
                    />
                    对比
                  </label>
                )}
              </div>
              
              {version.comment && (
                <p className="version-comment">{version.comment}</p>
              )}
              
              <div className="version-meta">
                <span className="version-author">{version.createdBy}</span>
                <span className="version-time">{formatTime(version.createdAt)}</span>
                <span className="version-size">{formatSize(version.content)}</span>
              </div>
              
              <div className="version-changes">
                {renderChangeSummary(version.changes)}
              </div>
              
              <div className="version-actions">
                <button
                  className="action-btn preview-btn"
                  onClick={(e) => {
                    e.stopPropagation();
                    handleSelectVersion(version);
                  }}
                >
                  预览
                </button>
                {!isCurrent && (
                  <button
                    className="action-btn restore-btn"
                    onClick={(e) => {
                      e.stopPropagation();
                      handleRestore(version);
                    }}
                    disabled={restoring === version.id}
                  >
                    {restoring === version.id ? '恢复中...' : '恢复'}
                  </button>
                )}
              </div>
            </div>
          </div>
        );
      })}
    </div>
  );

  // 渲染时间线视图
  const renderTimelineView = () => {
    // 按日期分组
    const groupedByDate = versions.reduce((acc, version) => {
      const date = new Date(version.createdAt).toDateString();
      if (!acc[date]) acc[date] = [];
      acc[date].push(version);
      return acc;
    }, {} as Record<string, DocumentVersion[]>);

    return (
      <div className="versions-timeline">
        {Object.entries(groupedByDate).map(([date, dateVersions]) => (
          <div key={date} className="timeline-group">
            <div className="timeline-date">
              {new Date(date).toLocaleDateString('zh-CN', {
                month: 'long',
                day: 'numeric',
                weekday: 'short',
              })}
            </div>
            <div className="timeline-items">
              {dateVersions.map((version) => (
                <div
                  key={version.id}
                  className="timeline-item"
                  onClick={() => handleSelectVersion(version)}
                >
                  <span className="timeline-time">
                    {new Date(version.createdAt).toLocaleTimeString('zh-CN', {
                      hour: '2-digit',
                      minute: '2-digit',
                    })}
                  </span>
                  <div className="timeline-dot" />
                  <div className="timeline-content">
                    <span className="timeline-version">v{version.version}</span>
                    <span className="timeline-comment">
                      {version.comment || '无描述'}
                    </span>
                    <span className="timeline-author">by {version.createdBy}</span>
                  </div>
                </div>
              ))}
            </div>
          </div>
        ))}
      </div>
    );
  };

  // 渲染对比视图
  const renderCompareView = () => {
    if (!compareVersions || !compareVersions[0] || !compareVersions[1]) {
      return (
        <div className="compare-placeholder">
          <p>请选择两个版本进行对比</p>
          <div className="compare-selection">
            <div className={`compare-slot ${compareVersions?.[0] ? 'filled' : ''}`}>
              {compareVersions?.[0]
                ? `版本 ${versions.find((v) => v.id === compareVersions[0])?.version}`
                : '选择版本 A'}
            </div>
            <span className="compare-vs">VS</span>
            <div className={`compare-slot ${compareVersions?.[1] ? 'filled' : ''}`}>
              {compareVersions?.[1]
                ? `版本 ${versions.find((v) => v.id === compareVersions[1])?.version}`
                : '选择版本 B'}
            </div>
          </div>
          <button
            className="compare-btn"
            onClick={handleCompare}
            disabled={!compareVersions || !compareVersions[0] || !compareVersions[1]}
          >
            开始对比
          </button>
        </div>
      );
    }

    return null;
  };

  // 渲染预览面板
  const renderPreview = () => {
    if (!showPreview || !selectedVersion) return null;

    return (
      <div className="version-preview-overlay" onClick={() => setShowPreview(false)}>
        <div className="version-preview-panel" onClick={(e) => e.stopPropagation()}>
          <div className="preview-header">
            <h3>版本预览 - 版本 {selectedVersion.version}</h3>
            <button className="close-btn" onClick={() => setShowPreview(false)}>
              ✕
            </button>
          </div>
          <div className="preview-info">
            <p><strong>作者:</strong> {selectedVersion.createdBy}</p>
            <p><strong>时间:</strong> {new Date(selectedVersion.createdAt).toLocaleString('zh-CN')}</p>
            {selectedVersion.comment && (
              <p><strong>备注:</strong> {selectedVersion.comment}</p>
            )}
          </div>
          <div className="preview-content">
            <pre>{JSON.stringify(selectedVersion.content, null, 2)}</pre>
          </div>
          <div className="preview-actions">
            <button
              className="restore-btn"
              onClick={() => handleRestore(selectedVersion)}
              disabled={restoring === selectedVersion.id}
            >
              {restoring === selectedVersion.id ? '恢复中...' : '恢复此版本'}
            </button>
          </div>
        </div>
      </div>
    );
  };

  if (isLoading && versions.length === 0) {
    return (
      <div className={`version-history loading ${className}`}>
        <div className="loading-spinner">加载版本历史...</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className={`version-history error ${className}`}>
        <div className="error-message">
          <p>加载失败</p>
          <p className="error-detail">{error}</p>
          <button onClick={loadVersions}>重试</button>
        </div>
      </div>
    );
  }

  return (
    <div className={`version-history ${className}`}>
      {/* 头部工具栏 */}
      <div className="version-history-header">
        <h3>版本历史</h3>
        <div className="view-mode-tabs">
          <button
            className={viewMode === 'list' ? 'active' : ''}
            onClick={() => setViewMode('list')}
          >
            列表
          </button>
          <button
            className={viewMode === 'timeline' ? 'active' : ''}
            onClick={() => setViewMode('timeline')}
          >
            时间线
          </button>
          <button
            className={viewMode === 'compare' ? 'active' : ''}
            onClick={() => {
              setViewMode('compare');
              setCompareVersions(null);
            }}
          >
            对比
          </button>
        </div>
        <button
          className="create-version-btn"
          onClick={() => {
            const comment = prompt('请输入版本备注（可选）:');
            handleCreateVersion(comment || undefined);
          }}
          title="保存当前内容为新版本"
        >
          + 保存版本
        </button>
      </div>

      {/* 内容区域 */}
      <div className="version-history-content">
        {versions.length === 0 ? (
          <div className="empty-state">
            <p>暂无版本历史</p>
            <p className="empty-hint">点击"保存版本"创建第一个版本</p>
          </div>
        ) : (
          <>
            {viewMode === 'list' && renderListView()}
            {viewMode === 'timeline' && renderTimelineView()}
            {viewMode === 'compare' && renderCompareView()}
          </>
        )}
      </div>

      {/* 对比操作栏 */}
      {viewMode === 'compare' && compareVersions && (compareVersions[0] || compareVersions[1]) && (
        <div className="compare-toolbar">
          <span>
            已选择: {' '}
            {compareVersions[0] && `版本 ${versions.find(v => v.id === compareVersions[0])?.version}`}
            {' '}{compareVersions[0] && compareVersions[1] && '和'}{' '}
            {compareVersions[1] && `版本 ${versions.find(v => v.id === compareVersions[1])?.version}`}
          </span>
          <button
            onClick={() => setCompareVersions(null)}
            className="clear-compare-btn"
          >
            清除选择
          </button>
        </div>
      )}

      {/* 预览面板 */}
      {renderPreview()}
    </div>
  );
};

export default VersionHistory;
