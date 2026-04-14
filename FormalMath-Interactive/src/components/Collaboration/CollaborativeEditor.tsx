// @ts-nocheck
// ==================== 协同编辑器组件 - 基于Yjs ====================

import React, { useEffect, useRef, useCallback, useState } from 'react';
import * as Y from 'yjs';
import { WebsocketProvider } from 'y-websocket';
import { collaborationService } from '@services/collaborationService';
import { UserPresence, CursorPosition, TextSelection } from '@types/collaboration';
import UserPresenceComponent from './UserPresence';
import ChatPanel from './ChatPanel';
import './CollaborativeEditor.css';

// 编辑器配置
interface CollaborativeEditorProps {
  documentId: string;
  roomId: string;
  userId: string;
  userName: string;
  userAvatar?: string;
  initialContent?: string;
  readOnly?: boolean;
  showChat?: boolean;
  showPresence?: boolean;
  onContentChange?: (content: string) => void;
  onCursorChange?: (cursor: CursorPosition) => void;
  onSelectionChange?: (selection: TextSelection) => void;
  className?: string;
  style?: React.CSSProperties;
}

// 远程光标装饰
interface RemoteCursor {
  user: UserPresence;
  position: CursorPosition;
  element: HTMLDivElement;
}

// 远程选择装饰
interface RemoteSelection {
  user: UserPresence;
  selection: TextSelection;
  elements: HTMLDivElement[];
}

export const CollaborativeEditor: React.FC<CollaborativeEditorProps> = ({
  documentId,
  roomId,
  userId,
  userName,
  userAvatar,
  initialContent = '',
  readOnly = false,
  showChat = true,
  showPresence = true,
  onContentChange,
  onCursorChange,
  onSelectionChange,
  className = '',
  style,
}) => {
  // Refs
  const editorRef = useRef<HTMLDivElement>(null);
  const yDocRef = useRef<Y.Doc | null>(null);
  const yTextRef = useRef<Y.Text | null>(null);
  const providerRef = useRef<WebsocketProvider | null>(null);
  const remoteCursorsRef = useRef<Map<string, RemoteCursor>>(new Map());
  const remoteSelectionsRef = useRef<Map<string, RemoteSelection>>(new Map());
  const isLocalChangeRef = useRef(false);
  const bindingRef = useRef<HTMLBinding | null>(null);

  // State
  const [isReady, setIsReady] = useState(false);
  const [isSynced, setIsSynced] = useState(false);
  const [onlineUsers, setOnlineUsers] = useState<UserPresence[]>([]);
  const [showChatPanel, setShowChatPanel] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // 初始化Yjs协同编辑
  useEffect(() => {
    let isMounted = true;

    const initCollaboration = async () => {
      try {
        // 连接协作服务
        await collaborationService.connect(userId, userName, userAvatar);

        // 加入房间
        await collaborationService.joinRoom(roomId);

        if (!isMounted) return;

        // 获取或创建Yjs文档
        let yDoc = collaborationService.getYDoc();
        if (!yDoc) {
          yDoc = new Y.Doc();
          yDocRef.current = yDoc;
        }

        // 获取或创建共享文本
        let yText = collaborationService.getSharedText('content');
        if (!yText) {
          yText = yDoc.getText('content');
        }
        yTextRef.current = yText;

        // 设置初始内容（如果是新文档）
        if (yText.length === 0 && initialContent) {
          yText.insert(0, initialContent);
        }

        // 获取provider
        const provider = collaborationService.getYProvider();
        if (provider) {
          providerRef.current = provider;
          
          // 监听同步状态
          provider.on('sync', (isSynced: boolean) => {
            if (isMounted) {
              setIsSynced(isSynced);
            }
          });

          // 监听awareness变化（其他用户的光标、选择等）
          provider.awareness.on('change', () => {
            updateRemoteCursors();
          });
        }

        // 绑定编辑器
        if (editorRef.current) {
          bindingRef.current = new HTMLBinding(
            yText,
            editorRef.current,
            providerRef.current?.awareness
          );
        }

        // 监听Yjs文本变化
        yText.observe(() => {
          if (isLocalChangeRef.current) return;
          onContentChange?.(yText.toString());
        });

        // 监听用户presence变化
        const unsubscribeUserJoined = collaborationService.on('room:user-joined', (user) => {
          setOnlineUsers((prev) => [...prev.filter((u) => u.id !== user.id), user]);
        });

        const unsubscribeUserLeft = collaborationService.on('room:user-left', (leftUserId) => {
          setOnlineUsers((prev) => prev.filter((u) => u.id !== leftUserId));
          removeRemoteCursor(leftUserId);
        });

        const unsubscribeUserUpdated = collaborationService.on('room:user-updated', (user) => {
          setOnlineUsers((prev) =>
            prev.map((u) => (u.id === user.id ? user : u))
          );
        });

        // 监听远程光标更新
        const unsubscribeCursor = collaborationService.on('cursor:updated', (remoteUserId, cursor) => {
          const user = onlineUsers.find((u) => u.id === remoteUserId);
          if (user) {
            updateRemoteCursorDisplay(user, cursor);
          }
        });

        // 监听远程选择更新
        const unsubscribeSelection = collaborationService.on('selection:updated', (remoteUserId, selection) => {
          const user = onlineUsers.find((u) => u.id === remoteUserId);
          if (user) {
            updateRemoteSelectionDisplay(user, selection);
          }
        });

        if (isMounted) {
          setIsReady(true);
        }

        return () => {
          unsubscribeUserJoined();
          unsubscribeUserLeft();
          unsubscribeUserUpdated();
          unsubscribeCursor();
          unsubscribeSelection();
        };
      } catch (err) {
        console.error('Failed to initialize collaboration:', err);
        if (isMounted) {
          setError(err instanceof Error ? err.message : '初始化协同编辑失败');
        }
      }
    };

    initCollaboration();

    return () => {
      isMounted = false;
      bindingRef.current?.destroy();
      collaborationService.leaveRoom();
    };
  }, [documentId, roomId, userId, userName, userAvatar, initialContent]);

  // 更新远程光标显示
  const updateRemoteCursors = useCallback(() => {
    const provider = providerRef.current;
    if (!provider) return;

    const states = provider.awareness.getStates() as Map<
      number,
      { user?: UserPresence; cursor?: CursorPosition }
    >;

    states.forEach((state, clientId) => {
      if (state.user && state.user.id !== userId && state.cursor) {
        updateRemoteCursorDisplay(state.user, state.cursor);
      }
    });
  }, [userId]);

  // 更新特定用户的光标显示
  const updateRemoteCursorDisplay = useCallback((user: UserPresence, position: CursorPosition) => {
    if (!editorRef.current) return;

    // 移除旧的光标
    removeRemoteCursor(user.id);

    // 创建新的光标元素
    const cursorEl = document.createElement('div');
    cursorEl.className = 'remote-cursor';
    cursorEl.style.cssText = `
      position: absolute;
      width: 2px;
      height: 1.2em;
      background-color: ${user.color};
      pointer-events: none;
      z-index: 10;
      transition: all 0.1s ease;
    `;

    // 创建用户标签
    const labelEl = document.createElement('div');
    labelEl.className = 'remote-cursor-label';
    labelEl.textContent = user.name;
    labelEl.style.cssText = `
      position: absolute;
      top: -1.5em;
      left: 0;
      background-color: ${user.color};
      color: white;
      font-size: 12px;
      padding: 2px 6px;
      border-radius: 3px;
      white-space: nowrap;
      pointer-events: none;
    `;

    cursorEl.appendChild(labelEl);
    editorRef.current.appendChild(cursorEl);

    // 定位光标（简化版，实际应根据文本位置计算）
    const charWidth = 8; // 估算字符宽度
    const lineHeight = 20; // 估算行高
    cursorEl.style.left = `${position.column ? position.column * charWidth : position.x}px`;
    cursorEl.style.top = `${position.line ? position.line * lineHeight : position.y}px`;

    remoteCursorsRef.current.set(user.id, {
      user,
      position,
      element: cursorEl,
    });
  }, []);

  // 移除远程光标
  const removeRemoteCursor = useCallback((userId: string) => {
    const cursor = remoteCursorsRef.current.get(userId);
    if (cursor) {
      cursor.element.remove();
      remoteCursorsRef.current.delete(userId);
    }
  }, []);

  // 更新远程选择显示
  const updateRemoteSelectionDisplay = useCallback((user: UserPresence, selection: TextSelection) => {
    if (!editorRef.current) return;

    // 移除旧的选择
    removeRemoteSelection(user.id);

    const selectionElements: HTMLDivElement[] = [];
    const charWidth = 8;
    const lineHeight = 20;

    // 创建选择高亮元素
    const selectionEl = document.createElement('div');
    selectionEl.className = 'remote-selection';
    selectionEl.style.cssText = `
      position: absolute;
      background-color: ${user.color}33;
      pointer-events: none;
      z-index: 5;
    `;

    // 简化的选择范围计算
    const startX = (selection.start % 80) * charWidth;
    const startY = Math.floor(selection.start / 80) * lineHeight;
    const endX = (selection.end % 80) * charWidth;
    const endY = Math.floor(selection.end / 80) * lineHeight;

    selectionEl.style.left = `${startX}px`;
    selectionEl.style.top = `${startY}px`;
    selectionEl.style.width = `${endX - startX}px`;
    selectionEl.style.height = `${Math.max(endY - startY + lineHeight, lineHeight)}px`;

    editorRef.current.appendChild(selectionEl);
    selectionElements.push(selectionEl);

    remoteSelectionsRef.current.set(user.id, {
      user,
      selection,
      elements: selectionElements,
    });
  }, []);

  // 移除远程选择
  const removeRemoteSelection = useCallback((userId: string) => {
    const selection = remoteSelectionsRef.current.get(userId);
    if (selection) {
      selection.elements.forEach((el) => el.remove());
      remoteSelectionsRef.current.delete(userId);
    }
  }, []);

  // 处理编辑器点击/输入事件
  const handleEditorClick = useCallback((e: React.MouseEvent) => {
    if (!editorRef.current) return;

    const rect = editorRef.current.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // 计算光标位置（简化版）
    const charWidth = 8;
    const lineHeight = 20;
    const column = Math.floor(x / charWidth);
    const line = Math.floor(y / lineHeight);

    const cursor: CursorPosition = {
      x,
      y,
      line,
      column,
      documentId,
    };

    collaborationService.updateCursor(cursor);
    onCursorChange?.(cursor);
  }, [documentId, onCursorChange]);

  // 处理选择变化
  const handleSelectionChange = useCallback(() => {
    const selection = window.getSelection();
    if (!selection || !editorRef.current) return;

    const range = selection.getRangeAt(0);
    const start = getTextOffset(editorRef.current, range.startContainer, range.startOffset);
    const end = getTextOffset(editorRef.current, range.endContainer, range.endOffset);

    const textSelection: TextSelection = {
      start,
      end,
      documentId,
    };

    collaborationService.updateSelection(textSelection);
    onSelectionChange?.(textSelection);
  }, [documentId, onSelectionChange]);

  // 处理输入
  const handleInput = useCallback((e: React.FormEvent<HTMLDivElement>) => {
    if (!yTextRef.current || !editorRef.current) return;

    isLocalChangeRef.current = true;
    const newContent = editorRef.current.innerText;

    // 更新Yjs文档
    yTextRef.current.delete(0, yTextRef.current.length);
    yTextRef.current.insert(0, newContent);

    onContentChange?.(newContent);
    isLocalChangeRef.current = false;
  }, [onContentChange]);

  // 获取文本偏移量
  const getTextOffset = (root: Node, targetNode: Node, targetOffset: number): number => {
    let offset = 0;
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
    let node: Node | null;

    while ((node = walker.nextNode())) {
      if (node === targetNode) {
        return offset + targetOffset;
      }
      offset += node.textContent?.length || 0;
    }

    return offset;
  };

  if (error) {
    return (
      <div className={`collaborative-editor error ${className}`} style={style}>
        <div className="error-message">
          <p>协同编辑初始化失败</p>
          <p className="error-detail">{error}</p>
          <button onClick={() => window.location.reload()}>重试</button>
        </div>
      </div>
    );
  }

  return (
    <div className={`collaborative-editor ${className}`} style={style}>
      {/* 工具栏 */}
      <div className="editor-toolbar">
        {showPresence && (
          <UserPresenceComponent
            users={onlineUsers}
            currentUserId={userId}
            showAvatars={true}
            maxDisplay={5}
          />
        )}
        <div className="editor-actions">
          <button
            className="chat-toggle-btn"
            onClick={() => setShowChatPanel(!showChatPanel)}
            title="切换聊天面板"
          >
            💬
          </button>
          {!isSynced && <span className="sync-status">同步中...</span>}
        </div>
      </div>

      {/* 编辑器主体 */}
      <div className="editor-container">
        <div
          ref={editorRef}
          className="editor-content"
          contentEditable={!readOnly && isReady}
          onClick={handleEditorClick}
          onInput={handleInput}
          onSelect={handleSelectionChange}
          suppressContentEditableWarning={true}
          style={{
            minHeight: '300px',
            padding: '16px',
            outline: 'none',
            whiteSpace: 'pre-wrap',
            wordWrap: 'break-word',
          }}
        >
          {!isReady && <div className="loading">正在连接协同编辑服务...</div>}
        </div>

        {/* 聊天面板 */}
        {showChat && showChatPanel && (
          <ChatPanel
            roomId={roomId}
            userId={userId}
            userName={userName}
            userAvatar={userAvatar}
            onClose={() => setShowChatPanel(false)}
          />
        )}
      </div>

      {/* 状态栏 */}
      <div className="editor-statusbar">
        <span>{onlineUsers.length + 1} 人在线</span>
        <span>{isSynced ? '已同步' : '同步中...'}</span>
      </div>
    </div>
  );
};

// HTML绑定类 - 简化版的编辑器绑定
class HTMLBinding {
  private yText: Y.Text;
  private dom: HTMLElement;
  private awareness: unknown;
  private observer: MutationObserver;

  constructor(yText: Y.Text, dom: HTMLElement, awareness?: unknown) {
    this.yText = yText;
    this.dom = dom;
    this.awareness = awareness;

    // 初始内容同步
    this.syncFromYjs();

    // 监听DOM变化
    this.observer = new MutationObserver((mutations) => {
      this.handleMutations(mutations);
    });

    this.observer.observe(dom, {
      characterData: true,
      characterDataOldValue: true,
      childList: true,
      subtree: true,
    });

    // 监听Yjs变化
    yText.observe(() => {
      this.syncFromYjs();
    });
  }

  private syncFromYjs(): void {
    const content = this.yText.toString();
    if (this.dom.innerText !== content) {
      this.dom.innerText = content;
    }
  }

  private handleMutations(mutations: MutationRecord[]): void {
    // 处理DOM变化并同步到Yjs
    // 这里简化处理，实际应使用更复杂的差异算法
    const newContent = this.dom.innerText;
    if (this.yText.toString() !== newContent) {
      this.yText.delete(0, this.yText.length);
      this.yText.insert(0, newContent);
    }
  }

  destroy(): void {
    this.observer.disconnect();
  }
}

export default CollaborativeEditor;
