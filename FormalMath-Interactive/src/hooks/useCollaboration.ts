// @ts-nocheck
// ==================== 协作功能Hook ====================

import { useState, useEffect, useCallback, useRef } from 'react';
import { collaborationService } from '@services/collaborationService';
import {
  ConnectionState,
  UserPresence,
  CollaborationRoom,
  ChatMessage,
  Comment,
  DocumentVersion,
  ProgressUpdate,
  SharedLearningPath,
  TeamChallenge,
} from '@types/collaboration';

// 连接状态Hook
export function useConnectionState(): ConnectionState {
  const [state, setState] = useState<ConnectionState>('disconnected');

  useEffect(() => {
    const updateState = () => {
      setState(collaborationService.getConnectionState());
    };

    updateState();

    const unsubscribeConnect = collaborationService.on('connect', updateState);
    const unsubscribeDisconnect = collaborationService.on('disconnect', updateState);
    const unsubscribeReconnect = collaborationService.on('reconnect', updateState);
    const unsubscribeReconnectAttempt = collaborationService.on('reconnect_attempt', updateState);

    return () => {
      unsubscribeConnect();
      unsubscribeDisconnect();
      unsubscribeReconnect();
      unsubscribeReconnectAttempt();
    };
  }, []);

  return state;
}

// 在线用户Hook
export function useOnlineUsers(roomId?: string): UserPresence[] {
  const [users, setUsers] = useState<UserPresence[]>([]);

  useEffect(() => {
    if (!roomId) return;

    const handleUserJoined = (user: UserPresence) => {
      setUsers((prev) => {
        const filtered = prev.filter((u) => u.id !== user.id);
        return [...filtered, user];
      });
    };

    const handleUserLeft = (userId: string) => {
      setUsers((prev) => prev.filter((u) => u.id !== userId));
    };

    const handleUserUpdated = (user: UserPresence) => {
      setUsers((prev) =>
        prev.map((u) => (u.id === user.id ? user : u))
      );
    };

    const unsubscribeJoined = collaborationService.on('room:user-joined', handleUserJoined);
    const unsubscribeLeft = collaborationService.on('room:user-left', handleUserLeft);
    const unsubscribeUpdated = collaborationService.on('room:user-updated', handleUserUpdated);

    return () => {
      unsubscribeJoined();
      unsubscribeLeft();
      unsubscribeUpdated();
    };
  }, [roomId]);

  return users;
}

// 聊天消息Hook
export function useChatMessages(roomId: string): {
  messages: ChatMessage[];
  sendMessage: (content: string, replyTo?: string) => Promise<void>;
  isTyping: (userId: string) => boolean;
  sendTypingStatus: (isTyping: boolean) => void;
} {
  const [messages, setMessages] = useState<ChatMessage[]>([]);
  const [typingUsers, setTypingUsers] = useState<Set<string>>(new Set());

  useEffect(() => {
    // 加载历史消息
    collaborationService.getMessages(50).then((history) => {
      setMessages(history);
    }).catch(console.error);

    // 监听新消息
    const unsubscribeMessage = collaborationService.on('chat:message', (message) => {
      setMessages((prev) => [...prev, message]);
    });

    // 监听输入状态
    const unsubscribeTyping = collaborationService.on('chat:typing', (userId, isTyping) => {
      setTypingUsers((prev) => {
        const next = new Set(prev);
        if (isTyping) {
          next.add(userId);
        } else {
          next.delete(userId);
        }
        return next;
      });
    });

    return () => {
      unsubscribeMessage();
      unsubscribeTyping();
    };
  }, [roomId]);

  const sendMessage = useCallback(async (content: string, replyTo?: string) => {
    await collaborationService.sendMessage(content, replyTo);
  }, []);

  const isTyping = useCallback((userId: string) => {
    return typingUsers.has(userId);
  }, [typingUsers]);

  const sendTypingStatus = useCallback((isTyping: boolean) => {
    collaborationService.sendTypingStatus(isTyping);
  }, []);

  return { messages, sendMessage, isTyping, sendTypingStatus };
}

// 评论Hook
export function useComments(documentId: string): {
  comments: Comment[];
  createComment: (content: string, position: { start: number; end: number; line?: number }) => Promise<void>;
  replyToComment: (commentId: string, content: string) => Promise<void>;
  resolveComment: (commentId: string) => void;
  deleteComment: (commentId: string) => void;
} {
  const [comments, setComments] = useState<Comment[]>([]);

  useEffect(() => {
    // 加载评论
    collaborationService.getComments(documentId).then((list) => {
      setComments(list);
    }).catch(console.error);

    // 监听评论事件
    const unsubscribeCreated = collaborationService.on('comment:created', (comment) => {
      if (comment.documentId === documentId) {
        setComments((prev) => [...prev, comment]);
      }
    });

    const unsubscribeUpdated = collaborationService.on('comment:updated', (comment) => {
      setComments((prev) =>
        prev.map((c) => (c.id === comment.id ? comment : c))
      );
    });

    const unsubscribeDeleted = collaborationService.on('comment:deleted', (commentId) => {
      setComments((prev) => prev.filter((c) => c.id !== commentId));
    });

    const unsubscribeResolved = collaborationService.on('comment:resolved', (commentId) => {
      setComments((prev) =>
        prev.map((c) =>
          c.id === commentId ? { ...c, resolved: true } : c
        )
      );
    });

    return () => {
      unsubscribeCreated();
      unsubscribeUpdated();
      unsubscribeDeleted();
      unsubscribeResolved();
    };
  }, [documentId]);

  const createComment = useCallback(async (content: string, position: { start: number; end: number; line?: number }) => {
    await collaborationService.createComment(content, position);
  }, []);

  const replyToComment = useCallback(async (commentId: string, content: string) => {
    await collaborationService.replyToComment(commentId, content);
  }, []);

  const resolveComment = useCallback((commentId: string) => {
    collaborationService.resolveComment(commentId);
  }, []);

  const deleteComment = useCallback((commentId: string) => {
    collaborationService.deleteComment(commentId);
  }, []);

  return { comments, createComment, replyToComment, resolveComment, deleteComment };
}

// 版本历史Hook
export function useVersionHistory(documentId: string): {
  versions: DocumentVersion[];
  createVersion: (comment?: string) => Promise<void>;
  restoreVersion: (versionId: string) => Promise<void>;
  isLoading: boolean;
} {
  const [versions, setVersions] = useState<DocumentVersion[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  useEffect(() => {
    setIsLoading(true);
    collaborationService.getVersions(documentId)
      .then((list) => {
        setVersions(list.sort((a, b) => b.createdAt - a.createdAt));
      })
      .catch(console.error)
      .finally(() => setIsLoading(false));

    const unsubscribe = collaborationService.on('version:created', (version) => {
      if (version.documentId === documentId) {
        setVersions((prev) => [version, ...prev]);
      }
    });

    return () => {
      unsubscribe();
    };
  }, [documentId]);

  const createVersion = useCallback(async (comment?: string) => {
    await collaborationService.createVersion(comment);
  }, []);

  const restoreVersion = useCallback(async (versionId: string) => {
    await collaborationService.restoreVersion(versionId);
  }, []);

  return { versions, createVersion, restoreVersion, isLoading };
}

// 共享学习路径Hook
export function useSharedLearningPaths(): {
  paths: SharedLearningPath[];
  createPath: (name: string, description: string, participants: string[]) => Promise<void>;
  updateProgress: (update: ProgressUpdate) => void;
  isLoading: boolean;
} {
  const [paths, setPaths] = useState<SharedLearningPath[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  useEffect(() => {
    setIsLoading(true);
    collaborationService.getSharedPaths()
      .then((list) => setPaths(list))
      .catch(console.error)
      .finally(() => setIsLoading(false));

    const unsubscribe = collaborationService.on('path:updated', (path) => {
      setPaths((prev) =>
        prev.map((p) => (p.id === path.id ? path : p))
      );
    });

    return () => unsubscribe();
  }, []);

  const createPath = useCallback(async (name: string, description: string, participants: string[]) => {
    await collaborationService.createSharedPath(name, description, participants);
  }, []);

  const updateProgress = useCallback((update: ProgressUpdate) => {
    collaborationService.updateProgress(update);
  }, []);

  return { paths, createPath, updateProgress, isLoading };
}

// 组队挑战Hook
export function useTeamChallenges(): {
  challenges: TeamChallenge[];
  createChallenge: (challenge: Partial<TeamChallenge>) => Promise<void>;
  joinChallenge: (challengeId: string, teamId?: string) => Promise<void>;
  updateProgress: (challengeId: string, teamId: string, progress: number) => void;
  updateScore: (challengeId: string, teamId: string, points: number) => void;
} {
  const [challenges, setChallenges] = useState<TeamChallenge[]>([]);

  useEffect(() => {
    // 监听挑战事件
    const unsubscribeStarted = collaborationService.on('challenge:started', (challenge) => {
      setChallenges((prev) => [...prev, challenge]);
    });

    const unsubscribeProgress = collaborationService.on('challenge:progress', (challengeId, teamId, progress) => {
      setChallenges((prev) =>
        prev.map((c) =>
          c.id === challengeId
            ? {
                ...c,
                teams: c.teams.map((t) =>
                  t.id === teamId ? { ...t, progress } : t
                ),
              }
            : c
        )
      );
    });

    const unsubscribeScore = collaborationService.on('challenge:score-update', (challengeId, teamId, score) => {
      setChallenges((prev) =>
        prev.map((c) =>
          c.id === challengeId
            ? {
                ...c,
                teams: c.teams.map((t) =>
                  t.id === teamId ? { ...t, score } : t
                ),
              }
            : c
        )
      );
    });

    return () => {
      unsubscribeStarted();
      unsubscribeProgress();
      unsubscribeScore();
    };
  }, []);

  const createChallenge = useCallback(async (challenge: Partial<TeamChallenge>) => {
    await collaborationService.createChallenge(challenge);
  }, []);

  const joinChallenge = useCallback(async (challengeId: string, teamId?: string) => {
    await collaborationService.joinChallenge(challengeId, teamId);
  }, []);

  const updateProgress = useCallback((challengeId: string, teamId: string, progress: number) => {
    collaborationService.updateChallengeProgress(challengeId, teamId, progress);
  }, []);

  const updateScore = useCallback((challengeId: string, teamId: string, points: number) => {
    collaborationService.updateChallengeScore(challengeId, teamId, points);
  }, []);

  return { challenges, createChallenge, joinChallenge, updateProgress, updateScore };
}

// 协同编辑器Hook
export function useCollaborativeEditor(
  documentId: string,
  roomId: string,
  userId: string,
  userName: string
): {
  isReady: boolean;
  isSynced: boolean;
  onlineUsers: UserPresence[];
  content: string;
  updateContent: (content: string) => void;
  updateCursor: (x: number, y: number, line?: number, column?: number) => void;
} {
  const [isReady, setIsReady] = useState(false);
  const [isSynced, setIsSynced] = useState(false);
  const [onlineUsers, setOnlineUsers] = useState<UserPresence[]>([]);
  const [content, setContent] = useState('');

  useEffect(() => {
    let isMounted = true;

    const init = async () => {
      try {
        await collaborationService.connect(userId, userName);
        await collaborationService.joinRoom(roomId);

        if (!isMounted) return;

        const yText = collaborationService.getSharedText('content');
        if (yText) {
          setContent(yText.toString());
          yText.observe(() => {
            if (isMounted) {
              setContent(yText.toString());
            }
          });
        }

        const provider = collaborationService.getYProvider();
        if (provider) {
          provider.on('sync', (synced: boolean) => {
            if (isMounted) setIsSynced(synced);
          });
        }

        if (isMounted) setIsReady(true);
      } catch (error) {
        console.error('Failed to initialize collaborative editor:', error);
      }
    };

    init();

    // 监听用户presence
    const unsubscribeJoined = collaborationService.on('room:user-joined', (user) => {
      setOnlineUsers((prev) => [...prev.filter((u) => u.id !== user.id), user]);
    });

    const unsubscribeLeft = collaborationService.on('room:user-left', (userId) => {
      setOnlineUsers((prev) => prev.filter((u) => u.id !== userId));
    });

    return () => {
      isMounted = false;
      unsubscribeJoined();
      unsubscribeLeft();
      collaborationService.leaveRoom();
    };
  }, [documentId, roomId, userId, userName]);

  const updateContent = useCallback((newContent: string) => {
    const yText = collaborationService.getSharedText('content');
    if (yText) {
      yText.delete(0, yText.length);
      yText.insert(0, newContent);
    }
    setContent(newContent);
  }, []);

  const updateCursor = useCallback((x: number, y: number, line?: number, column?: number) => {
    collaborationService.updateCursor({
      x,
      y,
      line,
      column,
      documentId,
    });
  }, [documentId]);

  return { isReady, isSynced, onlineUsers, content, updateContent, updateCursor };
}

export default useCollaboration;
