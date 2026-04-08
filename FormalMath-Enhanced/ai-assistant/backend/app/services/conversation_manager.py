"""
对话管理器
管理多轮对话和上下文持久化
"""
import json
import logging
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from enum import Enum
import asyncio

logger = logging.getLogger(__name__)


class ConversationStatus(Enum):
    """对话状态"""
    ACTIVE = "active"
    PAUSED = "paused"
    COMPLETED = "completed"
    EXPIRED = "expired"


@dataclass
class Message:
    """对话消息"""
    role: str  # 'user', 'assistant', 'system'
    content: str
    timestamp: datetime = field(default_factory=datetime.now)
    message_type: str = "text"  # 'text', 'formula', 'code'
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict:
        return {
            'role': self.role,
            'content': self.content,
            'timestamp': self.timestamp.isoformat(),
            'message_type': self.message_type,
            'metadata': self.metadata
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'Message':
        return cls(
            role=data['role'],
            content=data['content'],
            timestamp=datetime.fromisoformat(data['timestamp']),
            message_type=data.get('message_type', 'text'),
            metadata=data.get('metadata', {})
        )


@dataclass
class ConversationSession:
    """对话会话"""
    session_id: str
    user_id: Optional[str]
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    status: ConversationStatus = ConversationStatus.ACTIVE
    messages: List[Message] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    # 数学专用字段
    current_topic: Optional[str] = None
    related_concepts: List[str] = field(default_factory=list)
    latex_formulas: List[str] = field(default_factory=list)
    
    def add_message(self, role: str, content: str, **kwargs):
        """添加消息"""
        message = Message(role=role, content=content, **kwargs)
        self.messages.append(message)
        self.last_activity = datetime.now()
        
        # 提取LaTeX公式
        if role == 'assistant':
            self._extract_formulas(content)
    
    def _extract_formulas(self, text: str):
        """提取LaTeX公式"""
        import re
        
        # 匹配行内和独立公式
        patterns = [
            r'\$\$(.*?)\$\$',  # 独立公式
            r'(?<!\$)\$(?!\$)([^\$]+?)\$(?!\$)'  # 行内公式
        ]
        
        for pattern in patterns:
            matches = re.findall(pattern, text, re.DOTALL)
            self.latex_formulas.extend(matches)
        
        # 去重
        self.latex_formulas = list(set(self.latex_formulas))
    
    def get_recent_messages(self, n: int = 5) -> List[Dict]:
        """获取最近n条消息"""
        recent = self.messages[-n:] if len(self.messages) > n else self.messages
        return [m.to_dict() for m in recent]
    
    def get_context_for_llm(self, max_messages: int = 10) -> List[Dict]:
        """获取用于LLM的上下文"""
        # 保留系统消息和最近的用户/助手消息
        system_messages = [m for m in self.messages if m.role == 'system']
        other_messages = [m for m in self.messages if m.role != 'system']
        
        recent = other_messages[-max_messages:] if len(other_messages) > max_messages else other_messages
        selected = system_messages + recent
        
        return [{'role': m.role, 'content': m.content} for m in selected]
    
    def to_dict(self) -> Dict:
        return {
            'session_id': self.session_id,
            'user_id': self.user_id,
            'created_at': self.created_at.isoformat(),
            'last_activity': self.last_activity.isoformat(),
            'status': self.status.value,
            'messages': [m.to_dict() for m in self.messages],
            'metadata': self.metadata,
            'current_topic': self.current_topic,
            'related_concepts': self.related_concepts,
            'latex_formulas': self.latex_formulas
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'ConversationSession':
        return cls(
            session_id=data['session_id'],
            user_id=data.get('user_id'),
            created_at=datetime.fromisoformat(data['created_at']),
            last_activity=datetime.fromisoformat(data['last_activity']),
            status=ConversationStatus(data.get('status', 'active')),
            messages=[Message.from_dict(m) for m in data.get('messages', [])],
            metadata=data.get('metadata', {}),
            current_topic=data.get('current_topic'),
            related_concepts=data.get('related_concepts', []),
            latex_formulas=data.get('latex_formulas', [])
        )


class ConversationManager:
    """
    对话管理器
    管理对话会话的生命周期
    """
    
    def __init__(
        self,
        max_sessions_per_user: int = 10,
        session_timeout_minutes: int = 60,
        max_messages_per_session: int = 100
    ):
        self.max_sessions_per_user = max_sessions_per_user
        self.session_timeout = timedelta(minutes=session_timeout_minutes)
        self.max_messages = max_messages_per_session
        
        # 会话存储
        self._sessions: Dict[str, ConversationSession] = {}
        self._user_sessions: Dict[str, List[str]] = {}  # user_id -> session_ids
        
        # 启动清理任务
        self._cleanup_task = None
        self._start_cleanup_task()
    
    def _start_cleanup_task(self):
        """启动定期清理任务"""
        async def cleanup_loop():
            while True:
                await asyncio.sleep(300)  # 每5分钟清理一次
                self._cleanup_expired_sessions()
        
        try:
            self._cleanup_task = asyncio.create_task(cleanup_loop())
        except RuntimeError:
            # 没有事件循环时忽略
            pass
    
    def create_session(
        self,
        user_id: Optional[str] = None,
        system_prompt: Optional[str] = None,
        topic: Optional[str] = None
    ) -> ConversationSession:
        """创建新会话"""
        session_id = f"session_{datetime.now().timestamp()}_{id(self)}"
        
        session = ConversationSession(
            session_id=session_id,
            user_id=user_id,
            current_topic=topic
        )
        
        # 添加系统提示词
        if system_prompt:
            session.add_message('system', system_prompt)
        
        # 存储会话
        self._sessions[session_id] = session
        
        # 更新用户会话列表
        if user_id:
            if user_id not in self._user_sessions:
                self._user_sessions[user_id] = []
            self._user_sessions[user_id].append(session_id)
            
            # 限制用户会话数量
            if len(self._user_sessions[user_id]) > self.max_sessions_per_user:
                oldest_session = self._user_sessions[user_id].pop(0)
                if oldest_session in self._sessions:
                    del self._sessions[oldest_session]
        
        logger.info(f"创建新会话: {session_id} (用户: {user_id})")
        return session
    
    def get_session(self, session_id: str) -> Optional[ConversationSession]:
        """获取会话"""
        session = self._sessions.get(session_id)
        
        if session:
            # 检查是否过期
            if self._is_expired(session):
                session.status = ConversationStatus.EXPIRED
                return None
            
            # 更新活动时间
            session.last_activity = datetime.now()
        
        return session
    
    def add_message(
        self,
        session_id: str,
        role: str,
        content: str,
        **kwargs
    ) -> Optional[Message]:
        """向会话添加消息"""
        session = self.get_session(session_id)
        
        if not session:
            return None
        
        # 检查消息数量限制
        if len(session.messages) >= self.max_messages:
            # 移除最旧的用户/助手消息，保留系统消息
            non_system = [i for i, m in enumerate(session.messages) if m.role != 'system']
            if len(non_system) > 5:  # 至少保留5条
                del session.messages[non_system[0]]
        
        session.add_message(role, content, **kwargs)
        return session.messages[-1]
    
    def update_topic(self, session_id: str, topic: str):
        """更新当前话题"""
        session = self.get_session(session_id)
        if session:
            session.current_topic = topic
    
    def add_related_concepts(self, session_id: str, concepts: List[str]):
        """添加相关概念"""
        session = self.get_session(session_id)
        if session:
            for concept in concepts:
                if concept not in session.related_concepts:
                    session.related_concepts.append(concept)
    
    def end_session(self, session_id: str):
        """结束会话"""
        session = self._sessions.get(session_id)
        
        if session:
            session.status = ConversationStatus.COMPLETED
            
            # 从用户会话列表中移除
            if session.user_id and session.user_id in self._user_sessions:
                if session_id in self._user_sessions[session.user_id]:
                    self._user_sessions[session.user_id].remove(session_id)
            
            logger.info(f"结束会话: {session_id}")
    
    def delete_session(self, session_id: str):
        """删除会话"""
        if session_id in self._sessions:
            session = self._sessions[session_id]
            
            # 从用户会话列表中移除
            if session.user_id and session.user_id in self._user_sessions:
                if session_id in self._user_sessions[session.user_id]:
                    self._user_sessions[session.user_id].remove(session_id)
            
            del self._sessions[session_id]
            logger.info(f"删除会话: {session_id}")
    
    def get_user_sessions(self, user_id: str) -> List[Dict]:
        """获取用户的所有会话"""
        session_ids = self._user_sessions.get(user_id, [])
        sessions = []
        
        for sid in session_ids:
            session = self._sessions.get(sid)
            if session and not self._is_expired(session):
                sessions.append({
                    'session_id': sid,
                    'created_at': session.created_at.isoformat(),
                    'last_activity': session.last_activity.isoformat(),
                    'status': session.status.value,
                    'current_topic': session.current_topic,
                    'message_count': len(session.messages)
                })
        
        return sessions
    
    def _is_expired(self, session: ConversationSession) -> bool:
        """检查会话是否过期"""
        return datetime.now() - session.last_activity > self.session_timeout
    
    def _cleanup_expired_sessions(self):
        """清理过期会话"""
        expired = []
        
        for session_id, session in self._sessions.items():
            if self._is_expired(session):
                expired.append(session_id)
        
        for session_id in expired:
            self.delete_session(session_id)
        
        if expired:
            logger.info(f"清理了 {len(expired)} 个过期会话")
    
    def get_stats(self) -> Dict:
        """获取管理器统计"""
        total_sessions = len(self._sessions)
        active_sessions = sum(
            1 for s in self._sessions.values()
            if s.status == ConversationStatus.ACTIVE
        )
        
        return {
            'total_sessions': total_sessions,
            'active_sessions': active_sessions,
            'unique_users': len(self._user_sessions),
            'total_messages': sum(len(s.messages) for s in self._sessions.values())
        }
    
    def export_session(self, session_id: str) -> Optional[str]:
        """导出会话为JSON"""
        session = self.get_session(session_id)
        if session:
            return json.dumps(session.to_dict(), ensure_ascii=False, indent=2)
        return None


# 全局对话管理器实例
_conversation_manager: Optional[ConversationManager] = None


def get_conversation_manager() -> ConversationManager:
    """获取全局对话管理器实例"""
    global _conversation_manager
    if _conversation_manager is None:
        _conversation_manager = ConversationManager()
    return _conversation_manager
