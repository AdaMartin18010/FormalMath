"""
AI助手服务模块
"""
from .ai_assistant import AIAssistantService, get_ai_assistant
from .conversation_manager import ConversationManager, get_conversation_manager

__all__ = [
    'AIAssistantService',
    'get_ai_assistant',
    'ConversationManager',
    'get_conversation_manager',
]
