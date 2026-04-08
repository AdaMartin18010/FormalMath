"""
知识库集成模块
与现有知识图谱和语义搜索服务集成
"""
from .knowledge_service import KnowledgeService, get_knowledge_service
from .context_builder import ContextBuilder, get_context_builder

__all__ = [
    'KnowledgeService',
    'get_knowledge_service',
    'ContextBuilder',
    'get_context_builder',
]
