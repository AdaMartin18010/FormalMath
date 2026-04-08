"""
知识库服务
集成语义搜索、知识图谱和概念关系
"""
import os
import sys
import json
import logging
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, field
from pathlib import Path

# 将api目录添加到路径以导入现有服务
api_path = Path(__file__).parent.parent.parent.parent.parent / "api"
if str(api_path) not in sys.path:
    sys.path.insert(0, str(api_path))

# 尝试导入现有服务
try:
    from app.services.semantic_search_service import get_semantic_search_service, SearchRequest
    from app.services.qa_system import get_qa_system, Answer
    SEMANTIC_SEARCH_AVAILABLE = True
except ImportError as e:
    SEMANTIC_SEARCH_AVAILABLE = False
    logging.warning(f"语义搜索服务不可用: {e}")

try:
    from app.ml.learning_engine import LearningEngine, get_learning_engine
    LEARNING_ENGINE_AVAILABLE = True
except ImportError as e:
    LEARNING_ENGINE_AVAILABLE = False
    logging.warning(f"学习引擎不可用: {e}")

logger = logging.getLogger(__name__)


@dataclass
class ConceptInfo:
    """概念信息"""
    id: str
    name: str
    name_en: str = ""
    definition: str = ""
    properties: List[str] = field(default_factory=list)
    related_concepts: List[str] = field(default_factory=list)
    prerequisites: List[str] = field(default_factory=list)
    theorems: List[str] = field(default_factory=list)
    examples: List[str] = field(default_factory=list)
    msc_code: str = ""
    difficulty: str = "intermediate"


@dataclass
class SearchResult:
    """搜索结果"""
    content: str
    source: str
    score: float
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class KnowledgeContext:
    """知识上下文"""
    query: str
    concepts: List[ConceptInfo] = field(default_factory=list)
    documents: List[SearchResult] = field(default_factory=list)
    related_formulas: List[str] = field(default_factory=list)
    theorems: List[str] = field(default_factory=list)
    learning_path: List[str] = field(default_factory=list)


class KnowledgeService:
    """
    知识库服务
    整合语义搜索、知识图谱和概念信息
    """
    
    def __init__(self):
        self.semantic_search = None
        self.qa_system = None
        self.learning_engine = None
        
        self._init_services()
        
        # 概念缓存
        self._concept_cache: Dict[str, ConceptInfo] = {}
        
        # 知识图谱数据（从文件加载）
        self._knowledge_graph: Dict[str, Any] = {}
        self._load_knowledge_graph()
    
    def _init_services(self):
        """初始化现有服务"""
        if SEMANTIC_SEARCH_AVAILABLE:
            try:
                self.semantic_search = get_semantic_search_service()
                self.qa_system = get_qa_system()
                logger.info("语义搜索服务初始化成功")
            except Exception as e:
                logger.warning(f"语义搜索服务初始化失败: {e}")
        
        if LEARNING_ENGINE_AVAILABLE:
            try:
                self.learning_engine = get_learning_engine()
                logger.info("学习引擎初始化成功")
            except Exception as e:
                logger.warning(f"学习引擎初始化失败: {e}")
    
    def _load_knowledge_graph(self):
        """加载知识图谱数据"""
        # 尝试从多个位置加载
        possible_paths = [
            Path(__file__).parent.parent.parent.parent.parent.parent / "math_data.json",
            Path(__file__).parent.parent.parent.parent.parent / "app" / "data" / "knowledge_graph.json",
        ]
        
        for path in possible_paths:
            if path.exists():
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        self._knowledge_graph = json.load(f)
                    logger.info(f"知识图谱加载成功: {path}")
                    break
                except Exception as e:
                    logger.warning(f"无法加载知识图谱: {e}")
    
    def search_concepts(
        self,
        query: str,
        k: int = 5,
        search_type: str = "hybrid"
    ) -> List[SearchResult]:
        """
        搜索相关概念
        
        Args:
            query: 搜索查询
            k: 返回结果数量
            search_type: 搜索类型 (semantic/keyword/hybrid)
        """
        results = []
        
        if self.semantic_search:
            try:
                request = SearchRequest(
                    query=query,
                    search_type=search_type,
                    k=k,
                    rerank=True
                )
                response = self.semantic_search.search(request)
                
                for r in response.results:
                    results.append(SearchResult(
                        content=r.get('content', ''),
                        source=r.get('metadata', {}).get('source', 'unknown'),
                        score=r.get('combined_score', 0.0),
                        metadata=r.get('metadata', {})
                    ))
            except Exception as e:
                logger.error(f"语义搜索失败: {e}")
        
        # 如果语义搜索不可用或失败，使用简单关键词搜索
        if not results and self._knowledge_graph:
            results = self._simple_keyword_search(query, k)
        
        return results
    
    def _simple_keyword_search(self, query: str, k: int) -> List[SearchResult]:
        """简单的关键词搜索（后备方案）"""
        results = []
        query_lower = query.lower()
        
        # 在知识图谱中搜索
        concepts = self._knowledge_graph.get('concepts', [])
        for concept in concepts:
            name = concept.get('name', '')
            definition = concept.get('definition', '')
            
            # 简单匹配
            score = 0.0
            if query_lower in name.lower():
                score += 0.5
            if query_lower in definition.lower():
                score += 0.3
            
            if score > 0:
                results.append(SearchResult(
                    content=f"{name}: {definition[:200]}...",
                    source=concept.get('id', 'unknown'),
                    score=score,
                    metadata=concept
                ))
        
        # 按分数排序并限制数量
        results.sort(key=lambda x: x.score, reverse=True)
        return results[:k]
    
    def get_concept_info(self, concept_id: str) -> Optional[ConceptInfo]:
        """获取概念详细信息"""
        # 检查缓存
        if concept_id in self._concept_cache:
            return self._concept_cache[concept_id]
        
        # 从知识图谱查找
        if self._knowledge_graph:
            concepts = self._knowledge_graph.get('concepts', [])
            for concept in concepts:
                if concept.get('id') == concept_id or concept.get('name') == concept_id:
                    info = ConceptInfo(
                        id=concept.get('id', concept_id),
                        name=concept.get('name', concept_id),
                        name_en=concept.get('name_en', ''),
                        definition=concept.get('definition', ''),
                        properties=concept.get('properties', []),
                        related_concepts=concept.get('related', []),
                        prerequisites=concept.get('prerequisites', []),
                        theorems=concept.get('theorems', []),
                        examples=concept.get('examples', []),
                        msc_code=concept.get('msc', ''),
                        difficulty=concept.get('difficulty', 'intermediate')
                    )
                    self._concept_cache[concept_id] = info
                    return info
        
        return None
    
    def get_related_concepts(self, concept_id: str) -> List[str]:
        """获取相关概念"""
        info = self.get_concept_info(concept_id)
        if info:
            return info.related_concepts
        return []
    
    def get_prerequisites(self, concept_id: str) -> List[str]:
        """获取先修概念"""
        info = self.get_concept_info(concept_id)
        if info:
            return info.prerequisites
        return []
    
    def get_learning_path(self, concept_id: str) -> List[str]:
        """获取学习路径"""
        path = []
        visited = set()
        
        def dfs(current_id: str):
            if current_id in visited:
                return
            visited.add(current_id)
            
            # 先添加先修
            prereqs = self.get_prerequisites(current_id)
            for prereq in prereqs:
                dfs(prereq)
            
            path.append(current_id)
        
        dfs(concept_id)
        return path
    
    def ask_question(self, question: str) -> Optional[Answer]:
        """使用QA系统回答问题"""
        if self.qa_system:
            try:
                return self.qa_system.ask(question)
            except Exception as e:
                logger.error(f"QA系统调用失败: {e}")
        return None
    
    def build_knowledge_context(
        self,
        query: str,
        include_learning_path: bool = True
    ) -> KnowledgeContext:
        """
        构建完整的知识上下文
        
        Args:
            query: 用户查询
            include_learning_path: 是否包含学习路径
        """
        context = KnowledgeContext(query=query)
        
        # 1. 搜索相关文档
        search_results = self.search_concepts(query, k=5)
        context.documents = search_results
        
        # 2. 提取概念
        concept_ids = set()
        for result in search_results:
            metadata = result.metadata
            if 'concept_id' in metadata:
                concept_ids.add(metadata['concept_id'])
            if 'concepts' in metadata:
                concept_ids.update(metadata['concepts'])
        
        # 3. 获取概念详细信息
        for concept_id in concept_ids:
            info = self.get_concept_info(concept_id)
            if info:
                context.concepts.append(info)
        
        # 4. 提取公式
        context.related_formulas = self._extract_formulas(search_results)
        
        # 5. 收集定理
        for concept in context.concepts:
            context.theorems.extend(concept.theorems)
        
        # 6. 构建学习路径
        if include_learning_path and context.concepts:
            main_concept = context.concepts[0].id
            context.learning_path = self.get_learning_path(main_concept)
        
        return context
    
    def _extract_formulas(self, results: List[SearchResult]) -> List[str]:
        """从搜索结果中提取公式"""
        import re
        
        formulas = []
        pattern = r'\$[^$]+\$|\$\$[^$]+\$\$'
        
        for result in results:
            matches = re.findall(pattern, result.content)
            formulas.extend(matches)
        
        return list(set(formulas))[:10]  # 去重并限制数量
    
    def suggest_questions(self, topic: str, k: int = 5) -> List[str]:
        """获取建议问题"""
        if self.qa_system:
            try:
                return self.qa_system.get_suggested_questions(topic, k)
            except Exception as e:
                logger.error(f"获取建议问题失败: {e}")
        
        # 后备方案
        return [
            f"什么是{topic}？",
            f"{topic}的定义是什么？",
            f"{topic}有哪些重要性质？",
            f"{topic}的应用有哪些？",
            f"如何证明与{topic}相关的定理？"
        ]
    
    def get_diagnosis_context(self, user_id: str) -> Dict[str, Any]:
        """获取用户认知诊断上下文"""
        context = {
            'knowledge_level': 'intermediate',
            'weak_areas': [],
            'strong_areas': [],
            'learning_style': 'visual'
        }
        
        if self.learning_engine:
            try:
                # 这里可以调用学习引擎获取用户画像
                pass
            except Exception as e:
                logger.warning(f"获取诊断上下文失败: {e}")
        
        return context


# 全局知识服务实例
_knowledge_service: Optional[KnowledgeService] = None


def get_knowledge_service() -> KnowledgeService:
    """获取全局知识服务实例"""
    global _knowledge_service
    if _knowledge_service is None:
        _knowledge_service = KnowledgeService()
    return _knowledge_service
