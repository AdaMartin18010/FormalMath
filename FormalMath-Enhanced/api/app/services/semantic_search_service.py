"""
语义搜索服务整合
整合所有搜索功能的主服务
"""
from typing import List, Dict, Optional, Any
from dataclasses import dataclass
import os
import json

from .embedding import EmbeddingService, get_embedding_service, EmbeddingConfig
from .vector_store import VectorStore, get_vector_store
from .hybrid_search import HybridSearchService, get_hybrid_search_service, HybridSearchResult
from .formula_search import FormulaSearchService, get_formula_search_service, FormulaMatchResult
from .qa_system import QASystem, get_qa_system, Answer


@dataclass
class SearchRequest:
    """搜索请求"""
    query: str
    search_type: str = "hybrid"  # 'semantic', 'keyword', 'hybrid', 'formula'
    k: int = 10
    filter_metadata: Dict[str, Any] = None
    rerank: bool = True


@dataclass
class SearchResponse:
    """搜索响应"""
    results: List[Dict]
    total: int
    search_type: str
    query_time_ms: float
    facets: Dict[str, Any] = None


class SemanticSearchService:
    """语义搜索主服务"""
    
    def __init__(
        self,
        embedding_service: EmbeddingService = None,
        vector_store: VectorStore = None,
        hybrid_search: HybridSearchService = None,
        formula_search: FormulaSearchService = None,
        qa_system: QASystem = None,
        persist_dir: str = "./search_index"
    ):
        self.embedding_service = embedding_service or get_embedding_service()
        self.vector_store = vector_store or get_vector_store()
        self.hybrid_search = hybrid_search or get_hybrid_search_service()
        self.formula_search = formula_search or get_formula_search_service()
        self.qa_system = qa_system or get_qa_system()
        self.persist_dir = persist_dir
        
        os.makedirs(persist_dir, exist_ok=True)
    
    # ========== 索引管理 ==========
    
    def index_document(
        self,
        doc_id: str,
        content: str,
        metadata: Dict[str, Any] = None,
        index_formulas: bool = True
    ):
        """索引文档"""
        # 索引到混合搜索
        self.hybrid_search.index_document(doc_id, content, metadata)
        
        # 提取并索引公式
        if index_formulas:
            formulas = self.formula_search.extract_formula_from_text(content)
            for i, formula in enumerate(formulas):
                formula_id = f"{doc_id}_formula_{i}"
                self.formula_search.index_formula(
                    formula_id,
                    formula['content'],
                    metadata={
                        'source_doc': doc_id,
                        'formula_type': formula['type'],
                        **(metadata or {})
                    }
                )
    
    def index_documents(
        self,
        documents: List[Dict[str, Any]]
    ):
        """批量索引文档"""
        # 准备数据
        hybrid_docs = []
        for doc in documents:
            hybrid_docs.append((
                doc['id'],
                doc['content'],
                doc.get('metadata', {})
            ))
        
        # 索引到混合搜索
        self.hybrid_search.index_documents(hybrid_docs)
        
        # 索引公式
        for doc in documents:
            if doc.get('index_formulas', True):
                formulas = self.formula_search.extract_formula_from_text(doc['content'])
                for i, formula in enumerate(formulas):
                    formula_id = f"{doc['id']}_formula_{i}"
                    self.formula_search.index_formula(
                        formula_id,
                        formula['content'],
                        metadata={
                            'source_doc': doc['id'],
                            'formula_type': formula['type'],
                            **doc.get('metadata', {})
                        }
                    )
    
    def delete_document(self, doc_id: str):
        """删除文档"""
        self.hybrid_search.delete_document(doc_id)
        # 注意：相关公式不会自动删除，需要额外处理
    
    def save_index(self):
        """保存索引"""
        self.vector_store.save()
    
    # ========== 搜索功能 ==========
    
    def search(self, request: SearchRequest) -> SearchResponse:
        """执行搜索"""
        import time
        start_time = time.time()
        
        if request.search_type == "semantic":
            results = self._semantic_search(request)
        elif request.search_type == "keyword":
            results = self._keyword_search(request)
        elif request.search_type == "hybrid":
            results = self._hybrid_search(request)
        elif request.search_type == "formula":
            results = self._formula_search(request)
        else:
            results = self._hybrid_search(request)
        
        query_time = (time.time() - start_time) * 1000
        
        # 构建facets
        facets = self._compute_facets(results)
        
        return SearchResponse(
            results=[self._result_to_dict(r) for r in results],
            total=len(results),
            search_type=request.search_type,
            query_time_ms=query_time,
            facets=facets
        )
    
    def _semantic_search(self, request: SearchRequest) -> List[HybridSearchResult]:
        """语义搜索"""
        vector_results = self.vector_store.search(
            request.query,
            k=request.k,
            filter_metadata=request.filter_metadata
        )
        
        # 转换为HybridSearchResult格式
        return [
            HybridSearchResult(
                id=r.document.id,
                content=r.document.content,
                semantic_score=r.score,
                keyword_score=0.0,
                combined_score=r.score,
                metadata=r.document.metadata,
                rank=i,
                match_type='semantic'
            )
            for i, r in enumerate(vector_results, 1)
        ]
    
    def _keyword_search(self, request: SearchRequest) -> List[HybridSearchResult]:
        """关键词搜索"""
        keyword_results = self.hybrid_search.keyword_searcher.search(
            request.query,
            k=request.k
        )
        
        return [
            HybridSearchResult(
                id=doc_id,
                content=self.hybrid_search.get_document(doc_id).get('content', ''),
                semantic_score=0.0,
                keyword_score=score,
                combined_score=score,
                metadata=self.hybrid_search.get_document(doc_id).get('metadata', {}),
                rank=i,
                match_type='keyword'
            )
            for i, (doc_id, score) in enumerate(keyword_results, 1)
        ]
    
    def _hybrid_search(self, request: SearchRequest) -> List[HybridSearchResult]:
        """混合搜索"""
        return self.hybrid_search.search(
            query=request.query,
            k=request.k,
            rerank=request.rerank,
            filter_metadata=request.filter_metadata
        )
    
    def _formula_search(self, request: SearchRequest) -> List[HybridSearchResult]:
        """公式搜索"""
        formula_results = self.formula_search.search(
            request.query,
            k=request.k
        )
        
        # 获取源文档
        results = []
        for i, fr in enumerate(formula_results, 1):
            doc_info = self.formula_search.structure_index.get_formula(fr.formula_id)
            source_doc_id = doc_info.get('metadata', {}).get('source_doc', '') if doc_info else ''
            
            results.append(HybridSearchResult(
                id=fr.formula_id,
                content=fr.formula_latex,
                semantic_score=fr.similarity,
                keyword_score=fr.similarity,
                combined_score=fr.similarity,
                metadata={
                    'formula_match_type': fr.match_type,
                    'matched_variables': fr.matched_vars,
                    'source_document': source_doc_id
                },
                rank=i,
                match_type='formula'
            ))
        
        return results
    
    def _result_to_dict(self, result: HybridSearchResult) -> Dict:
        """转换结果为字典"""
        return {
            'id': result.id,
            'content': result.content[:500] + '...' if len(result.content) > 500 else result.content,
            'semantic_score': round(result.semantic_score, 4),
            'keyword_score': round(result.keyword_score, 4),
            'combined_score': round(result.combined_score, 4),
            'metadata': result.metadata,
            'rank': result.rank,
            'match_type': result.match_type
        }
    
    def _compute_facets(self, results: List[HybridSearchResult]) -> Dict[str, Any]:
        """计算聚合信息"""
        facets = {
            'match_types': {},
            'metadata_keys': set()
        }
        
        for r in results:
            # 统计匹配类型
            facets['match_types'][r.match_type] = facets['match_types'].get(r.match_type, 0) + 1
            
            # 收集元数据键
            facets['metadata_keys'].update(r.metadata.keys())
        
        facets['metadata_keys'] = list(facets['metadata_keys'])
        
        return facets
    
    # ========== 问答功能 ==========
    
    def ask(self, question: str, use_multi_hop: bool = True) -> Dict:
        """问答"""
        answer = self.qa_system.ask(question, use_multi_hop=use_multi_hop)
        
        return {
            'answer': answer.text,
            'confidence': round(answer.confidence, 4),
            'answer_type': answer.answer_type,
            'sources': answer.sources,
            'reasoning_chain': answer.reasoning_chain
        }
    
    def suggest_questions(self, topic: str, k: int = 5) -> List[str]:
        """获取建议问题"""
        return self.qa_system.get_suggested_questions(topic, k)
    
    # ========== 公式相关 ==========
    
    def search_formula(
        self,
        latex: str,
        k: int = 10,
        match_type: str = 'all'
    ) -> List[Dict]:
        """搜索公式"""
        results = self.formula_search.search(latex, k=k, match_type=match_type)
        
        return [
            {
                'formula_id': r.formula_id,
                'latex': r.formula_latex,
                'similarity': round(r.similarity, 4),
                'match_type': r.match_type,
                'variable_mapping': r.matched_vars,
                'rank': r.rank
            }
            for r in results
        ]
    
    def compare_formulas(self, latex1: str, latex2: str) -> Dict:
        """比较两个公式"""
        return self.formula_search.compare_formulas(latex1, latex2)
    
    # ========== 统计信息 ==========
    
    def get_stats(self) -> Dict:
        """获取搜索系统统计信息"""
        return {
            'vector_store': self.vector_store.get_stats(),
            'embedding_model': self.embedding_service.config.model_name if hasattr(self.embedding_service, 'config') else 'default',
            'indexed_documents': len(self.vector_store.documents),
            'indexed_formulas': len(self.formula_search.structure_index.formulas)
        }


# 全局语义搜索服务实例
_semantic_search_service: Optional[SemanticSearchService] = None


def get_semantic_search_service() -> SemanticSearchService:
    """获取全局语义搜索服务实例"""
    global _semantic_search_service
    if _semantic_search_service is None:
        _semantic_search_service = SemanticSearchService()
    return _semantic_search_service
