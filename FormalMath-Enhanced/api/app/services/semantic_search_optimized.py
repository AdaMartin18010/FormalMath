"""
语义搜索服务 - 完整优化版本
整合所有优化组件
"""
import time
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime
import numpy as np

from .embedding_optimized import (
    OptimizedEmbeddingService, 
    get_embedding_service_optimized,
    EmbeddingConfig,
    ModelType
)
from .vector_index_optimized import (
    OptimizedVectorStore,
    get_vector_store_optimized
)
from .formula_search_optimized import (
    FormulaSearchServiceOptimized,
    get_formula_search_service_optimized
)
from .reranker_optimized import (
    OptimizedReranker,
    get_reranker_optimized,
    RerankConfig,
    RerankStrategy
)


@dataclass
class SearchRequest:
    """搜索请求"""
    query: str
    search_type: str = "hybrid"  # 'semantic', 'keyword', 'hybrid', 'formula'
    k: int = 10
    filter_metadata: Dict[str, Any] = None
    rerank: bool = True
    rerank_strategy: str = "hybrid"
    timeout_ms: int = 5000


@dataclass
class SearchResponse:
    """搜索响应"""
    results: List[Dict]
    total: int
    search_type: str
    query_time_ms: float
    rerank_time_ms: float
    facets: Dict[str, Any] = None
    performance_metrics: Dict[str, float] = None


@dataclass
class PerformanceMetrics:
    """性能指标"""
    query_time_ms: float = 0.0
    embedding_time_ms: float = 0.0
    index_search_time_ms: float = 0.0
    rerank_time_ms: float = 0.0
    total_time_ms: float = 0.0
    cache_hit: bool = False
    results_count: int = 0


class OptimizedSemanticSearchService:
    """
    优化的语义搜索服务
    
    特性：
    1. 自动模型选择
    2. 分层向量索引
    3. 查询缓存
    4. 多级重排序
    5. 性能监控
    """
    
    def __init__(
        self,
        embedding_service: OptimizedEmbeddingService = None,
        vector_store: OptimizedVectorStore = None,
        formula_search: FormulaSearchServiceOptimized = None,
        reranker: OptimizedReranker = None,
        persist_dir: str = "./search_index_optimized"
    ):
        self.embedding_service = embedding_service or get_embedding_service_optimized()
        self.vector_store = vector_store or get_vector_store_optimized()
        self.formula_search = formula_search or get_formula_search_service_optimized()
        self.reranker = reranker or get_reranker_optimized()
        self.persist_dir = persist_dir
        
        # 关键词索引
        self.keyword_index: Dict[str, Dict] = {}
        self.inverted_index: Dict[str, set] = {}
        
        # 性能监控
        self.search_history: List[PerformanceMetrics] = []
        self.max_history_size = 1000
    
    # ========== 索引管理 ==========
    
    def index_document(
        self,
        doc_id: str,
        content: str,
        metadata: Dict[str, Any] = None,
        index_formulas: bool = True
    ):
        """索引文档"""
        # 索引到向量存储
        self.vector_store.add_document(doc_id, content, metadata)
        
        # 更新关键词索引
        self._update_keyword_index(doc_id, content, metadata)
        
        # 提取并索引公式
        if index_formulas:
            formulas = self._extract_formulas(content)
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
        # 准备批量数据
        vector_docs = []
        for doc in documents:
            vector_docs.append((
                doc['id'],
                doc['content'],
                doc.get('metadata', {})
            ))
        
        # 批量添加到向量存储
        self.vector_store.add_documents(vector_docs)
        
        # 更新关键词索引
        for doc in documents:
            self._update_keyword_index(
                doc['id'],
                doc['content'],
                doc.get('metadata', {})
            )
        
        # 批量索引公式
        for doc in documents:
            if doc.get('index_formulas', True):
                formulas = self._extract_formulas(doc['content'])
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
    
    def _update_keyword_index(self, doc_id: str, content: str, metadata: Dict):
        """更新关键词索引"""
        # 分词
        terms = self._tokenize(content)
        
        self.keyword_index[doc_id] = {
            'content': content,
            'metadata': metadata,
            'terms': terms
        }
        
        # 更新倒排索引
        for term in set(terms):
            if term not in self.inverted_index:
                self.inverted_index[term] = set()
            self.inverted_index[term].add(doc_id)
    
    def _tokenize(self, text: str) -> List[str]:
        """分词"""
        import re
        text = text.lower()
        
        # 提取LaTeX
        latex_pattern = r'\$[^$]+\$|\\begin\{[^}]+\}.*?\\end\{[^}]+\}|\\[a-zA-Z]+'
        latex_exprs = re.findall(latex_pattern, text, re.DOTALL)
        text_without_latex = re.sub(latex_pattern, ' ', text)
        
        # 分词
        words = re.findall(r'\b\w+\b', text_without_latex)
        
        return words + [expr.lower() for expr in latex_exprs]
    
    def _extract_formulas(self, text: str) -> List[Dict]:
        """从文本中提取公式"""
        import re
        formulas = []
        
        # 内联公式
        inline_pattern = r'\$([^$]+)\$'
        for match in re.finditer(inline_pattern, text):
            formulas.append({
                'type': 'inline',
                'content': match.group(1)
            })
        
        # 显示公式
        display_pattern = r'\$\$([^$]+)\$\$'
        for match in re.finditer(display_pattern, text):
            formulas.append({
                'type': 'display',
                'content': match.group(1)
            })
        
        # 环境公式
        env_pattern = r'\\begin\{(equation|align|align\*|gather)\}(.*?)\\end\{\1\}'
        for match in re.finditer(env_pattern, text, re.DOTALL):
            formulas.append({
                'type': match.group(1),
                'content': match.group(2)
            })
        
        return formulas
    
    def delete_document(self, doc_id: str):
        """删除文档"""
        self.vector_store.delete_document(doc_id)
        
        if doc_id in self.keyword_index:
            for term in self.keyword_index[doc_id]['terms']:
                if term in self.inverted_index:
                    self.inverted_index[term].discard(doc_id)
            del self.keyword_index[doc_id]
    
    def save_index(self):
        """保存索引"""
        self.vector_store.save()
    
    # ========== 搜索功能 ==========
    
    def search(self, request: SearchRequest) -> SearchResponse:
        """
        执行搜索
        
        完整的搜索流程：
        1. 查询分析和预处理
        2. 选择合适的搜索策略
        3. 执行搜索
        4. 重排序
        5. 返回结果和指标
        """
        start_time = time.time()
        metrics = PerformanceMetrics()
        
        # 自动选择模型
        auto_model_start = time.time()
        optimal_model = self.embedding_service.auto_select_model(request.query)
        if optimal_model != self.embedding_service.current_model_type:
            self.embedding_service.switch_model(optimal_model)
        metrics.embedding_time_ms = (time.time() - auto_model_start) * 1000
        
        # 执行搜索
        search_start = time.time()
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
        
        metrics.index_search_time_ms = (time.time() - search_start) * 1000
        
        # 重排序
        rerank_start = time.time()
        if request.rerank and results:
            strategy_map = {
                "cross_encoder": RerankStrategy.CROSS_ENCODER,
                "rrf": RerankStrategy.RECIPROCAL_RANK_FUSION,
                "mmr": RerankStrategy.MMR,
                "diversity": RerankStrategy.DIVERSITY_AWARE,
                "formula": RerankStrategy.FORMULA_AWARE,
                "hybrid": RerankStrategy.HYBRID
            }
            strategy = strategy_map.get(request.rerank_strategy, RerankStrategy.HYBRID)
            
            rerank_results = self.reranker.rerank(
                request.query,
                [self._to_dict(r) for r in results],
                strategy=strategy
            )
            results = [self._from_rerank_result(r) for r in rerank_results]
        
        metrics.rerank_time_ms = (time.time() - rerank_start) * 1000
        
        # 计算总时间
        total_time = (time.time() - start_time) * 1000
        metrics.total_time_ms = total_time
        metrics.query_time_ms = total_time
        metrics.results_count = len(results)
        
        # 记录性能指标
        self.search_history.append(metrics)
        if len(self.search_history) > self.max_history_size:
            self.search_history = self.search_history[-self.max_history_size:]
        
        # 构建facets
        facets = self._compute_facets(results)
        
        return SearchResponse(
            results=[self._result_to_dict(r) for r in results[:request.k]],
            total=len(results),
            search_type=request.search_type,
            query_time_ms=metrics.index_search_time_ms,
            rerank_time_ms=metrics.rerank_time_ms,
            facets=facets,
            performance_metrics={
                'total_time_ms': metrics.total_time_ms,
                'embedding_time_ms': metrics.embedding_time_ms,
                'index_search_time_ms': metrics.index_search_time_ms,
                'rerank_time_ms': metrics.rerank_time_ms
            }
        )
    
    def _semantic_search(self, request: SearchRequest) -> List[Any]:
        """语义搜索"""
        vector_results = self.vector_store.search(
            request.query,
            k=request.k * 2,
            filter_metadata=request.filter_metadata
        )
        
        return [
            self._to_hybrid_result(r, 'semantic')
            for r in vector_results
        ]
    
    def _keyword_search(self, request: SearchRequest) -> List[Any]:
        """关键词搜索"""
        query_terms = self._tokenize(request.query)
        
        if not query_terms:
            return []
        
        # 计算BM25分数
        scores = self._bm25_search(query_terms)
        
        # 获取top_k
        sorted_results = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        
        results = []
        for doc_id, score in sorted_results[:request.k * 2]:
            doc_info = self.keyword_index.get(doc_id, {})
            results.append(self._to_hybrid_result_from_keyword(
                doc_id, doc_info, score
            ))
        
        return results
    
    def _bm25_search(self, query_terms: List[str]) -> Dict[str, float]:
        """BM25搜索"""
        k1, b = 1.5, 0.75
        
        # 计算平均文档长度
        avg_doc_len = np.mean([
            len(doc['terms']) for doc in self.keyword_index.values()
        ]) if self.keyword_index else 0
        
        scores = {}
        N = len(self.keyword_index)
        
        for term in query_terms:
            n_q = len(self.inverted_index.get(term, set()))
            if n_q == 0:
                continue
            
            idf = np.log((N - n_q + 0.5) / (n_q + 0.5) + 1)
            
            for doc_id in self.inverted_index.get(term, set()):
                doc = self.keyword_index[doc_id]
                doc_len = len(doc['terms'])
                f_qd = doc['terms'].count(term)
                
                tf_component = (f_qd * (k1 + 1)) / (f_qd + k1 * (1 - b + b * doc_len / avg_doc_len))
                score = idf * tf_component
                
                scores[doc_id] = scores.get(doc_id, 0) + score
        
        return scores
    
    def _hybrid_search(self, request: SearchRequest) -> List[Any]:
        """混合搜索"""
        # 并行执行语义和关键词搜索
        semantic_results = self.vector_store.search(
            request.query,
            k=request.k * 3,
            filter_metadata=request.filter_metadata
        )
        
        keyword_results = self._keyword_search(request)
        
        # 合并结果
        return self._merge_results(semantic_results, keyword_results)
    
    def _formula_search(self, request: SearchRequest) -> List[Any]:
        """公式搜索"""
        formula_results = self.formula_search.search(
            request.query,
            k=request.k
        )
        
        results = []
        for fr in formula_results:
            results.append({
                'id': fr.formula_id,
                'content': fr.formula_latex,
                'semantic_score': fr.similarity,
                'keyword_score': fr.similarity,
                'combined_score': fr.similarity,
                'metadata': {
                    'formula_match_type': fr.match_type,
                    'matched_variables': fr.matched_vars
                },
                'match_type': 'formula'
            })
        
        return results
    
    def _merge_results(
        self,
        semantic_results: List[Any],
        keyword_results: List[Any]
    ) -> List[Any]:
        """合并语义和关键词搜索结果"""
        result_dict = {}
        
        # 处理语义结果
        max_semantic = max([r.score for r in semantic_results]) if semantic_results else 1.0
        for r in semantic_results:
            normalized_score = r.score / max_semantic if max_semantic > 0 else 0
            result_dict[r.document.id] = {
                'id': r.document.id,
                'content': r.document.content,
                'semantic_score': normalized_score,
                'keyword_score': 0.0,
                'combined_score': normalized_score * 0.6,
                'metadata': r.document.metadata,
                'match_type': 'semantic'
            }
        
        # 处理关键词结果
        max_keyword = max([r['combined_score'] for r in keyword_results]) if keyword_results else 1.0
        for r in keyword_results:
            normalized_score = r['combined_score'] / max_keyword if max_keyword > 0 else 0
            
            if r['id'] in result_dict:
                result_dict[r['id']]['keyword_score'] = normalized_score
                result_dict[r['id']]['combined_score'] += normalized_score * 0.4
                result_dict[r['id']]['match_type'] = 'both'
            else:
                result_dict[r['id']] = {
                    'id': r['id'],
                    'content': r['content'],
                    'semantic_score': 0.0,
                    'keyword_score': normalized_score,
                    'combined_score': normalized_score * 0.4,
                    'metadata': r['metadata'],
                    'match_type': 'keyword'
                }
        
        # 转换为列表并排序
        results = list(result_dict.values())
        results.sort(key=lambda x: x['combined_score'], reverse=True)
        
        return results
    
    def _to_hybrid_result(self, search_result, match_type: str):
        """转换为混合结果格式"""
        return {
            'id': search_result.document.id,
            'content': search_result.document.content,
            'semantic_score': search_result.score if match_type == 'semantic' else 0.0,
            'keyword_score': 0.0,
            'combined_score': search_result.score,
            'metadata': search_result.document.metadata,
            'match_type': match_type
        }
    
    def _to_hybrid_result_from_keyword(self, doc_id: str, doc_info: Dict, score: float):
        """从关键词结果转换为混合结果格式"""
        return {
            'id': doc_id,
            'content': doc_info.get('content', ''),
            'semantic_score': 0.0,
            'keyword_score': score,
            'combined_score': score,
            'metadata': doc_info.get('metadata', {}),
            'match_type': 'keyword'
        }
    
    def _to_dict(self, result: Dict) -> Dict:
        """转换为字典"""
        return result
    
    def _from_rerank_result(self, rr) -> Dict:
        """从重排序结果转换"""
        return {
            'id': rr.id,
            'content': rr.content,
            'semantic_score': rr.semantic_score,
            'keyword_score': rr.keyword_score,
            'combined_score': rr.rerank_score,
            'metadata': rr.metadata,
            'match_type': 'reranked',
            'explanation': rr.explanation
        }
    
    def _result_to_dict(self, result: Dict) -> Dict:
        """转换为输出字典"""
        return {
            'id': result['id'],
            'content': result['content'][:500] + '...' if len(result['content']) > 500 else result['content'],
            'semantic_score': round(result.get('semantic_score', 0), 4),
            'keyword_score': round(result.get('keyword_score', 0), 4),
            'combined_score': round(result.get('combined_score', 0), 4),
            'metadata': result.get('metadata', {}),
            'match_type': result.get('match_type', 'unknown'),
            'explanation': result.get('explanation', '')
        }
    
    def _compute_facets(self, results: List[Dict]) -> Dict[str, Any]:
        """计算聚合信息"""
        facets = {
            'match_types': {},
            'metadata_keys': set(),
            'avg_score': 0.0
        }
        
        total_score = 0.0
        for r in results:
            match_type = r.get('match_type', 'unknown')
            facets['match_types'][match_type] = facets['match_types'].get(match_type, 0) + 1
            facets['metadata_keys'].update(r.get('metadata', {}).keys())
            total_score += r.get('combined_score', 0)
        
        if results:
            facets['avg_score'] = round(total_score / len(results), 4)
        
        facets['metadata_keys'] = list(facets['metadata_keys'])
        
        return facets
    
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
        recent_metrics = self.search_history[-100:] if self.search_history else []
        
        return {
            'vector_store': self.vector_store.get_stats(),
            'embedding_service': self.embedding_service.get_performance_stats(),
            'reranker': self.reranker.get_stats(),
            'indexed_documents': len(self.vector_store.documents),
            'indexed_formulas': len(self.formula_search.structure_index.formulas),
            'search_history': {
                'total_searches': len(self.search_history),
                'avg_query_time_ms': np.mean([m.total_time_ms for m in recent_metrics]) if recent_metrics else 0,
                'p95_query_time_ms': np.percentile([m.total_time_ms for m in recent_metrics], 95) if recent_metrics else 0,
            }
        }


# 全局实例
_semantic_search_service_optimized: Optional[OptimizedSemanticSearchService] = None


def get_semantic_search_service_optimized() -> OptimizedSemanticSearchService:
    """获取全局优化的语义搜索服务实例"""
    global _semantic_search_service_optimized
    if _semantic_search_service_optimized is None:
        _semantic_search_service_optimized = OptimizedSemanticSearchService()
    return _semantic_search_service_optimized
