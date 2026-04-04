"""
混合搜索服务
结合关键词搜索和语义搜索，支持结果重排序和相关性评分
"""
import re
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass
from datetime import datetime
import numpy as np

from .vector_store import VectorStore, get_vector_store, SearchResult
from .embedding import EmbeddingService, get_embedding_service


@dataclass
class HybridSearchResult:
    """混合搜索结果"""
    id: str
    content: str
    semantic_score: float
    keyword_score: float
    combined_score: float
    metadata: Dict[str, Any]
    rank: int
    match_type: str  # 'semantic', 'keyword', 'both'


class KeywordSearcher:
    """关键词搜索器"""
    
    def __init__(self):
        self.documents: Dict[str, Dict] = {}
        self.inverted_index: Dict[str, set] = {}
    
    def add_document(self, doc_id: str, content: str, metadata: Dict = None):
        """添加文档到索引"""
        self.documents[doc_id] = {
            'content': content,
            'metadata': metadata or {},
            'terms': self._tokenize(content)
        }
        
        # 更新倒排索引
        for term in self.documents[doc_id]['terms']:
            if term not in self.inverted_index:
                self.inverted_index[term] = set()
            self.inverted_index[term].add(doc_id)
    
    def search(
        self,
        query: str,
        k: int = 10,
        exact_match: bool = False
    ) -> List[Tuple[str, float]]:
        """关键词搜索"""
        query_terms = self._tokenize(query)
        
        if not query_terms:
            return []
        
        # 计算BM25分数
        scores = self._bm25_search(query_terms, exact_match)
        
        # 排序并返回前k个
        sorted_results = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        return sorted_results[:k]
    
    def _bm25_search(
        self,
        query_terms: List[str],
        exact_match: bool = False
    ) -> Dict[str, float]:
        """BM25评分算法"""
        k1 = 1.5  # 词频饱和参数
        b = 0.75  # 长度归一化参数
        
        # 计算平均文档长度
        avg_doc_len = np.mean([
            len(doc['terms']) 
            for doc in self.documents.values()
        ]) if self.documents else 0
        
        scores = {}
        N = len(self.documents)
        
        for term in query_terms:
            # 包含该词的文档数
            n_q = len(self.inverted_index.get(term, set()))
            if n_q == 0:
                continue
            
            # IDF计算
            idf = np.log((N - n_q + 0.5) / (n_q + 0.5) + 1)
            
            for doc_id in self.inverted_index.get(term, set()):
                doc = self.documents[doc_id]
                doc_len = len(doc['terms'])
                
                # 词频
                f_qd = doc['terms'].count(term)
                
                if exact_match:
                    # 精确匹配要求词频等于查询中的次数
                    query_tf = query_terms.count(term)
                    if f_qd < query_tf:
                        continue
                
                # BM25公式
                tf_component = (f_qd * (k1 + 1)) / (f_qd + k1 * (1 - b + b * doc_len / avg_doc_len))
                score = idf * tf_component
                
                scores[doc_id] = scores.get(doc_id, 0) + score
        
        return scores
    
    def _tokenize(self, text: str) -> List[str]:
        """分词"""
        # 转换为小写
        text = text.lower()
        
        # 提取LaTeX表达式
        latex_pattern = r'\$[^$]+\$|\\begin\{[^}]+\}.*?\\end\{[^}]+\}|\\[a-zA-Z]+'
        latex_exprs = re.findall(latex_pattern, text, re.DOTALL)
        
        # 移除LaTeX，处理剩余文本
        text_without_latex = re.sub(latex_pattern, ' ', text)
        
        # 分词
        words = re.findall(r'\b\w+\b', text_without_latex)
        
        # 合并结果
        tokens = words + [expr.lower() for expr in latex_exprs]
        
        return tokens
    
    def remove_document(self, doc_id: str):
        """删除文档"""
        if doc_id not in self.documents:
            return
        
        doc = self.documents[doc_id]
        for term in doc['terms']:
            if term in self.inverted_index:
                self.inverted_index[term].discard(doc_id)
        
        del self.documents[doc_id]


class Reranker:
    """结果重排序器"""
    
    def __init__(self, embedding_service: EmbeddingService = None):
        self.embedding_service = embedding_service or get_embedding_service()
    
    def rerank(
        self,
        query: str,
        results: List[HybridSearchResult],
        method: str = "cross_encoder"
    ) -> List[HybridSearchResult]:
        """重排序结果"""
        if not results:
            return results
        
        if method == "cross_encoder":
            return self._cross_encoder_rerank(query, results)
        elif method == "reciprocal_rank_fusion":
            return self._rrf_rerank(results)
        elif method == "semantic_boost":
            return self._semantic_boost_rerank(query, results)
        else:
            return sorted(results, key=lambda x: x.combined_score, reverse=True)
    
    def _cross_encoder_rerank(
        self,
        query: str,
        results: List[HybridSearchResult]
    ) -> List[HybridSearchResult]:
        """
        使用交叉编码器重排序
        由于没有真正的cross-encoder模型，使用语义相似度作为近似
        """
        query_embedding = self.embedding_service.embed_math_content(query)
        
        for result in results:
            content_embedding = self.embedding_service.embed_math_content(result.content)
            cross_score = self.embedding_service.compute_similarity(
                query_embedding, content_embedding
            )
            # 结合原始分数和交叉分数
            result.combined_score = result.combined_score * 0.3 + cross_score * 0.7
        
        # 重新排序
        sorted_results = sorted(
            results,
            key=lambda x: x.combined_score,
            reverse=True
        )
        
        # 更新排名
        for i, result in enumerate(sorted_results, 1):
            result.rank = i
        
        return sorted_results
    
    def _rrf_rerank(
        self,
        results: List[HybridSearchResult],
        k: int = 60
    ) -> List[HybridSearchResult]:
        """Reciprocal Rank Fusion重排序"""
        # 按语义分数排名
        semantic_sorted = sorted(results, key=lambda x: x.semantic_score, reverse=True)
        semantic_ranks = {r.id: i+1 for i, r in enumerate(semantic_sorted)}
        
        # 按关键词分数排名
        keyword_sorted = sorted(results, key=lambda x: x.keyword_score, reverse=True)
        keyword_ranks = {r.id: i+1 for i, r in enumerate(keyword_sorted)}
        
        # 计算RRF分数
        for result in results:
            semantic_rrf = 1.0 / (k + semantic_ranks.get(result.id, 1000))
            keyword_rrf = 1.0 / (k + keyword_ranks.get(result.id, 1000))
            result.combined_score = semantic_rrf + keyword_rrf
        
        # 重新排序
        sorted_results = sorted(
            results,
            key=lambda x: x.combined_score,
            reverse=True
        )
        
        for i, result in enumerate(sorted_results, 1):
            result.rank = i
        
        return sorted_results
    
    def _semantic_boost_rerank(
        self,
        query: str,
        results: List[HybridSearchResult],
        boost_threshold: float = 0.7
    ) -> List[HybridSearchResult]:
        """
        语义提升重排序
        对高语义相似度的结果给予额外提升
        """
        for result in results:
            # 如果语义分数高，给予额外权重
            if result.semantic_score >= boost_threshold:
                boost = (result.semantic_score - boost_threshold) / (1 - boost_threshold)
                result.combined_score = result.combined_score * (1 + boost * 0.5)
        
        sorted_results = sorted(
            results,
            key=lambda x: x.combined_score,
            reverse=True
        )
        
        for i, result in enumerate(sorted_results, 1):
            result.rank = i
        
        return sorted_results


class HybridSearchService:
    """混合搜索服务"""
    
    def __init__(
        self,
        vector_store: VectorStore = None,
        embedding_service: EmbeddingService = None,
        alpha: float = 0.6  # 语义搜索权重
    ):
        self.vector_store = vector_store or get_vector_store()
        self.embedding_service = embedding_service or get_embedding_service()
        self.keyword_searcher = KeywordSearcher()
        self.reranker = Reranker(self.embedding_service)
        self.alpha = alpha
    
    def index_document(
        self,
        doc_id: str,
        content: str,
        metadata: Dict[str, Any] = None
    ):
        """索引文档到混合搜索"""
        # 添加到向量存储
        self.vector_store.add_document(doc_id, content, metadata)
        
        # 添加到关键词索引
        self.keyword_searcher.add_document(doc_id, content, metadata)
    
    def index_documents(
        self,
        documents: List[Tuple[str, str, Optional[Dict]]]
    ):
        """批量索引文档"""
        # 添加到向量存储
        self.vector_store.add_documents(documents)
        
        # 添加到关键词索引
        for doc_id, content, metadata in documents:
            self.keyword_searcher.add_document(doc_id, content, metadata)
    
    def search(
        self,
        query: str,
        k: int = 10,
        semantic_weight: float = None,
        rerank: bool = True,
        rerank_method: str = "cross_encoder",
        filter_metadata: Dict[str, Any] = None
    ) -> List[HybridSearchResult]:
        """
        混合搜索
        
        Args:
            query: 搜索查询
            k: 返回结果数量
            semantic_weight: 语义搜索权重（默认使用初始化时的alpha）
            rerank: 是否重排序
            rerank_method: 重排序方法
            filter_metadata: 元数据过滤条件
        """
        semantic_weight = semantic_weight or self.alpha
        keyword_weight = 1 - semantic_weight
        
        # 语义搜索
        semantic_results = self.vector_store.search(
            query, 
            k=k*2,
            filter_metadata=filter_metadata
        )
        
        # 关键词搜索
        keyword_results = self.keyword_searcher.search(query, k=k*2)
        
        # 合并结果
        combined = self._merge_results(
            semantic_results,
            keyword_results,
            semantic_weight,
            keyword_weight
        )
        
        # 重排序
        if rerank:
            combined = self.reranker.rerank(query, combined, rerank_method)
        
        return combined[:k]
    
    def _merge_results(
        self,
        semantic_results: List[SearchResult],
        keyword_results: List[Tuple[str, float]],
        semantic_weight: float,
        keyword_weight: float
    ) -> List[HybridSearchResult]:
        """合并语义和关键词搜索结果"""
        # 归一化分数
        max_semantic = max([r.score for r in semantic_results]) if semantic_results else 1.0
        max_keyword = max([s for _, s in keyword_results]) if keyword_results else 1.0
        
        # 构建结果字典
        result_dict: Dict[str, HybridSearchResult] = {}
        
        # 添加语义搜索结果
        for r in semantic_results:
            doc = r.document
            normalized_score = r.score / max_semantic if max_semantic > 0 else 0
            
            result_dict[doc.id] = HybridSearchResult(
                id=doc.id,
                content=doc.content,
                semantic_score=normalized_score,
                keyword_score=0.0,
                combined_score=normalized_score * semantic_weight,
                metadata=doc.metadata,
                rank=0,
                match_type='semantic'
            )
        
        # 添加关键词搜索结果
        for doc_id, score in keyword_results:
            normalized_score = score / max_keyword if max_keyword > 0 else 0
            
            if doc_id in result_dict:
                # 更新已有结果
                result = result_dict[doc_id]
                result.keyword_score = normalized_score
                result.combined_score += normalized_score * keyword_weight
                result.match_type = 'both'
            else:
                # 获取文档内容
                doc = self.vector_store.get_document(doc_id)
                if doc:
                    result_dict[doc_id] = HybridSearchResult(
                        id=doc_id,
                        content=doc.content,
                        semantic_score=0.0,
                        keyword_score=normalized_score,
                        combined_score=normalized_score * keyword_weight,
                        metadata=doc.metadata,
                        rank=0,
                        match_type='keyword'
                    )
        
        # 转换为列表并排序
        results = list(result_dict.values())
        results.sort(key=lambda x: x.combined_score, reverse=True)
        
        # 更新排名
        for i, result in enumerate(results, 1):
            result.rank = i
        
        return results
    
    def delete_document(self, doc_id: str):
        """删除文档"""
        self.vector_store.delete_document(doc_id)
        self.keyword_searcher.remove_document(doc_id)
    
    def get_document(self, doc_id: str) -> Optional[Dict]:
        """获取文档"""
        doc = self.vector_store.get_document(doc_id)
        if doc:
            return {
                'id': doc.id,
                'content': doc.content,
                'metadata': doc.metadata,
                'created_at': doc.created_at
            }
        return None


# 全局混合搜索服务实例
_hybrid_search_service: Optional[HybridSearchService] = None


def get_hybrid_search_service() -> HybridSearchService:
    """获取全局混合搜索服务实例"""
    global _hybrid_search_service
    if _hybrid_search_service is None:
        _hybrid_search_service = HybridSearchService()
    return _hybrid_search_service
