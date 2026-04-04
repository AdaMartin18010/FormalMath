"""
优化的搜索结果重排序器
- 多级重排序策略
- 深度学习重排序模型集成
- 领域自适应重排序
"""
import re
import time
from typing import List, Dict, Optional, Tuple, Any, Callable
from dataclasses import dataclass
from enum import Enum
import numpy as np
from functools import lru_cache

from .embedding_optimized import OptimizedEmbeddingService, get_embedding_service_optimized


class RerankStrategy(Enum):
    """重排序策略"""
    CROSS_ENCODER = "cross_encoder"           # 交叉编码器
    RECIPROCAL_RANK_FUSION = "rrf"            # RRF融合
    DIVERSITY_AWARE = "diversity"             # 多样性感知
    MMR = "mmr"                               # 最大边际相关性
    FORMULA_AWARE = "formula"                 # 公式感知
    HYBRID = "hybrid"                         # 混合策略


@dataclass
class RerankConfig:
    """重排序配置"""
    strategy: RerankStrategy = RerankStrategy.HYBRID
    top_k_initial: int = 50      # 初始候选数量
    top_k_final: int = 10        # 最终返回数量
    
    # RRF参数
    rrf_k: int = 60
    
    # MMR参数
    mmr_lambda: float = 0.5      # 相关性vs多样性平衡
    
    # 多样性参数
    diversity_threshold: float = 0.7
    
    # 公式参数
    formula_boost: float = 1.2
    
    # 性能参数
    enable_cache: bool = True
    batch_size: int = 16


@dataclass
class RerankResult:
    """重排序结果"""
    id: str
    content: str
    original_score: float
    rerank_score: float
    semantic_score: float
    keyword_score: float
    diversity_score: float
    metadata: Dict[str, Any]
    rank: int
    explanation: str = ""  # 重排序解释


class CrossEncoderScorer:
    """
    交叉编码器评分器
    
    使用双塔模型对查询-文档对进行评分
    """
    
    def __init__(self, embedding_service: OptimizedEmbeddingService = None):
        self.embedding_service = embedding_service or get_embedding_service_optimized()
        self._pair_cache: Dict[str, float] = {}
        self._max_cache_size = 5000
    
    def _get_cache_key(self, query: str, content: str) -> str:
        """生成缓存键"""
        import hashlib
        return hashlib.md5(f"{query}:{content[:200]}".encode()).hexdigest()
    
    def score(self, query: str, content: str) -> float:
        """对查询-文档对进行评分"""
        cache_key = self._get_cache_key(query, content)
        
        if cache_key in self._pair_cache:
            return self._pair_cache[cache_key]
        
        # 计算查询和文档的嵌入
        query_emb = self.embedding_service.embed_text(query)
        content_emb = self.embedding_service.embed_text(content[:1000])  # 限制长度
        
        # 计算相似度
        similarity = self.embedding_service.compute_similarity(query_emb, content_emb)
        
        # 缓存结果
        if len(self._pair_cache) >= self._max_cache_size:
            # LRU: 移除最早的条目
            self._pair_cache.pop(next(iter(self._pair_cache)))
        
        self._pair_cache[cache_key] = similarity
        return similarity
    
    def batch_score(self, query: str, contents: List[str]) -> List[float]:
        """批量评分"""
        results = []
        contents_to_score = []
        indices = []
        
        for i, content in enumerate(contents):
            cache_key = self._get_cache_key(query, content)
            if cache_key in self._pair_cache:
                results.append((i, self._pair_cache[cache_key]))
            else:
                contents_to_score.append(content)
                indices.append(i)
        
        # 批量嵌入
        if contents_to_score:
            query_emb = self.embedding_service.embed_text(query)
            content_embs = self.embedding_service.embed_texts(
                [c[:1000] for c in contents_to_score]
            )
            
            for idx, content_emb, content in zip(indices, content_embs, contents_to_score):
                similarity = self.embedding_service.compute_similarity(query_emb, content_emb)
                
                # 缓存
                cache_key = self._get_cache_key(query, content)
                self._pair_cache[cache_key] = similarity
                
                results.append((idx, similarity))
        
        # 排序
        results.sort(key=lambda x: x[0])
        return [r[1] for r in results]


class DiversityCalculator:
    """多样性计算器"""
    
    def __init__(self, embedding_service: OptimizedEmbeddingService = None):
        self.embedding_service = embedding_service or get_embedding_service_optimized()
        self._embedding_cache: Dict[str, np.ndarray] = {}
    
    def _get_embedding(self, content: str) -> np.ndarray:
        """获取或计算嵌入"""
        cache_key = hash(content[:200])
        if cache_key not in self._embedding_cache:
            self._embedding_cache[cache_key] = self.embedding_service.embed_text(content[:1000])
        return self._embedding_cache[cache_key]
    
    def compute_mmr_scores(
        self,
        query_embedding: np.ndarray,
        candidates: List[Dict],
        lambda_param: float = 0.5,
        top_k: int = 10
    ) -> List[Tuple[int, float]]:
        """
        计算MMR分数
        
        MMR = λ * Sim(query, doc) - (1-λ) * max(Sim(doc, selected))
        """
        selected = []
        selected_indices = []
        
        # 计算所有候选与查询的相似度
        query_sims = []
        for i, cand in enumerate(candidates):
            emb = self._get_embedding(cand['content'])
            sim = self.embedding_service.compute_similarity(query_embedding, emb)
            query_sims.append((i, sim))
        
        # 选择top_k
        for _ in range(min(top_k, len(candidates))):
            if not selected:
                # 第一个选择：最高查询相似度
                best_idx = max(query_sims, key=lambda x: x[1])[0]
            else:
                # MMR选择
                best_mmr = -float('inf')
                best_idx = -1
                
                for idx, query_sim in query_sims:
                    if idx in selected_indices:
                        continue
                    
                    # 计算与已选文档的最大相似度
                    cand_emb = self._get_embedding(candidates[idx]['content'])
                    max_sim_to_selected = 0
                    
                    for sel_idx in selected_indices:
                        sel_emb = self._get_embedding(candidates[sel_idx]['content'])
                        sim = self.embedding_service.compute_similarity(cand_emb, sel_emb)
                        max_sim_to_selected = max(max_sim_to_selected, sim)
                    
                    # 计算MMR分数
                    mmr_score = lambda_param * query_sim - (1 - lambda_param) * max_sim_to_selected
                    
                    if mmr_score > best_mmr:
                        best_mmr = mmr_score
                        best_idx = idx
            
            selected.append((best_idx, query_sims[best_idx][1]))
            selected_indices.append(best_idx)
        
        return selected
    
    def compute_diversity_penalty(
        self,
        results: List[Dict],
        threshold: float = 0.7
    ) -> List[float]:
        """计算多样性惩罚分数"""
        penalties = [0.0] * len(results)
        embeddings = [self._get_embedding(r['content']) for r in results]
        
        for i in range(len(results)):
            for j in range(i + 1, len(results)):
                sim = self.embedding_service.compute_similarity(embeddings[i], embeddings[j])
                if sim > threshold:
                    # 相似的文档，后面的受到惩罚
                    penalties[j] += (sim - threshold) * 0.1
        
        return penalties


class FormulaReranker:
    """公式感知重排序器"""
    
    # 公式相关关键词
    MATH_KEYWORDS = [
        'theorem', 'proof', 'lemma', 'corollary', 'proposition',
        'definition', 'axiom', 'equation', 'formula', 'identity',
        'inequality', 'convergence', 'divergence', 'derivative',
        'integral', 'limit', 'series', 'function', 'matrix',
        'vector', 'tensor', 'group', 'ring', 'field', 'space',
        'manifold', 'topology', 'homology', 'cohomology'
    ]
    
    # LaTeX模式
    LATEX_PATTERNS = [
        r'\$[^$]+\$',
        r'\\begin\{equation\}',
        r'\\begin\{align\}',
        r'\\[a-zA-Z]+\{',
        r'\\frac\{',
        r'\\sum_',
        r'\\int_',
    ]
    
    def __init__(self):
        self.compiled_patterns = [re.compile(p) for p in self.LATEX_PATTERNS]
    
    def compute_formula_score(self, content: str, query: str) -> float:
        """计算公式匹配分数"""
        # 查询中的数学关键词
        query_math_terms = sum(1 for kw in self.MATH_KEYWORDS if kw in query.lower())
        
        # 内容中的LaTeX公式
        formula_count = sum(len(p.findall(content)) for p in self.compiled_patterns)
        
        # 内容中的数学关键词
        content_math_terms = sum(1 for kw in self.MATH_KEYWORDS if kw in content.lower())
        
        # 综合分数
        formula_score = min(1.0, (formula_count * 0.1 + content_math_terms * 0.05))
        
        # 如果查询包含数学内容，提升公式丰富的结果
        if query_math_terms > 0:
            formula_score *= 1.2
        
        return min(1.0, formula_score)


class OptimizedReranker:
    """
    优化的重排序器
    
    支持多种重排序策略的组合
    """
    
    def __init__(
        self,
        embedding_service: OptimizedEmbeddingService = None,
        config: RerankConfig = None
    ):
        self.config = config or RerankConfig()
        self.embedding_service = embedding_service or get_embedding_service_optimized()
        
        # 子组件
        self.cross_encoder = CrossEncoderScorer(self.embedding_service)
        self.diversity_calc = DiversityCalculator(self.embedding_service)
        self.formula_reranker = FormulaReranker()
        
        # 性能监控
        self._rerank_times: List[float] = []
    
    def rerank(
        self,
        query: str,
        results: List[Dict],
        strategy: RerankStrategy = None
    ) -> List[RerankResult]:
        """
        重排序结果
        
        Args:
            query: 查询字符串
            results: 原始搜索结果列表
            strategy: 重排序策略
        """
        start_time = time.time()
        strategy = strategy or self.config.strategy
        
        if not results:
            return []
        
        # 限制初始候选数
        candidates = results[:self.config.top_k_initial]
        
        # 根据策略选择重排序方法
        if strategy == RerankStrategy.CROSS_ENCODER:
            reranked = self._cross_encoder_rerank(query, candidates)
        elif strategy == RerankStrategy.RECIPROCAL_RANK_FUSION:
            reranked = self._rrf_rerank(query, candidates)
        elif strategy == RerankStrategy.MMR:
            reranked = self._mmr_rerank(query, candidates)
        elif strategy == RerankStrategy.DIVERSITY_AWARE:
            reranked = self._diversity_rerank(query, candidates)
        elif strategy == RerankStrategy.FORMULA_AWARE:
            reranked = self._formula_rerank(query, candidates)
        elif strategy == RerankStrategy.HYBRID:
            reranked = self._hybrid_rerank(query, candidates)
        else:
            reranked = self._default_rerank(candidates)
        
        # 记录时间
        elapsed = (time.time() - start_time) * 1000
        self._rerank_times.append(elapsed)
        if len(self._rerank_times) > 1000:
            self._rerank_times = self._rerank_times[-1000:]
        
        return reranked[:self.config.top_k_final]
    
    def _cross_encoder_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """交叉编码器重排序"""
        contents = [c.get('content', '') for c in candidates]
        scores = self.cross_encoder.batch_score(query, contents)
        
        results = []
        for i, (cand, score) in enumerate(zip(candidates, scores)):
            results.append(RerankResult(
                id=cand.get('id', str(i)),
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=score * 0.7 + cand.get('combined_score', 0) * 0.3,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=0,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation=f"Cross-encoder score: {score:.4f}"
            ))
        
        # 排序
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        for i, r in enumerate(results, 1):
            r.rank = i
        
        return results
    
    def _rrf_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """RRF重排序"""
        k = self.config.rrf_k
        
        # 按语义分数排名
        semantic_sorted = sorted(candidates, key=lambda x: x.get('semantic_score', 0), reverse=True)
        semantic_ranks = {c.get('id', i): i + 1 for i, c in enumerate(semantic_sorted)}
        
        # 按关键词分数排名
        keyword_sorted = sorted(candidates, key=lambda x: x.get('keyword_score', 0), reverse=True)
        keyword_ranks = {c.get('id', i): i + 1 for i, c in enumerate(keyword_sorted)}
        
        # 按原始分数排名
        original_sorted = sorted(candidates, key=lambda x: x.get('combined_score', 0), reverse=True)
        original_ranks = {c.get('id', i): i + 1 for i, c in enumerate(original_sorted)}
        
        results = []
        for cand in candidates:
            doc_id = cand.get('id', '')
            semantic_rrf = 1.0 / (k + semantic_ranks.get(doc_id, 1000))
            keyword_rrf = 1.0 / (k + keyword_ranks.get(doc_id, 1000))
            original_rrf = 1.0 / (k + original_ranks.get(doc_id, 1000))
            
            rrf_score = semantic_rrf + keyword_rrf + original_rrf
            
            results.append(RerankResult(
                id=doc_id,
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=rrf_score,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=0,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation=f"RRF fusion: semantic_rank={semantic_ranks.get(doc_id, 1000)}, keyword_rank={keyword_ranks.get(doc_id, 1000)}"
            ))
        
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        for i, r in enumerate(results, 1):
            r.rank = i
        
        return results
    
    def _mmr_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """MMR重排序"""
        query_emb = self.embedding_service.embed_text(query)
        
        selected = self.diversity_calc.compute_mmr_scores(
            query_emb,
            candidates,
            lambda_param=self.config.mmr_lambda,
            top_k=self.config.top_k_final
        )
        
        results = []
        for rank, (idx, query_sim) in enumerate(selected, 1):
            cand = candidates[idx]
            results.append(RerankResult(
                id=cand.get('id', str(idx)),
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=query_sim,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=0,
                metadata=cand.get('metadata', {}),
                rank=rank,
                explanation="MMR diversity-aware ranking"
            ))
        
        return results
    
    def _diversity_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """多样性感知重排序"""
        # 计算多样性惩罚
        penalties = self.diversity_calc.compute_diversity_penalty(
            candidates,
            threshold=self.config.diversity_threshold
        )
        
        results = []
        for i, (cand, penalty) in enumerate(zip(candidates, penalties)):
            adjusted_score = cand.get('combined_score', 0) * (1 - penalty)
            
            results.append(RerankResult(
                id=cand.get('id', str(i)),
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=adjusted_score,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=1 - penalty,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation=f"Diversity penalty: {penalty:.4f}"
            ))
        
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        for i, r in enumerate(results, 1):
            r.rank = i
        
        return results
    
    def _formula_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """公式感知重排序"""
        results = []
        
        for i, cand in enumerate(candidates):
            formula_score = self.formula_reranker.compute_formula_score(
                cand.get('content', ''),
                query
            )
            
            # 提升公式匹配的结果
            boost = 1 + (formula_score * (self.config.formula_boost - 1))
            adjusted_score = cand.get('combined_score', 0) * boost
            
            results.append(RerankResult(
                id=cand.get('id', str(i)),
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=adjusted_score,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=formula_score,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation=f"Formula boost: {boost:.4f}"
            ))
        
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        for i, r in enumerate(results, 1):
            r.rank = i
        
        return results
    
    def _hybrid_rerank(self, query: str, candidates: List[Dict]) -> List[RerankResult]:
        """
        混合重排序策略
        
        结合交叉编码器、RRF和多样性
        """
        # 1. 首先使用交叉编码器评分
        contents = [c.get('content', '') for c in candidates]
        cross_scores = self.cross_encoder.batch_score(query, contents)
        
        # 2. 计算RRF分数
        k = self.config.rrf_k
        semantic_sorted = sorted(candidates, key=lambda x: x.get('semantic_score', 0), reverse=True)
        semantic_ranks = {c.get('id', i): i + 1 for i, c in enumerate(semantic_sorted)}
        keyword_ranks = {c.get('id', i): i + 1 for i, c in enumerate(
            sorted(candidates, key=lambda x: x.get('keyword_score', 0), reverse=True)
        )}
        
        # 3. 公式分数
        formula_scores = [
            self.formula_reranker.compute_formula_score(c.get('content', ''), query)
            for c in candidates
        ]
        
        results = []
        for i, (cand, cross_score, formula_score) in enumerate(zip(candidates, cross_scores, formula_scores)):
            doc_id = cand.get('id', str(i))
            
            # RRF分数
            semantic_rrf = 1.0 / (k + semantic_ranks.get(doc_id, 1000))
            keyword_rrf = 1.0 / (k + keyword_ranks.get(doc_id, 1000))
            rrf_score = semantic_rrf + keyword_rrf
            
            # 加权组合
            combined = (
                cross_score * 0.4 +
                rrf_score * 0.3 +
                cand.get('combined_score', 0) * 0.2 +
                formula_score * 0.1
            )
            
            results.append(RerankResult(
                id=doc_id,
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=combined,
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=formula_score,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation=f"Hybrid: cross={cross_score:.4f}, rrf={rrf_score:.4f}, formula={formula_score:.4f}"
            ))
        
        # 4. 多样性重排序（确保前N个结果多样性）
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        top_n = min(20, len(results))
        top_results = results[:top_n]
        
        # 对前N个应用MMR
        query_emb = self.embedding_service.embed_text(query)
        selected_indices = self.diversity_calc.compute_mmr_scores(
            query_emb,
            [{'content': r.content} for r in top_results],
            lambda_param=0.7,  # 更侧重相关性
            top_k=self.config.top_k_final
        )
        
        final_results = []
        for rank, (idx, _) in enumerate(selected_indices, 1):
            result = top_results[idx]
            result.rank = rank
            final_results.append(result)
        
        return final_results
    
    def _default_rerank(self, candidates: List[Dict]) -> List[RerankResult]:
        """默认重排序（按原始分数）"""
        results = []
        for i, cand in enumerate(candidates):
            results.append(RerankResult(
                id=cand.get('id', str(i)),
                content=cand.get('content', ''),
                original_score=cand.get('combined_score', 0),
                rerank_score=cand.get('combined_score', 0),
                semantic_score=cand.get('semantic_score', 0),
                keyword_score=cand.get('keyword_score', 0),
                diversity_score=0,
                metadata=cand.get('metadata', {}),
                rank=0,
                explanation="Default ranking (no reranking)"
            ))
        
        results.sort(key=lambda x: x.rerank_score, reverse=True)
        for i, r in enumerate(results, 1):
            r.rank = i
        
        return results
    
    def get_stats(self) -> Dict:
        """获取重排序统计"""
        return {
            'avg_rerank_time_ms': np.mean(self._rerank_times) if self._rerank_times else 0,
            'p95_rerank_time_ms': np.percentile(self._rerank_times, 95) if self._rerank_times else 0,
            'strategy': self.config.strategy.value,
            'cache_size': len(self.cross_encoder._pair_cache)
        }


# 全局实例
_reranker_optimized: Optional[OptimizedReranker] = None


def get_reranker_optimized(config: RerankConfig = None) -> OptimizedReranker:
    """获取优化的重排序器实例"""
    global _reranker_optimized
    if _reranker_optimized is None:
        _reranker_optimized = OptimizedReranker(config=config)
    return _reranker_optimized
