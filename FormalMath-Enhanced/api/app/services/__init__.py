"""
服务模块 - FormalMath语义搜索服务

包含优化版本和传统版本的搜索服务
"""
# 基础服务（原始版本）
from .semantic_search_service import (
    SemanticSearchService,
    get_semantic_search_service,
    SearchRequest,
    SearchResponse
)
from .embedding import (
    EmbeddingService,
    get_embedding_service,
    LaTeXTokenizer,
    FormulaEmbedder,
    EmbeddingConfig
)
from .vector_store import (
    VectorStore,
    get_vector_store,
    VectorDocument,
    SearchResult
)
from .hybrid_search import (
    HybridSearchService,
    get_hybrid_search_service,
    HybridSearchResult
)
from .formula_search import (
    FormulaSearchService,
    get_formula_search_service,
    FormulaMatchResult
)
from .qa_system import (
    QASystem,
    get_qa_system,
    Answer,
    Question
)

# 优化版本服务
from .embedding_optimized import (
    OptimizedEmbeddingService,
    get_embedding_service_optimized,
    ModelType,
    ModelRegistry,
    QuantizedEmbeddingCache
)
from .vector_index_optimized import (
    OptimizedVectorStore,
    get_vector_store_optimized,
    HierarchicalIndex,
    QueryCache,
    IndexLevel
)
from .formula_search_optimized import (
    FormulaSearchServiceOptimized,
    get_formula_search_service_optimized,
    VariableMappingSolver,
    FormulaNormalizer
)
from .reranker_optimized import (
    OptimizedReranker,
    get_reranker_optimized,
    RerankStrategy,
    RerankConfig,
    RerankResult,
    CrossEncoderScorer,
    DiversityCalculator
)
from .semantic_search_optimized import (
    OptimizedSemanticSearchService,
    get_semantic_search_service_optimized,
    PerformanceMetrics
)

# 基准测试
from .benchmark import (
    SearchBenchmark,
    BenchmarkResult,
    AccuracyResult,
    run_benchmark
)

__all__ = [
    # ========== 原始版本 ==========
    # 主服务
    'SemanticSearchService',
    'get_semantic_search_service',
    'SearchRequest',
    'SearchResponse',
    
    # 嵌入服务
    'EmbeddingService',
    'get_embedding_service',
    'LaTeXTokenizer',
    'FormulaEmbedder',
    'EmbeddingConfig',
    
    # 向量存储
    'VectorStore',
    'get_vector_store',
    'VectorDocument',
    'SearchResult',
    
    # 混合搜索
    'HybridSearchService',
    'get_hybrid_search_service',
    'HybridSearchResult',
    
    # 公式搜索
    'FormulaSearchService',
    'get_formula_search_service',
    'FormulaMatchResult',
    
    # 问答系统
    'QASystem',
    'get_qa_system',
    'Answer',
    'Question',
    
    # ========== 优化版本 ==========
    # 优化的嵌入服务
    'OptimizedEmbeddingService',
    'get_embedding_service_optimized',
    'ModelType',
    'ModelRegistry',
    'QuantizedEmbeddingCache',
    
    # 优化的向量存储
    'OptimizedVectorStore',
    'get_vector_store_optimized',
    'HierarchicalIndex',
    'QueryCache',
    'IndexLevel',
    
    # 优化的公式搜索
    'FormulaSearchServiceOptimized',
    'get_formula_search_service_optimized',
    'VariableMappingSolver',
    'FormulaNormalizer',
    
    # 优化的重排序器
    'OptimizedReranker',
    'get_reranker_optimized',
    'RerankStrategy',
    'RerankConfig',
    'RerankResult',
    'CrossEncoderScorer',
    'DiversityCalculator',
    
    # 优化的主搜索服务
    'OptimizedSemanticSearchService',
    'get_semantic_search_service_optimized',
    'PerformanceMetrics',
    
    # 基准测试
    'SearchBenchmark',
    'BenchmarkResult',
    'AccuracyResult',
    'run_benchmark',
]
