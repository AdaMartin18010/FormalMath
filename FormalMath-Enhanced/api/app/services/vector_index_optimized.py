"""
优化的向量索引结构
- 分层索引（HNSW + IVF + PQ）
- 增量索引构建
- 多尺度检索
"""
import os
import json
import pickle
from typing import List, Dict, Optional, Tuple, Any, Set
from dataclasses import dataclass, asdict
from datetime import datetime
from enum import Enum
import numpy as np

from .embedding_optimized import OptimizedEmbeddingService, get_embedding_service_optimized

# 尝试导入FAISS
try:
    import faiss
    FAISS_AVAILABLE = True
except ImportError:
    FAISS_AVAILABLE = False
    print("Warning: FAISS not available")


class IndexLevel(Enum):
    """索引层级"""
    L0_CENTRAL = "central"      # 中心索引（精确）
    L1_REGIONAL = "regional"    # 区域索引（IVF）
    L2_DISTRIBUTED = "distributed"  # 分布式索引（HNSW）


@dataclass
class IndexConfig:
    """索引配置"""
    dimension: int = 768
    nlist: int = 100            # IVF聚类中心数
    nprobe: int = 10            # 搜索时探查的聚类数
    hnsw_m: int = 32            # HNSW每个节点的连接数
    ef_construction: int = 200  # HNSW构建时的ef参数
    ef_search: int = 128        # HNSW搜索时的ef参数
    pq_m: int = 8               # PQ子向量数
    pq_bits: int = 8            # PQ每个子向量的比特数
    use_gpu: bool = False


@dataclass
class VectorDocument:
    """向量文档"""
    id: str
    content: str
    embedding: Optional[np.ndarray] = None
    metadata: Dict[str, Any] = None
    created_at: datetime = None
    index_level: IndexLevel = IndexLevel.L1_REGIONAL
    
    def __post_init__(self):
        if self.metadata is None:
            self.metadata = {}
        if self.created_at is None:
            self.created_at = datetime.utcnow()


@dataclass
class SearchResult:
    """搜索结果"""
    document: VectorDocument
    score: float
    rank: int
    search_level: str = "unknown"


class HierarchicalIndex:
    """
    分层向量索引
    
    架构：
    - L0（精确）：最近添加的文档，内存中的精确索引
    - L1（区域）：中等规模数据集，IVF索引
    - L2（分布式）：大规模数据集，HNSW索引
    """
    
    def __init__(self, dimension: int, config: IndexConfig = None):
        self.dimension = dimension
        self.config = config or IndexConfig(dimension=dimension)
        
        # 层级索引
        self.l0_index = None          # 精确索引（小数据集）
        self.l1_index = None          # IVF索引（中等数据集）
        self.l2_index = None          # HNSW索引（大数据集）
        
        # 文档映射
        self.doc_ids: List[str] = []
        self.id_to_level: Dict[str, IndexLevel] = {}
        self.id_to_idx: Dict[str, int] = {}
        
        # 统计
        self.doc_count = 0
        
        if FAISS_AVAILABLE:
            self._init_indexes()
    
    def _init_indexes(self):
        """初始化各级索引"""
        # L0: 精确索引（适合<10000文档）
        self.l0_index = faiss.IndexFlatIP(self.dimension)
        self.l0_index = faiss.IndexIDMap(self.l0_index)
        
        # L1: IVF索引（适合1万-100万文档）
        quantizer = faiss.IndexFlatIP(self.dimension)
        self.l1_index = faiss.IndexIVFFlat(
            quantizer, 
            self.dimension, 
            self.config.nlist,
            faiss.METRIC_INNER_PRODUCT
        )
        self.l1_index = faiss.IndexIDMap(self.l1_index)
        
        # L2: HNSW索引（适合>100万文档）
        self.l2_index = faiss.IndexHNSWFlat(self.dimension, self.config.hnsw_m)
        self.l2_index.hnsw.efConstruction = self.config.ef_construction
        self.l2_index.hnsw.efSearch = self.config.ef_search
        self.l2_index = faiss.IndexIDMap(self.l2_index)
    
    def _determine_level(self, doc_count: int) -> IndexLevel:
        """根据文档数量确定索引层级"""
        if doc_count < 10000:
            return IndexLevel.L0_CENTRAL
        elif doc_count < 1000000:
            return IndexLevel.L1_REGIONAL
        else:
            return IndexLevel.L2_DISTRIBUTED
    
    def add(self, embeddings: np.ndarray, doc_ids: List[str]):
        """添加向量到索引"""
        if not FAISS_AVAILABLE or len(embeddings) == 0:
            return
        
        embeddings = embeddings.astype(np.float32)
        
        # 确定索引层级
        target_level = self._determine_level(self.doc_count + len(doc_ids))
        
        # 生成内部ID
        start_id = len(self.doc_ids)
        internal_ids = np.arange(start_id, start_id + len(doc_ids), dtype=np.int64)
        
        # 根据层级选择索引
        if target_level == IndexLevel.L0_CENTRAL:
            self.l0_index.add_with_ids(embeddings, internal_ids)
        elif target_level == IndexLevel.L1_REGIONAL:
            if not self.l1_index.is_trained:
                self.l1_index.train(embeddings)
            self.l1_index.add_with_ids(embeddings, internal_ids)
        else:
            self.l2_index.add_with_ids(embeddings, internal_ids)
        
        # 更新映射
        for i, doc_id in enumerate(doc_ids):
            self.doc_ids.append(doc_id)
            self.id_to_level[doc_id] = target_level
            self.id_to_idx[doc_id] = start_id + i
        
        self.doc_count += len(doc_ids)
    
    def search(
        self, 
        query_embedding: np.ndarray, 
        k: int = 10,
        nprobe: int = None
    ) -> Tuple[np.ndarray, np.ndarray, List[str]]:
        """
        分层搜索
        
        Returns:
            (scores, indices, levels) - levels表示每个结果来自哪个层级
        """
        if not FAISS_AVAILABLE or self.doc_count == 0:
            return np.array([]), np.array([]), []
        
        query_embedding = query_embedding.astype(np.float32).reshape(1, -1)
        nprobe = nprobe or self.config.nprobe
        
        all_scores = []
        all_indices = []
        all_levels = []
        
        # L0搜索（如果存在）
        if self.l0_index.ntotal > 0:
            scores, indices = self.l0_index.search(query_embedding, min(k, self.l0_index.ntotal))
            all_scores.extend(scores[0])
            all_indices.extend(indices[0])
            all_levels.extend(["L0"] * len(scores[0]))
        
        # L1搜索
        if self.l1_index.ntotal > 0:
            self.l1_index.nprobe = nprobe
            scores, indices = self.l1_index.search(query_embedding, min(k, self.l1_index.ntotal))
            all_scores.extend(scores[0])
            all_indices.extend(indices[0])
            all_levels.extend(["L1"] * len(scores[0]))
        
        # L2搜索
        if self.l2_index.ntotal > 0:
            scores, indices = self.l2_index.search(query_embedding, min(k, self.l2_index.ntotal))
            all_scores.extend(scores[0])
            all_indices.extend(indices[0])
            all_levels.extend(["L2"] * len(scores[0]))
        
        # 合并并排序
        if all_scores:
            combined = list(zip(all_scores, all_indices, all_levels))
            combined.sort(key=lambda x: x[0], reverse=True)
            combined = combined[:k]
            
            return (
                np.array([c[0] for c in combined]),
                np.array([c[1] for c in combined]),
                [c[2] for c in combined]
            )
        
        return np.array([]), np.array([]), []
    
    def remove(self, doc_id: str):
        """删除文档"""
        if doc_id not in self.id_to_idx:
            return
        
        internal_id = self.id_to_idx[doc_id]
        level = self.id_to_level.get(doc_id)
        
        if level == IndexLevel.L0_CENTRAL:
            self.l0_index.remove_ids(np.array([internal_id], dtype=np.int64))
        elif level == IndexLevel.L1_REGIONAL:
            self.l1_index.remove_ids(np.array([internal_id], dtype=np.int64))
        else:
            self.l2_index.remove_ids(np.array([internal_id], dtype=np.int64))
        
        self.doc_ids[internal_id] = None
        del self.id_to_level[doc_id]
        del self.id_to_idx[doc_id]
    
    def save(self, path: str):
        """保存索引"""
        if not FAISS_AVAILABLE:
            return
        
        os.makedirs(path, exist_ok=True)
        
        # 保存各级索引
        if self.l0_index:
            faiss.write_index(self.l0_index, os.path.join(path, "l0.index"))
        if self.l1_index:
            faiss.write_index(self.l1_index, os.path.join(path, "l1.index"))
        if self.l2_index:
            faiss.write_index(self.l2_index, os.path.join(path, "l2.index"))
        
        # 保存映射
        with open(os.path.join(path, "mapping.pkl"), 'wb') as f:
            pickle.dump({
                'doc_ids': self.doc_ids,
                'id_to_level': self.id_to_level,
                'id_to_idx': self.id_to_idx,
                'doc_count': self.doc_count
            }, f)
    
    def load(self, path: str):
        """加载索引"""
        if not FAISS_AVAILABLE:
            return
        
        # 加载各级索引
        l0_path = os.path.join(path, "l0.index")
        l1_path = os.path.join(path, "l1.index")
        l2_path = os.path.join(path, "l2.index")
        
        if os.path.exists(l0_path):
            self.l0_index = faiss.read_index(l0_path)
        if os.path.exists(l1_path):
            self.l1_index = faiss.read_index(l1_path)
        if os.path.exists(l2_path):
            self.l2_index = faiss.read_index(l2_path)
        
        # 加载映射
        mapping_path = os.path.join(path, "mapping.pkl")
        if os.path.exists(mapping_path):
            with open(mapping_path, 'rb') as f:
                mapping = pickle.load(f)
                self.doc_ids = mapping['doc_ids']
                self.id_to_level = mapping['id_to_level']
                self.id_to_idx = mapping['id_to_idx']
                self.doc_count = mapping['doc_count']


class QueryCache:
    """查询结果缓存"""
    
    def __init__(self, max_size: int = 1000, ttl_seconds: float = 300):
        self.max_size = max_size
        self.ttl_seconds = ttl_seconds
        self._cache: Dict[str, Dict] = {}
        self._timestamps: Dict[str, float] = {}
        self._access_count: Dict[str, int] = {}
    
    def _get_key(self, query: str, k: int, filter_metadata: Dict) -> str:
        """生成缓存键"""
        import hashlib
        key_str = f"{query}:{k}:{json.dumps(filter_metadata, sort_keys=True)}"
        return hashlib.md5(key_str.encode()).hexdigest()
    
    def get(self, query: str, k: int, filter_metadata: Dict) -> Optional[List[SearchResult]]:
        """获取缓存结果"""
        key = self._get_key(query, k, filter_metadata)
        
        if key in self._cache:
            # 检查TTL
            if time.time() - self._timestamps[key] > self.ttl_seconds:
                del self._cache[key]
                del self._timestamps[key]
                del self._access_count[key]
                return None
            
            self._access_count[key] += 1
            return self._cache[key]
        
        return None
    
    def put(self, query: str, k: int, filter_metadata: Dict, results: List[SearchResult]):
        """缓存结果"""
        key = self._get_key(query, k, filter_metadata)
        
        # LRU淘汰
        if len(self._cache) >= self.max_size:
            min_key = min(self._access_count, key=self._access_count.get)
            del self._cache[min_key]
            del self._timestamps[min_key]
            del self._access_count[min_key]
        
        self._cache[key] = results
        self._timestamps[key] = time.time()
        self._access_count[key] = 1
    
    def clear(self):
        """清空缓存"""
        self._cache.clear()
        self._timestamps.clear()
        self._access_count.clear()


class OptimizedVectorStore:
    """优化的向量存储"""
    
    def __init__(
        self,
        collection_name: str = "default",
        dimension: int = 768,
        embedding_service: OptimizedEmbeddingService = None,
        persist_dir: str = "./vector_store_optimized",
        enable_cache: bool = True
    ):
        self.collection_name = collection_name
        self.dimension = dimension
        self.embedding_service = embedding_service or get_embedding_service_optimized()
        self.persist_dir = persist_dir
        
        # 创建索引
        if FAISS_AVAILABLE:
            self.index = HierarchicalIndex(dimension)
        else:
            self.index = None
        
        # 文档存储
        self.documents: Dict[str, VectorDocument] = {}
        
        # 查询缓存
        self.query_cache = QueryCache() if enable_cache else None
        
        # 确保目录存在
        os.makedirs(persist_dir, exist_ok=True)
        
        # 加载已有数据
        self._load()
    
    def add_document(
        self,
        doc_id: str,
        content: str,
        metadata: Dict[str, Any] = None,
        embedding: np.ndarray = None
    ) -> VectorDocument:
        """添加文档"""
        if embedding is None:
            embedding = self.embedding_service.embed_math_content(content)
        
        doc = VectorDocument(
            id=doc_id,
            content=content,
            embedding=embedding,
            metadata=metadata or {}
        )
        
        # 添加到索引
        if self.index:
            self.index.add(embedding.reshape(1, -1), [doc_id])
        
        self.documents[doc_id] = doc
        
        # 清除相关缓存
        if self.query_cache:
            self.query_cache.clear()
        
        return doc
    
    def add_documents(
        self,
        documents: List[Tuple[str, str, Optional[Dict]]]
    ) -> List[VectorDocument]:
        """批量添加文档"""
        if not documents:
            return []
        
        results = []
        embeddings_list = []
        doc_ids = []
        
        for doc_id, content, metadata in documents:
            embedding = self.embedding_service.embed_math_content(content)
            embeddings_list.append(embedding)
            doc_ids.append(doc_id)
            
            doc = VectorDocument(
                id=doc_id,
                content=content,
                embedding=embedding,
                metadata=metadata or {}
            )
            self.documents[doc_id] = doc
            results.append(doc)
        
        # 批量添加到索引
        if embeddings_list and self.index:
            embeddings = np.array(embeddings_list)
            self.index.add(embeddings, doc_ids)
        
        # 清除缓存
        if self.query_cache:
            self.query_cache.clear()
        
        return results
    
    def search(
        self,
        query: str,
        k: int = 10,
        filter_metadata: Dict[str, Any] = None,
        use_cache: bool = True
    ) -> List[SearchResult]:
        """语义搜索"""
        # 检查缓存
        if use_cache and self.query_cache:
            cached = self.query_cache.get(query, k, filter_metadata or {})
            if cached is not None:
                return cached
        
        # 计算查询嵌入
        query_embedding = self.embedding_service.embed_math_content(query)
        
        # 搜索索引
        if self.index:
            scores, indices, levels = self.index.search(query_embedding, k * 2)
        else:
            # Fallback: 线性搜索
            scores, indices, levels = self._fallback_search(query_embedding, k * 2)
        
        results = []
        rank = 1
        
        for score, idx, level in zip(scores, indices, levels):
            if idx < 0 or idx >= len(self.index.doc_ids if self.index else []):
                continue
            
            doc_id = self.index.doc_ids[idx] if self.index else list(self.documents.keys())[int(idx)]
            if doc_id is None or doc_id not in self.documents:
                continue
            
            doc = self.documents[doc_id]
            
            # 元数据过滤
            if filter_metadata and not self._match_filter(doc.metadata, filter_metadata):
                continue
            
            results.append(SearchResult(
                document=doc,
                score=float(score),
                rank=rank,
                search_level=level
            ))
            rank += 1
            
            if len(results) >= k:
                break
        
        # 缓存结果
        if use_cache and self.query_cache:
            self.query_cache.put(query, k, filter_metadata or {}, results)
        
        return results
    
    def _fallback_search(
        self, 
        query_embedding: np.ndarray, 
        k: int
    ) -> Tuple[np.ndarray, np.ndarray, List[str]]:
        """Fallback线性搜索"""
        scores = []
        indices = []
        
        query_norm = np.linalg.norm(query_embedding)
        if query_norm == 0:
            return np.array([]), np.array([]), []
        
        for idx, (doc_id, doc) in enumerate(self.documents.items()):
            if doc.embedding is not None:
                emb_norm = np.linalg.norm(doc.embedding)
                if emb_norm > 0:
                    similarity = np.dot(query_embedding, doc.embedding) / (query_norm * emb_norm)
                    scores.append(similarity)
                    indices.append(idx)
        
        if scores:
            sorted_indices = np.argsort(scores)[::-1][:k]
            return (
                np.array([scores[i] for i in sorted_indices]),
                np.array([indices[i] for i in sorted_indices]),
                ["fallback"] * len(sorted_indices)
            )
        
        return np.array([]), np.array([]), []
    
    def _match_filter(self, metadata: Dict, filter_criteria: Dict) -> bool:
        """检查元数据是否匹配过滤条件"""
        for key, value in filter_criteria.items():
            if key not in metadata:
                return False
            
            if isinstance(value, dict):
                for op, op_value in value.items():
                    if op == '$eq' and metadata[key] != op_value:
                        return False
                    elif op == '$ne' and metadata[key] == op_value:
                        return False
                    elif op == '$gt' and not (metadata[key] > op_value):
                        return False
                    elif op == '$gte' and not (metadata[key] >= op_value):
                        return False
                    elif op == '$lt' and not (metadata[key] < op_value):
                        return False
                    elif op == '$lte' and not (metadata[key] <= op_value):
                        return False
                    elif op == '$in' and metadata[key] not in op_value:
                        return False
                    elif op == '$nin' and metadata[key] in op_value:
                        return False
            else:
                if metadata[key] != value:
                    return False
        
        return True
    
    def delete_document(self, doc_id: str):
        """删除文档"""
        if doc_id in self.documents:
            if self.index:
                self.index.remove(doc_id)
            del self.documents[doc_id]
            
            if self.query_cache:
                self.query_cache.clear()
    
    def save(self):
        """保存索引"""
        index_path = os.path.join(self.persist_dir, self.collection_name)
        if self.index:
            self.index.save(index_path)
        
        # 保存文档
        docs_path = os.path.join(self.persist_dir, f"{self.collection_name}.docs")
        with open(docs_path, 'wb') as f:
            pickle.dump(self.documents, f)
        
        # 保存元数据
        meta_path = os.path.join(self.persist_dir, f"{self.collection_name}.meta")
        with open(meta_path, 'w') as f:
            json.dump({
                'collection_name': self.collection_name,
                'dimension': self.dimension,
                'doc_count': len(self.documents),
                'created_at': datetime.utcnow().isoformat()
            }, f)
    
    def _load(self):
        """加载索引"""
        index_path = os.path.join(self.persist_dir, self.collection_name)
        if os.path.exists(index_path) and self.index:
            self.index.load(index_path)
        
        docs_path = os.path.join(self.persist_dir, f"{self.collection_name}.docs")
        if os.path.exists(docs_path):
            with open(docs_path, 'rb') as f:
                self.documents = pickle.load(f)
    
    def get_stats(self) -> Dict:
        """获取统计信息"""
        return {
            'collection_name': self.collection_name,
            'dimension': self.dimension,
            'document_count': len(self.documents),
            'index_type': 'Hierarchical' if FAISS_AVAILABLE else 'Fallback',
            'cache_enabled': self.query_cache is not None
        }


# 全局实例
_vector_stores_optimized: Dict[str, OptimizedVectorStore] = {}


def get_vector_store_optimized(collection_name: str = "default") -> OptimizedVectorStore:
    """获取优化的向量存储实例"""
    if collection_name not in _vector_stores_optimized:
        _vector_stores_optimized[collection_name] = OptimizedVectorStore(
            collection_name=collection_name
        )
    return _vector_stores_optimized[collection_name]
