"""
向量数据库存储与检索服务
支持FAISS索引、相似度搜索、近似最近邻
"""
import os
import json
import pickle
from typing import List, Dict, Optional, Tuple, Any, Union
from dataclasses import dataclass, asdict
from datetime import datetime
import numpy as np

from .embedding import EmbeddingService, get_embedding_service, EmbeddingConfig

# 尝试导入FAISS
try:
    import faiss
    FAISS_AVAILABLE = True
except ImportError:
    FAISS_AVAILABLE = False
    print("Warning: FAISS not available, using fallback vector search")


@dataclass
class VectorDocument:
    """向量文档"""
    id: str
    content: str
    embedding: Optional[np.ndarray] = None
    metadata: Dict[str, Any] = None
    created_at: datetime = None
    
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


class FAISSIndex:
    """FAISS向量索引封装"""
    
    def __init__(self, dimension: int, index_type: str = "Flat"):
        self.dimension = dimension
        self.index_type = index_type
        self.index = None
        self.doc_ids: List[str] = []
        
        if FAISS_AVAILABLE:
            self._create_index()
    
    def _create_index(self):
        """创建FAISS索引"""
        if not FAISS_AVAILABLE:
            return
        
        if self.index_type == "Flat":
            # 精确搜索，适合小数据集
            self.index = faiss.IndexFlatIP(self.dimension)  # 内积（余弦相似度）
        elif self.index_type == "IVF":
            # 倒排文件索引，适合中等数据集
            quantizer = faiss.IndexFlatIP(self.dimension)
            nlist = 100  # 聚类中心数
            self.index = faiss.IndexIVFFlat(quantizer, self.dimension, nlist)
        elif self.index_type == "HNSW":
            # HNSW图索引，适合大数据集
            self.index = faiss.IndexHNSWFlat(self.dimension, 32)
            self.index.hnsw.efConstruction = 200
        elif self.index_type == "PQ":
            # 乘积量化，适合内存受限场景
            m = 8  # 子向量数
            nbits = 8  # 每个子向量的比特数
            self.index = faiss.IndexPQ(self.dimension, m, nbits)
        else:
            self.index = faiss.IndexFlatIP(self.dimension)
        
        # 使用ID映射，支持删除操作
        self.index = faiss.IndexIDMap(self.index)
    
    def add(self, embeddings: np.ndarray, doc_ids: List[str]):
        """添加向量到索引"""
        if not FAISS_AVAILABLE or self.index is None:
            return
        
        if len(embeddings) == 0:
            return
        
        # 转换为float32
        embeddings = embeddings.astype(np.float32)
        
        # 生成内部ID
        start_id = len(self.doc_ids)
        ids = np.arange(start_id, start_id + len(doc_ids), dtype=np.int64)
        
        # 添加向量
        self.index.add_with_ids(embeddings, ids)
        self.doc_ids.extend(doc_ids)
    
    def search(self, query_embedding: np.ndarray, k: int = 10) -> Tuple[np.ndarray, np.ndarray]:
        """搜索最近邻"""
        if not FAISS_AVAILABLE or self.index is None:
            # Fallback：返回空结果
            return np.array([]), np.array([])
        
        if self.index.ntotal == 0:
            return np.array([]), np.array([])
        
        # 转换为float32并reshape
        query_embedding = query_embedding.astype(np.float32).reshape(1, -1)
        
        # 搜索
        distances, indices = self.index.search(query_embedding, min(k, self.index.ntotal))
        
        return distances[0], indices[0]
    
    def remove(self, doc_id: str):
        """从索引中删除文档"""
        if not FAISS_AVAILABLE or self.index is None:
            return
        
        try:
            idx = self.doc_ids.index(doc_id)
            self.index.remove_ids(np.array([idx], dtype=np.int64))
            self.doc_ids[idx] = None  # 标记为删除
        except ValueError:
            pass
    
    def save(self, path: str):
        """保存索引到文件"""
        if not FAISS_AVAILABLE or self.index is None:
            return
        
        faiss.write_index(self.index, path)
        
        # 保存文档ID映射
        with open(path + '.ids', 'wb') as f:
            pickle.dump(self.doc_ids, f)
    
    def load(self, path: str):
        """从文件加载索引"""
        if not FAISS_AVAILABLE:
            return
        
        self.index = faiss.read_index(path)
        
        # 加载文档ID映射
        if os.path.exists(path + '.ids'):
            with open(path + '.ids', 'rb') as f:
                self.doc_ids = pickle.load(f)


class FallbackIndex:
    """Fallback索引（当FAISS不可用时）"""
    
    def __init__(self, dimension: int):
        self.dimension = dimension
        self.embeddings: Dict[str, np.ndarray] = {}
    
    def add(self, embeddings: np.ndarray, doc_ids: List[str]):
        """添加向量"""
        for i, doc_id in enumerate(doc_ids):
            self.embeddings[doc_id] = embeddings[i]
    
    def search(self, query_embedding: np.ndarray, k: int = 10) -> Tuple[np.ndarray, np.ndarray]:
        """线性搜索"""
        if not self.embeddings:
            return np.array([]), np.array([])
        
        # 计算所有余弦相似度
        scores = []
        ids = []
        
        query_norm = np.linalg.norm(query_embedding)
        if query_norm == 0:
            return np.array([]), np.array([])
        
        for doc_id, emb in self.embeddings.items():
            emb_norm = np.linalg.norm(emb)
            if emb_norm > 0:
                similarity = np.dot(query_embedding, emb) / (query_norm * emb_norm)
                scores.append(similarity)
                ids.append(list(self.embeddings.keys()).index(doc_id))
        
        # 排序并取前k个
        if scores:
            sorted_indices = np.argsort(scores)[::-1][:k]
            return np.array([scores[i] for i in sorted_indices]), np.array([ids[i] for i in sorted_indices])
        
        return np.array([]), np.array([])
    
    def remove(self, doc_id: str):
        """删除文档"""
        if doc_id in self.embeddings:
            del self.embeddings[doc_id]
    
    def save(self, path: str):
        """保存索引"""
        with open(path + '.fallback', 'wb') as f:
            pickle.dump(self.embeddings, f)
    
    def load(self, path: str):
        """加载索引"""
        if os.path.exists(path + '.fallback'):
            with open(path + '.fallback', 'rb') as f:
                self.embeddings = pickle.load(f)


class VectorStore:
    """向量存储主类"""
    
    def __init__(
        self,
        collection_name: str = "default",
        dimension: int = 384,
        index_type: str = "Flat",
        embedding_service: EmbeddingService = None,
        persist_dir: str = "./vector_store"
    ):
        self.collection_name = collection_name
        self.dimension = dimension
        self.embedding_service = embedding_service or get_embedding_service()
        self.persist_dir = persist_dir
        
        # 创建索引
        if FAISS_AVAILABLE:
            self.index = FAISSIndex(dimension, index_type)
        else:
            self.index = FallbackIndex(dimension)
        
        # 文档存储
        self.documents: Dict[str, VectorDocument] = {}
        
        # 确保持久化目录存在
        os.makedirs(persist_dir, exist_ok=True)
        
        # 尝试加载已有数据
        self._load()
    
    def add_document(
        self,
        doc_id: str,
        content: str,
        metadata: Dict[str, Any] = None,
        embedding: np.ndarray = None
    ) -> VectorDocument:
        """添加文档"""
        # 如果未提供嵌入，则计算
        if embedding is None:
            embedding = self.embedding_service.embed_math_content(content)
        
        # 创建文档
        doc = VectorDocument(
            id=doc_id,
            content=content,
            embedding=embedding,
            metadata=metadata or {}
        )
        
        # 添加到索引
        self.index.add(
            embedding.reshape(1, -1),
            [doc_id]
        )
        
        # 存储文档
        self.documents[doc_id] = doc
        
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
        if embeddings_list:
            embeddings = np.array(embeddings_list)
            self.index.add(embeddings, doc_ids)
        
        return results
    
    def search(
        self,
        query: str,
        k: int = 10,
        filter_metadata: Dict[str, Any] = None
    ) -> List[SearchResult]:
        """语义搜索"""
        # 计算查询嵌入
        query_embedding = self.embedding_service.embed_math_content(query)
        
        # 搜索
        scores, indices = self.index.search(query_embedding, k * 2)  # 获取更多结果以便过滤
        
        results = []
        rank = 1
        
        for score, idx in zip(scores, indices):
            if idx < 0 or idx >= len(self.index.doc_ids):
                continue
            
            doc_id = self.index.doc_ids[idx]
            if doc_id is None or doc_id not in self.documents:
                continue
            
            doc = self.documents[doc_id]
            
            # 元数据过滤
            if filter_metadata:
                if not self._match_filter(doc.metadata, filter_metadata):
                    continue
            
            results.append(SearchResult(
                document=doc,
                score=float(score),
                rank=rank
            ))
            rank += 1
            
            if len(results) >= k:
                break
        
        return results
    
    def search_by_vector(
        self,
        embedding: np.ndarray,
        k: int = 10
    ) -> List[SearchResult]:
        """使用向量进行搜索"""
        scores, indices = self.index.search(embedding, k)
        
        results = []
        for rank, (score, idx) in enumerate(zip(scores, indices), 1):
            if idx < 0 or idx >= len(self.index.doc_ids):
                continue
            
            doc_id = self.index.doc_ids[idx]
            if doc_id is None or doc_id not in self.documents:
                continue
            
            results.append(SearchResult(
                document=self.documents[doc_id],
                score=float(score),
                rank=rank
            ))
        
        return results
    
    def get_document(self, doc_id: str) -> Optional[VectorDocument]:
        """获取文档"""
        return self.documents.get(doc_id)
    
    def delete_document(self, doc_id: str):
        """删除文档"""
        if doc_id in self.documents:
            self.index.remove(doc_id)
            del self.documents[doc_id]
    
    def update_document(
        self,
        doc_id: str,
        content: str = None,
        metadata: Dict[str, Any] = None
    ) -> Optional[VectorDocument]:
        """更新文档"""
        if doc_id not in self.documents:
            return None
        
        doc = self.documents[doc_id]
        
        if content is not None and content != doc.content:
            doc.content = content
            doc.embedding = self.embedding_service.embed_math_content(content)
            
            # 更新索引
            self.index.remove(doc_id)
            self.index.add(doc.embedding.reshape(1, -1), [doc_id])
        
        if metadata is not None:
            doc.metadata.update(metadata)
        
        doc.created_at = datetime.utcnow()
        
        return doc
    
    def _match_filter(
        self,
        metadata: Dict[str, Any],
        filter_criteria: Dict[str, Any]
    ) -> bool:
        """检查元数据是否匹配过滤条件"""
        for key, value in filter_criteria.items():
            if key not in metadata:
                return False
            
            if isinstance(value, dict):
                # 支持操作符：$eq, $ne, $gt, $gte, $lt, $lte, $in, $nin
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
    
    def save(self):
        """保存索引和文档"""
        index_path = os.path.join(self.persist_dir, f"{self.collection_name}.index")
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
        """加载索引和文档"""
        index_path = os.path.join(self.persist_dir, f"{self.collection_name}.index")
        docs_path = os.path.join(self.persist_dir, f"{self.collection_name}.docs")
        
        if os.path.exists(index_path):
            self.index.load(index_path)
        
        if os.path.exists(docs_path):
            with open(docs_path, 'rb') as f:
                self.documents = pickle.load(f)
    
    def get_stats(self) -> Dict[str, any]:
        """获取统计信息"""
        return {
            'collection_name': self.collection_name,
            'dimension': self.dimension,
            'document_count': len(self.documents),
            'index_type': 'FAISS' if FAISS_AVAILABLE else 'Fallback'
        }


# 全局向量存储实例
_vector_stores: Dict[str, VectorStore] = {}


def get_vector_store(collection_name: str = "default") -> VectorStore:
    """获取向量存储实例"""
    if collection_name not in _vector_stores:
        _vector_stores[collection_name] = VectorStore(collection_name=collection_name)
    return _vector_stores[collection_name]
