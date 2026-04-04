"""
知识图谱嵌入模型
- TransE: 平移距离模型
- RotatE: 旋转模型
- 概念向量表示与语义相似度计算
"""
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from typing import Dict, List, Optional, Tuple, Any
from sqlalchemy.orm import Session
from collections import defaultdict
import logging

from ..models.models import KnowledgeGraphNode, KnowledgeGraphRelation, UserProgress

logger = logging.getLogger(__name__)


class TransE(nn.Module):
    """
    TransE模型: h + r ≈ t
    通过平移距离建模知识图谱中的关系
    """
    
    def __init__(self, num_entities: int, num_relations: int, embedding_dim: int = 128, gamma: float = 12.0):
        super(TransE, self).__init__()
        self.embedding_dim = embedding_dim
        self.gamma = gamma
        
        # 实体嵌入
        self.entity_embedding = nn.Embedding(num_entities, embedding_dim)
        # 关系嵌入
        self.relation_embedding = nn.Embedding(num_relations, embedding_dim)
        
        # 初始化
        self._init_weights()
    
    def _init_weights(self):
        """初始化权重"""
        nn.init.uniform_(self.entity_embedding.weight, -6/(self.embedding_dim**0.5), 6/(self.embedding_dim**0.5))
        nn.init.uniform_(self.relation_embedding.weight, -6/(self.embedding_dim**0.5), 6/(self.embedding_dim**0.5))
        
        # 归一化实体嵌入
        self.entity_embedding.weight.data = F.normalize(self.entity_embedding.weight.data, p=2, dim=1)
    
    def forward(self, heads: torch.Tensor, relations: torch.Tensor, tails: torch.Tensor) -> torch.Tensor:
        """
        前向传播计算分数
        
        Args:
            heads: 头实体索引 [batch_size]
            relations: 关系索引 [batch_size]
            tails: 尾实体索引 [batch_size]
        
        Returns:
            分数（距离） [batch_size]
        """
        h = self.entity_embedding(heads)
        r = self.relation_embedding(relations)
        t = self.entity_embedding(tails)
        
        # TransE评分函数: ||h + r - t||
        score = torch.norm(h + r - t, p=2, dim=1)
        return score
    
    def get_entity_embedding(self, entity_id: int) -> np.ndarray:
        """获取实体嵌入向量"""
        with torch.no_grad():
            embedding = self.entity_embedding(torch.tensor([entity_id])).numpy()
        return embedding[0]


class RotatE(nn.Module):
    """
    RotatE模型: 在复数空间中使用旋转建模关系
    h ◦ r = t, 其中r是旋转
    """
    
    def __init__(self, num_entities: int, num_relations: int, embedding_dim: int = 250, gamma: float = 12.0):
        super(RotatE, self).__init__()
        self.embedding_dim = embedding_dim  # 复数空间的维度
        self.gamma = gamma
        
        # 实体嵌入（实部和虚部）
        self.entity_embedding = nn.Embedding(num_entities, embedding_dim * 2)
        # 关系嵌入（相位）
        self.relation_embedding = nn.Embedding(num_relations, embedding_dim)
        
        self._init_weights()
    
    def _init_weights(self):
        """初始化权重"""
        nn.init.uniform_(self.entity_embedding.weight, -6/(self.embedding_dim**0.5), 6/(self.embedding_dim**0.5))
        nn.init.uniform_(self.relation_embedding.weight, -6/(self.embedding_dim**0.5), 6/(self.embedding_dim**0.5))
    
    def forward(self, heads: torch.Tensor, relations: torch.Tensor, tails: torch.Tensor) -> torch.Tensor:
        """
        前向传播
        
        将实体分解为实部和虚部，关系表示为旋转角度
        """
        # 获取嵌入
        h = self.entity_embedding(heads)
        r = self.relation_embedding(relations)
        t = self.entity_embedding(tails)
        
        # 分离实部和虚部
        h_re, h_im = torch.chunk(h, 2, dim=-1)
        t_re, t_im = torch.chunk(t, 2, dim=-1)
        
        # 关系作为相位
        r_phase = r / (self.embedding_dim ** 0.5)
        
        # 旋转
        cos_r = torch.cos(r_phase)
        sin_r = torch.sin(r_phase)
        
        h_rotate_re = h_re * cos_r - h_im * sin_r
        h_rotate_im = h_re * sin_r + h_im * cos_r
        
        # 计算距离
        score_re = h_rotate_re - t_re
        score_im = h_rotate_im - t_im
        
        score = torch.stack([score_re, score_im], dim=0).norm(dim=0).sum(dim=-1)
        return score
    
    def get_entity_embedding(self, entity_id: int) -> np.ndarray:
        """获取实体嵌入向量"""
        with torch.no_grad():
            embedding = self.entity_embedding(torch.tensor([entity_id])).numpy()
        return embedding[0]


class KnowledgeGraphEmbedding:
    """知识图谱嵌入管理器"""
    
    def __init__(self, db: Session, model_type: str = "rotate", embedding_dim: int = 128):
        self.db = db
        self.model_type = model_type.lower()
        self.embedding_dim = embedding_dim
        self.model = None
        self.entity2id = {}
        self.relation2id = {}
        self.id2entity = {}
        self.id2relation = {}
        self.triples = []
        
    def load_knowledge_graph(self):
        """从数据库加载知识图谱"""
        # 加载所有实体
        nodes = self.db.query(KnowledgeGraphNode).all()
        self.entity2id = {node.id: idx for idx, node in enumerate(nodes)}
        self.id2entity = {idx: node.id for idx, node in enumerate(nodes)}
        
        # 加载所有关系
        relations = self.db.query(KnowledgeGraphRelation.relation_type).distinct().all()
        relation_types = [r[0] for r in relations]
        self.relation2id = {rel: idx for idx, rel in enumerate(relation_types)}
        self.id2relation = {idx: rel for idx, rel in enumerate(relation_types)}
        
        # 加载所有三元组
        all_relations = self.db.query(KnowledgeGraphRelation).all()
        self.triples = []
        for rel in all_relations:
            if rel.source_id in self.entity2id and rel.target_id in self.entity2id:
                self.triples.append((
                    self.entity2id[rel.source_id],
                    self.relation2id.get(rel.relation_type, 0),
                    self.entity2id[rel.target_id]
                ))
        
        logger.info(f"加载知识图谱: {len(self.entity2id)}实体, {len(self.relation2id)}关系, {len(self.triples)}三元组")
    
    def build_model(self):
        """构建嵌入模型"""
        if not self.entity2id:
            self.load_knowledge_graph()
        
        num_entities = len(self.entity2id)
        num_relations = max(len(self.relation2id), 1)
        
        if self.model_type == "transe":
            self.model = TransE(num_entities, num_relations, self.embedding_dim)
        elif self.model_type == "rotate":
            self.model = RotatE(num_entities, num_relations, self.embedding_dim)
        else:
            raise ValueError(f"不支持的模型类型: {self.model_type}")
        
        logger.info(f"构建{self.model_type}模型完成")
    
    def train(self, epochs: int = 1000, batch_size: int = 256, lr: float = 0.001, 
              negative_samples: int = 10, device: str = "cpu") -> List[float]:
        """
        训练知识图谱嵌入模型
        
        Args:
            epochs: 训练轮数
            batch_size: 批次大小
            lr: 学习率
            negative_samples: 负采样数量
            device: 计算设备
        
        Returns:
            训练损失历史
        """
        if self.model is None:
            self.build_model()
        
        self.model.to(device)
        optimizer = torch.optim.Adam(self.model.parameters(), lr=lr)
        
        losses = []
        num_triples = len(self.triples)
        
        for epoch in range(epochs):
            self.model.train()
            epoch_loss = 0
            
            # 随机打乱
            np.random.shuffle(self.triples)
            
            for i in range(0, num_triples, batch_size):
                batch_triples = self.triples[i:i+batch_size]
                
                heads = torch.tensor([t[0] for t in batch_triples], device=device)
                relations = torch.tensor([t[1] for t in batch_triples], device=device)
                tails = torch.tensor([t[2] for t in batch_triples], device=device)
                
                # 生成负样本
                neg_heads, neg_tails = self._negative_sampling(
                    heads, tails, negative_samples, device
                )
                
                # 计算正样本分数
                pos_score = self.model(heads, relations, tails)
                
                # 计算负样本分数
                neg_score = self.model(neg_heads, relations, neg_tails)
                
                # 计算损失 (margin-based loss)
                loss = F.relu(pos_score - neg_score + 6.0).mean()
                
                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
                
                epoch_loss += loss.item()
            
            avg_loss = epoch_loss / (num_triples // batch_size + 1)
            losses.append(avg_loss)
            
            if (epoch + 1) % 100 == 0:
                logger.info(f"Epoch {epoch+1}/{epochs}, Loss: {avg_loss:.4f}")
        
        return losses
    
    def _negative_sampling(
        self,
        heads: torch.Tensor,
        tails: torch.Tensor,
        negative_samples: int,
        device: str
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """负采样"""
        batch_size = heads.size(0)
        num_entities = len(self.entity2id)
        
        # 50%概率替换头实体，50%概率替换尾实体
        neg_heads = heads.repeat(negative_samples)
        neg_tails = tails.repeat(negative_samples)
        
        for i in range(negative_samples):
            start_idx = i * batch_size
            end_idx = (i + 1) * batch_size
            
            if np.random.random() < 0.5:
                # 替换头实体
                neg_heads[start_idx:end_idx] = torch.randint(
                    0, num_entities, (batch_size,), device=device
                )
            else:
                # 替换尾实体
                neg_tails[start_idx:end_idx] = torch.randint(
                    0, num_entities, (batch_size,), device=device
                )
        
        return neg_heads, neg_tails
    
    def get_concept_embedding(self, concept_id: str) -> Optional[np.ndarray]:
        """获取概念的嵌入向量"""
        if concept_id not in self.entity2id:
            return None
        
        entity_idx = self.entity2id[concept_id]
        return self.model.get_entity_embedding(entity_idx)
    
    def compute_semantic_similarity(self, concept_id1: str, concept_id2: str) -> float:
        """
        计算两个概念的语义相似度
        
        Returns:
            余弦相似度 [-1, 1]
        """
        emb1 = self.get_concept_embedding(concept_id1)
        emb2 = self.get_concept_embedding(concept_id2)
        
        if emb1 is None or emb2 is None:
            return 0.0
        
        # 计算余弦相似度
        dot_product = np.dot(emb1, emb2)
        norm1 = np.linalg.norm(emb1)
        norm2 = np.linalg.norm(emb2)
        
        if norm1 == 0 or norm2 == 0:
            return 0.0
        
        return dot_product / (norm1 * norm2)
    
    def find_similar_concepts(
        self,
        concept_id: str,
        top_k: int = 10,
        exclude_related: bool = True
    ) -> List[Dict[str, Any]]:
        """
        找到与指定概念最相似的概念
        
        Args:
            concept_id: 概念ID
            top_k: 返回数量
            exclude_related: 是否排除直接相关的概念
        
        Returns:
            相似概念列表
        """
        if concept_id not in self.entity2id:
            return []
        
        target_emb = self.get_concept_embedding(concept_id)
        if target_emb is None:
            return []
        
        # 获取直接相关的概念（如果排除）
        related_concepts = set()
        if exclude_related:
            relations = self.db.query(KnowledgeGraphRelation).filter(
                (KnowledgeGraphRelation.source_id == concept_id) |
                (KnowledgeGraphRelation.target_id == concept_id)
            ).all()
            related_concepts = {r.source_id for r in relations} | {r.target_id for r in relations}
        
        # 计算与所有其他概念的相似度
        similarities = []
        for entity_id, entity_idx in self.entity2id.items():
            if entity_id == concept_id or entity_id in related_concepts:
                continue
            
            emb = self.model.get_entity_embedding(entity_idx)
            sim = np.dot(target_emb, emb) / (np.linalg.norm(target_emb) * np.linalg.norm(emb))
            similarities.append((entity_id, float(sim)))
        
        # 排序并返回Top-K
        similarities.sort(key=lambda x: x[1], reverse=True)
        
        # 获取概念详情
        result = []
        for entity_id, sim in similarities[:top_k]:
            node = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == entity_id
            ).first()
            if node:
                result.append({
                    "concept_id": entity_id,
                    "name": node.name,
                    "branch": node.branch,
                    "similarity": sim,
                    "reason": f"知识图谱嵌入相似度: {sim:.3f}"
                })
        
        return result
    
    def recommend_by_knowledge_graph(
        self,
        user_id: int,
        n_recommendations: int = 10
    ) -> List[Dict[str, Any]]:
        """
        基于知识图谱嵌入的推荐
        
        策略：
        1. 获取用户已学习的概念
        2. 找到这些概念的相似概念
        3. 过滤已学习的概念
        4. 按相似度排序
        """
        # 获取用户已学习的概念
        user_progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()
        
        studied_concepts = {p.concept_id for p in user_progress}
        
        if not studied_concepts:
            return []
        
        # 计算推荐分数
        concept_scores = defaultdict(float)
        
        for progress in user_progress:
            concept_id = progress.concept_id
            mastery = progress.mastery_level
            
            # 找到相似概念
            similar = self.find_similar_concepts(concept_id, top_k=20, exclude_related=True)
            
            for sim_concept in similar:
                cid = sim_concept["concept_id"]
                if cid not in studied_concepts:
                    # 权重 = 当前概念掌握程度 * 相似度
                    concept_scores[cid] += mastery * sim_concept["similarity"]
        
        # 排序并返回Top-N
        sorted_concepts = sorted(concept_scores.items(), key=lambda x: x[1], reverse=True)
        
        recommendations = []
        for concept_id, score in sorted_concepts[:n_recommendations]:
            node = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == concept_id
            ).first()
            if node:
                recommendations.append({
                    "concept_id": concept_id,
                    "name": node.name,
                    "branch": node.branch,
                    "score": float(score),
                    "reason": f"基于您已掌握的{node.branch}领域概念推荐"
                })
        
        return recommendations
    
    def save_model(self, path: str):
        """保存模型"""
        if self.model is None:
            raise ValueError("模型未训练")
        
        torch.save({
            "model_state_dict": self.model.state_dict(),
            "entity2id": self.entity2id,
            "relation2id": self.relation2id,
            "model_type": self.model_type,
            "embedding_dim": self.embedding_dim
        }, path)
        logger.info(f"模型已保存到: {path}")
    
    def load_model(self, path: str, device: str = "cpu"):
        """加载模型"""
        checkpoint = torch.load(path, map_location=device)
        
        self.model_type = checkpoint["model_type"]
        self.embedding_dim = checkpoint["embedding_dim"]
        self.entity2id = checkpoint["entity2id"]
        self.relation2id = checkpoint["relation2id"]
        self.id2entity = {v: k for k, v in self.entity2id.items()}
        self.id2relation = {v: k for k, v in self.relation2id.items()}
        
        num_entities = len(self.entity2id)
        num_relations = max(len(self.relation2id), 1)
        
        if self.model_type == "transe":
            self.model = TransE(num_entities, num_relations, self.embedding_dim)
        else:
            self.model = RotatE(num_entities, num_relations, self.embedding_dim)
        
        self.model.load_state_dict(checkpoint["model_state_dict"])
        self.model.to(device)
        self.model.eval()
        
        logger.info(f"模型已从{path}加载")
