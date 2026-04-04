"""
SQLAlchemy数据模型
"""
from datetime import datetime
from enum import Enum as PyEnum
from sqlalchemy import Column, Integer, String, Float, DateTime, Text, ForeignKey, Enum, Boolean, JSON
from sqlalchemy.orm import relationship
from ..core.database import Base


class ConceptDifficulty(str, PyEnum):
    """概念难度级别"""
    BASIC = "basic"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"
    RESEARCH = "research"


class LearningPathStatus(str, PyEnum):
    """学习路径状态"""
    ACTIVE = "active"
    COMPLETED = "completed"
    PAUSED = "paused"
    ABANDONED = "abandoned"


class User(Base):
    """用户表"""
    __tablename__ = "users"
    
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String(100), unique=True, index=True, nullable=False)
    email = Column(String(255), unique=True, index=True, nullable=False)
    hashed_password = Column(String(255), nullable=False)
    is_active = Column(Boolean, default=True)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    learning_paths = relationship("LearningPath", back_populates="user")
    progresses = relationship("UserProgress", back_populates="user")


class KnowledgeGraphNode(Base):
    """知识图谱节点表"""
    __tablename__ = "knowledge_graph_nodes"
    
    id = Column(String(100), primary_key=True, index=True)
    name = Column(String(255), nullable=False)
    branch = Column(String(100), index=True, nullable=False)
    difficulty = Column(Enum(ConceptDifficulty), index=True, nullable=False)
    description = Column(Text)
    prerequisites = Column(JSON, default=list)  # 前置概念ID列表
    metadata = Column(JSON, default=dict)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    outgoing_relations = relationship(
        "KnowledgeGraphRelation",
        foreign_keys="KnowledgeGraphRelation.source_id",
        back_populates="source"
    )
    incoming_relations = relationship(
        "KnowledgeGraphRelation",
        foreign_keys="KnowledgeGraphRelation.target_id",
        back_populates="target"
    )


class KnowledgeGraphRelation(Base):
    """知识图谱关系表"""
    __tablename__ = "knowledge_graph_relations"
    
    id = Column(Integer, primary_key=True, index=True)
    source_id = Column(String(100), ForeignKey("knowledge_graph_nodes.id"), nullable=False)
    target_id = Column(String(100), ForeignKey("knowledge_graph_nodes.id"), nullable=False)
    relation_type = Column(String(50), nullable=False)
    weight = Column(Float, default=1.0)
    description = Column(Text)
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 关系
    source = relationship(
        "KnowledgeGraphNode",
        foreign_keys=[source_id],
        back_populates="outgoing_relations"
    )
    target = relationship(
        "KnowledgeGraphNode",
        foreign_keys=[target_id],
        back_populates="incoming_relations"
    )


class LearningPath(Base):
    """学习路径表"""
    __tablename__ = "learning_paths"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    name = Column(String(255), nullable=False)
    description = Column(Text)
    status = Column(Enum(LearningPathStatus), default=LearningPathStatus.ACTIVE)
    path_data = Column(JSON, nullable=False)  # 路径节点序列
    total_nodes = Column(Integer, default=0)
    completed_nodes = Column(Integer, default=0)
    estimated_duration = Column(Integer)  # 预估学习时间（分钟）
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    completed_at = Column(DateTime)
    
    # 关系
    user = relationship("User", back_populates="learning_paths")


class UserProgress(Base):
    """用户学习进度表"""
    __tablename__ = "user_progresses"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    concept_id = Column(String(100), ForeignKey("knowledge_graph_nodes.id"), nullable=False)
    mastery_level = Column(Float, default=0.0)  # 掌握程度 0-1
    study_time = Column(Integer, default=0)  # 学习时间（分钟）
    attempts = Column(Integer, default=0)
    successes = Column(Integer, default=0)
    last_studied_at = Column(DateTime)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    user = relationship("User", back_populates="progresses")
    concept = relationship("KnowledgeGraphNode")


class CognitiveDiagnosis(Base):
    """认知诊断表"""
    __tablename__ = "cognitive_diagnoses"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    concept_id = Column(String(100), ForeignKey("knowledge_graph_nodes.id"), nullable=False)
    diagnosis_type = Column(String(50), nullable=False)
    result_data = Column(JSON, nullable=False)
    confidence = Column(Float)
    created_at = Column(DateTime, default=datetime.utcnow)


class UserActivity(Base):
    """用户活动记录表"""
    __tablename__ = "user_activities"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    activity_type = Column(String(50), nullable=False)
    resource_type = Column(String(50))
    resource_id = Column(String(100))
    metadata = Column(JSON, default=dict)
    created_at = Column(DateTime, default=datetime.utcnow)


class AsyncTask(Base):
    """异步任务记录表"""
    __tablename__ = "async_tasks"
    
    id = Column(String(36), primary_key=True, index=True)
    task_type = Column(String(50), nullable=False)
    status = Column(String(20), default="pending")  # pending, running, completed, failed
    user_id = Column(Integer, ForeignKey("users.id"))
    input_data = Column(JSON)
    result_data = Column(JSON)
    error_message = Column(Text)
    started_at = Column(DateTime)
    completed_at = Column(DateTime)
    created_at = Column(DateTime, default=datetime.utcnow)
