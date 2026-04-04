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


# ========== 反馈系统数据模型 ==========

class FeedbackType(str, PyEnum):
    """反馈类型"""
    BUG_REPORT = "bug_report"           # 错误报告
    FEATURE_REQUEST = "feature_request" # 功能请求
    CONTENT_ERROR = "content_error"     # 内容错误
    USABILITY = "usability"             # 可用性问题
    PERFORMANCE = "performance"         # 性能问题
    GENERAL = "general"                 # 一般反馈
    COMPLAINT = "complaint"             # 投诉
    COMPLIMENT = "compliment"           # 表扬


class FeedbackStatus(str, PyEnum):
    """反馈处理状态"""
    PENDING = "pending"                 # 待处理
    CLASSIFIED = "classified"           # 已分类
    UNDER_REVIEW = "under_review"       # 审核中
    IN_PROGRESS = "in_progress"         # 处理中
    RESOLVED = "resolved"               # 已解决
    CLOSED = "closed"                   # 已关闭
    REJECTED = "rejected"               # 已拒绝


class FeedbackPriority(str, PyEnum):
    """反馈优先级"""
    CRITICAL = "critical"               # 紧急
    HIGH = "high"                       # 高
    MEDIUM = "medium"                   # 中
    LOW = "low"                         # 低


class UserFeedback(Base):
    """用户反馈表"""
    __tablename__ = "user_feedbacks"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=True, index=True)  # 可选匿名
    
    # 反馈内容
    title = Column(String(255), nullable=False)
    content = Column(Text, nullable=False)
    feedback_type = Column(Enum(FeedbackType), nullable=False, index=True)
    
    # 自动分类结果
    auto_classified_type = Column(Enum(FeedbackType), nullable=True)
    classification_confidence = Column(Float, default=0.0)
    
    # 处理状态
    status = Column(Enum(FeedbackStatus), default=FeedbackStatus.PENDING, index=True)
    priority = Column(Enum(FeedbackPriority), default=FeedbackPriority.MEDIUM, index=True)
    
    # 关联信息
    related_concept_id = Column(String(100), ForeignKey("knowledge_graph_nodes.id"), nullable=True)
    related_page = Column(String(255), nullable=True)  # 相关页面URL
    screenshot_url = Column(String(500), nullable=True)  # 截图URL
    
    # 元数据
    browser_info = Column(JSON, default=dict)  # 浏览器信息
    device_info = Column(JSON, default=dict)   # 设备信息
    session_id = Column(String(100), nullable=True)
    
    # 评分
    satisfaction_rating = Column(Integer, nullable=True)  # 满意度评分 1-5
    helpfulness_rating = Column(Integer, nullable=True)   # 有用性评分 1-5
    
    # 处理信息
    assigned_to = Column(Integer, ForeignKey("users.id"), nullable=True)  # 分配给
    resolution_notes = Column(Text, nullable=True)
    resolved_at = Column(DateTime, nullable=True)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow, index=True)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    user = relationship("User", foreign_keys=[user_id])
    assigned_user = relationship("User", foreign_keys=[assigned_to])
    related_concept = relationship("KnowledgeGraphNode")
    responses = relationship("FeedbackResponse", back_populates="feedback", cascade="all, delete-orphan")
    processing_logs = relationship("FeedbackProcessingLog", back_populates="feedback", cascade="all, delete-orphan")


class FeedbackResponse(Base):
    """反馈回复表"""
    __tablename__ = "feedback_responses"
    
    id = Column(Integer, primary_key=True, index=True)
    feedback_id = Column(Integer, ForeignKey("user_feedbacks.id"), nullable=False, index=True)
    responder_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    
    # 回复内容
    content = Column(Text, nullable=False)
    is_internal = Column(Boolean, default=False)  # 是否内部备注
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    feedback = relationship("UserFeedback", back_populates="responses")
    responder = relationship("User")


class FeedbackProcessingLog(Base):
    """反馈处理日志表"""
    __tablename__ = "feedback_processing_logs"
    
    id = Column(Integer, primary_key=True, index=True)
    feedback_id = Column(Integer, ForeignKey("user_feedbacks.id"), nullable=False, index=True)
    
    # 处理信息
    action = Column(String(50), nullable=False)  # 操作类型
    old_status = Column(Enum(FeedbackStatus), nullable=True)
    new_status = Column(Enum(FeedbackStatus), nullable=True)
    old_priority = Column(Enum(FeedbackPriority), nullable=True)
    new_priority = Column(Enum(FeedbackPriority), nullable=True)
    
    # 操作人
    performed_by = Column(Integer, ForeignKey("users.id"), nullable=True)
    notes = Column(Text, nullable=True)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 关系
    feedback = relationship("UserFeedback", back_populates="processing_logs")
    user = relationship("User", foreign_keys=[performed_by])


class FeedbackAnalytics(Base):
    """反馈分析统计表"""
    __tablename__ = "feedback_analytics"
    
    id = Column(Integer, primary_key=True, index=True)
    
    # 统计周期
    period_type = Column(String(20), nullable=False, index=True)  # daily, weekly, monthly
    period_start = Column(DateTime, nullable=False, index=True)
    period_end = Column(DateTime, nullable=False)
    
    # 统计数据
    total_feedbacks = Column(Integer, default=0)
    feedbacks_by_type = Column(JSON, default=dict)  # 各类型数量
    feedbacks_by_status = Column(JSON, default=dict)  # 各状态数量
    feedbacks_by_priority = Column(JSON, default=dict)  # 各优先级数量
    
    # 处理效率
    avg_resolution_time_hours = Column(Float, default=0.0)  # 平均解决时间
    resolved_count = Column(Integer, default=0)
    pending_count = Column(Integer, default=0)
    
    # 满意度
    avg_satisfaction = Column(Float, default=0.0)
    satisfaction_distribution = Column(JSON, default=dict)
    
    # 热门标签/关键词
    top_keywords = Column(JSON, default=list)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
