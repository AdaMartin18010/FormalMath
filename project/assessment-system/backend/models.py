# -*- coding: utf-8 -*-
"""
models.py - FormalMath 评估系统数据模型

定义评估系统使用的所有数据模型，包括：
- 学习者模型
- 评价记录模型
- 学习行为模型
- 报告模型
"""

from sqlalchemy import (
    create_engine, Column, Integer, String, Float, DateTime, 
    Text, JSON, ForeignKey, Boolean, Enum as SQLEnum, Index
)
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship, sessionmaker
from datetime import datetime
from enum import Enum
import json

Base = declarative_base()


# =============================================================================
# 枚举类型定义
# =============================================================================

class AssessmentType(str, Enum):
    """评估类型"""
    FORMATIVE = "formative"           # 形成性评价
    SUMMATIVE = "summative"           # 总结性评价
    PROCESS = "process"               # 过程性评价
    VALUE_ADDED = "value_added"       # 增值评价
    PERFORMANCE = "performance"       # 表现性评价
    DIVERGENT = "divergent"           # 发散思维评价
    PEER = "peer"                     # 同伴评价
    SELF = "self"                     # 自我评价


class EvaluationLevel(str, Enum):
    """评价等级"""
    BEGINNER = "beginner"             # 初级
    DEVELOPING = "developing"         # 发展中
    PROFICIENT = "proficient"         # 熟练
    ADVANCED = "advanced"             # 高级
    EXPERT = "expert"                 # 专家


class ReportType(str, Enum):
    """报告类型"""
    PROGRESS = "progress"             # 学习进度报告
    ABILITY = "ability"               # 能力评估报告
    VALUE_ADDED = "value_added"       # 增值评价报告
    PERFORMANCE = "performance"       # 表现性评价报告
    COMPREHENSIVE = "comprehensive"   # 综合评价报告
    GROUP_ANALYSIS = "group_analysis" # 群体分析报告


class FeedbackType(str, Enum):
    """反馈类型"""
    REAL_TIME = "real_time"           # 实时反馈
    SUMMARY = "summary"               # 总结反馈
    PROCESS = "process"               # 过程反馈
    VALUE_ADDED = "value_added"       # 增值反馈
    PERFORMANCE = "performance"       # 表现性反馈
    IMPROVEMENT = "improvement"       # 改进建议


class BehaviorType(str, Enum):
    """学习行为类型"""
    CONTENT_VIEW = "content_view"     # 内容查看
    VIDEO_WATCH = "video_watch"       # 视频观看
    EXERCISE_START = "exercise_start" # 练习开始
    EXERCISE_SUBMIT = "exercise_submit"  # 练习提交
    EXERCISE_CORRECT = "exercise_correct"  # 答题正确
    EXERCISE_WRONG = "exercise_wrong"  # 答题错误
    NOTE_CREATE = "note_create"       # 笔记创建
    SEARCH = "search"                 # 搜索
    DISCUSSION = "discussion"         # 讨论参与
    REFLECTION = "reflection"         # 反思记录


# =============================================================================
# 数据模型
# =============================================================================

class Learner(Base):
    """学习者模型"""
    __tablename__ = "learners"
    
    id = Column(String(36), primary_key=True)
    name = Column(String(100), nullable=False)
    email = Column(String(200), unique=True, nullable=True)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 能力档案（JSON格式存储五维能力数据）
    ability_profile = Column(JSON, default=dict)
    initial_ability = Column(JSON, default=dict)
    
    # 知识状态
    knowledge_state = Column(JSON, default=dict)
    
    # 学习偏好设置
    preferences = Column(JSON, default=dict)
    
    # 关系
    evaluation_records = relationship("EvaluationRecord", back_populates="learner")
    behavior_records = relationship("BehaviorRecord", back_populates="learner")
    reports = relationship("Report", back_populates="learner")
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "name": self.name,
            "email": self.email,
            "created_at": self.created_at.isoformat() if self.created_at else None,
            "ability_profile": self.ability_profile,
            "knowledge_state": self.knowledge_state
        }


class EvaluationRecord(Base):
    """评价记录模型"""
    __tablename__ = "evaluation_records"
    
    id = Column(String(36), primary_key=True)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=False)
    assessment_type = Column(SQLEnum(AssessmentType), nullable=False)
    
    # 评价周期
    period_start = Column(DateTime, nullable=True)
    period_end = Column(DateTime, default=datetime.utcnow)
    
    # 评价得分（JSON格式，存储各维度得分）
    scores = Column(JSON, default=dict)
    overall_score = Column(Float, default=0.0)
    level = Column(SQLEnum(EvaluationLevel), nullable=True)
    
    # 详细数据
    details = Column(JSON, default=dict)
    
    # 元数据
    created_at = Column(DateTime, default=datetime.utcnow)
    evaluator_id = Column(String(36), nullable=True)  # 评价者ID（自评时为null）
    evaluator_type = Column(String(20), default="system")  # system, teacher, peer, self
    
    # 索引
    __table_args__ = (
        Index('idx_evaluation_learner', 'learner_id'),
        Index('idx_evaluation_type', 'assessment_type'),
        Index('idx_evaluation_date', 'period_end'),
    )
    
    # 关系
    learner = relationship("Learner", back_populates="evaluation_records")
    feedback = relationship("Feedback", back_populates="evaluation", uselist=False)
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "learner_id": self.learner_id,
            "assessment_type": self.assessment_type.value if self.assessment_type else None,
            "period_start": self.period_start.isoformat() if self.period_start else None,
            "period_end": self.period_end.isoformat() if self.period_end else None,
            "scores": self.scores,
            "overall_score": self.overall_score,
            "level": self.level.value if self.level else None,
            "details": self.details,
            "evaluator_type": self.evaluator_type,
            "created_at": self.created_at.isoformat() if self.created_at else None
        }


class BehaviorRecord(Base):
    """学习行为记录模型"""
    __tablename__ = "behavior_records"
    
    id = Column(String(36), primary_key=True)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=False)
    session_id = Column(String(36), nullable=True)
    
    # 行为类型
    behavior_type = Column(SQLEnum(BehaviorType), nullable=False)
    
    # 时间戳
    timestamp = Column(DateTime, default=datetime.utcnow)
    duration = Column(Integer, default=0)  # 行为持续时长（秒）
    
    # 行为详情（JSON格式）
    metadata = Column(JSON, default=dict)
    
    # 内容信息
    content_id = Column(String(100), nullable=True)
    content_type = Column(String(50), nullable=True)
    
    # 索引
    __table_args__ = (
        Index('idx_behavior_learner', 'learner_id'),
        Index('idx_behavior_type', 'behavior_type'),
        Index('idx_behavior_timestamp', 'timestamp'),
        Index('idx_behavior_session', 'session_id'),
    )
    
    # 关系
    learner = relationship("Learner", back_populates="behavior_records")
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "learner_id": self.learner_id,
            "behavior_type": self.behavior_type.value if self.behavior_type else None,
            "timestamp": self.timestamp.isoformat() if self.timestamp else None,
            "duration": self.duration,
            "content_id": self.content_id,
            "metadata": self.metadata
        }


class Feedback(Base):
    """反馈模型"""
    __tablename__ = "feedbacks"
    
    id = Column(String(36), primary_key=True)
    evaluation_id = Column(String(36), ForeignKey("evaluation_records.id"), nullable=True)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=False)
    
    feedback_type = Column(SQLEnum(FeedbackType), nullable=False)
    priority = Column(String(10), default="medium")  # high, medium, low
    
    # 反馈内容
    title = Column(String(200), nullable=False)
    content = Column(Text, nullable=False)
    suggestions = Column(JSON, default=list)
    resources = Column(JSON, default=list)
    
    # 反馈状态
    is_read = Column(Boolean, default=False)
    read_at = Column(DateTime, nullable=True)
    
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 索引
    __table_args__ = (
        Index('idx_feedback_learner', 'learner_id'),
        Index('idx_feedback_type', 'feedback_type'),
        Index('idx_feedback_read', 'is_read'),
    )
    
    # 关系
    evaluation = relationship("EvaluationRecord", back_populates="feedback")
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "learner_id": self.learner_id,
            "feedback_type": self.feedback_type.value if self.feedback_type else None,
            "priority": self.priority,
            "title": self.title,
            "content": self.content,
            "suggestions": self.suggestions,
            "resources": self.resources,
            "is_read": self.is_read,
            "created_at": self.created_at.isoformat() if self.created_at else None
        }


class Report(Base):
    """报告模型"""
    __tablename__ = "reports"
    
    id = Column(String(36), primary_key=True)
    report_type = Column(SQLEnum(ReportType), nullable=False)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=True)  # 群体报告时为null
    group_id = Column(String(36), nullable=True)  # 群体ID
    
    # 报告周期
    period_start = Column(DateTime, nullable=True)
    period_end = Column(DateTime, nullable=True)
    
    # 报告内容
    title = Column(String(200), nullable=False)
    content = Column(JSON, default=dict)  # 报告内容结构
    summary = Column(Text, nullable=True)
    
    # 文件路径
    file_urls = Column(JSON, default=dict)  # {format: url}
    
    # 元数据
    created_at = Column(DateTime, default=datetime.utcnow)
    generated_by = Column(String(50), default="system")  # system, teacher, etc.
    
    # 索引
    __table_args__ = (
        Index('idx_report_learner', 'learner_id'),
        Index('idx_report_type', 'report_type'),
        Index('idx_report_date', 'created_at'),
    )
    
    # 关系
    learner = relationship("Learner", back_populates="reports")
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "report_type": self.report_type.value if self.report_type else None,
            "learner_id": self.learner_id,
            "group_id": self.group_id,
            "period_start": self.period_start.isoformat() if self.period_start else None,
            "period_end": self.period_end.isoformat() if self.period_end else None,
            "title": self.title,
            "summary": self.summary,
            "file_urls": self.file_urls,
            "created_at": self.created_at.isoformat() if self.created_at else None
        }


class LearningTrajectory(Base):
    """学习轨迹模型"""
    __tablename__ = "learning_trajectories"
    
    id = Column(String(36), primary_key=True)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=False)
    
    # 维度
    dimension = Column(String(50), nullable=False)  # knowledge, skill, problem_solving等
    
    # 数据点
    data_points = Column(JSON, default=list)  # [{date, score, context}]
    
    # 分析结果
    trend_slope = Column(Float, default=0.0)  # 趋势线斜率
    trend_direction = Column(String(20), default="stable")  # up, down, stable
    
    # 预测
    projection = Column(JSON, default=list)  # 未来预测值
    
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 索引
    __table_args__ = (
        Index('idx_trajectory_learner', 'learner_id'),
        Index('idx_trajectory_dimension', 'dimension'),
    )
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "learner_id": self.learner_id,
            "dimension": self.dimension,
            "data_points": self.data_points,
            "trend_slope": self.trend_slope,
            "trend_direction": self.trend_direction,
            "projection": self.projection,
            "updated_at": self.updated_at.isoformat() if self.updated_at else None
        }


class ErrorPattern(Base):
    """错误模式模型"""
    __tablename__ = "error_patterns"
    
    id = Column(String(36), primary_key=True)
    learner_id = Column(String(36), ForeignKey("learners.id"), nullable=False)
    
    # 错误类型
    error_type = Column(String(100), nullable=False)
    concept_id = Column(String(100), nullable=True)  # 相关概念
    
    # 统计
    occurrence_count = Column(Integer, default=1)
    last_occurrence = Column(DateTime, default=datetime.utcnow)
    
    # 详细记录
    error_instances = Column(JSON, default=list)  # 错误实例列表
    
    # 分析
    root_cause = Column(Text, nullable=True)
    suggestions = Column(JSON, default=list)
    
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 索引
    __table_args__ = (
        Index('idx_error_learner', 'learner_id'),
        Index('idx_error_type', 'error_type'),
    )
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "learner_id": self.learner_id,
            "error_type": self.error_type,
            "concept_id": self.concept_id,
            "occurrence_count": self.occurrence_count,
            "root_cause": self.root_cause,
            "suggestions": self.suggestions
        }


class Group(Base):
    """学习群体模型（班级/小组）"""
    __tablename__ = "groups"
    
    id = Column(String(36), primary_key=True)
    name = Column(String(100), nullable=False)
    description = Column(Text, nullable=True)
    group_type = Column(String(50), default="class")  # class, team, etc.
    
    # 成员
    member_ids = Column(JSON, default=list)  # 学习者ID列表
    
    # 统计
    statistics = Column(JSON, default=dict)
    
    created_at = Column(DateTime, default=datetime.utcnow)
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "name": self.name,
            "group_type": self.group_type,
            "member_count": len(self.member_ids) if self.member_ids else 0,
            "created_at": self.created_at.isoformat() if self.created_at else None
        }


# =============================================================================
# 数据库连接和会话管理
# =============================================================================

class DatabaseManager:
    """数据库管理器"""
    
    def __init__(self, database_url: str):
        self.engine = create_engine(database_url, echo=False)
        self.SessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=self.engine)
    
    def create_tables(self):
        """创建所有表"""
        Base.metadata.create_all(bind=self.engine)
    
    def drop_tables(self):
        """删除所有表"""
        Base.metadata.drop_all(bind=self.engine)
    
    def get_session(self):
        """获取数据库会话"""
        return self.SessionLocal()
    
    def close(self):
        """关闭数据库连接"""
        self.engine.dispose()


# 便捷函数
def get_db_session(database_url: str = None):
    """获取数据库会话（用于依赖注入）"""
    if database_url is None:
        database_url = "sqlite:///./assessment.db"  # 默认使用SQLite
    
    db_manager = DatabaseManager(database_url)
    session = db_manager.get_session()
    try:
        yield session
    finally:
        session.close()
