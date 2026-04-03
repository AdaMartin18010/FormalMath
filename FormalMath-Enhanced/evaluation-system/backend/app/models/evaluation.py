"""Evaluation database models."""
from datetime import datetime
from sqlalchemy import Column, Integer, String, Float, DateTime, Text, JSON, ForeignKey, Enum
from sqlalchemy.orm import relationship
import enum

from app.core.database import Base


class EvaluationType(str, enum.Enum):
    """Evaluation types."""
    PROCESS = "process"           # 过程性评价
    VALUE_ADDED = "value_added"   # 增值评价
    PERFORMANCE = "performance"   # 表现性评价
    DIVERGENT = "divergent"       # 发散思维评价
    COMPREHENSIVE = "comprehensive"  # 综合评价


class AssessmentDimension(Base):
    """Assessment dimension model."""
    __tablename__ = "assessment_dimensions"
    
    id = Column(Integer, primary_key=True, index=True)
    name = Column(String(100), nullable=False, unique=True)
    name_cn = Column(String(100), nullable=False)
    weight = Column(Float, nullable=False, default=0.2)
    description = Column(Text)
    indicators = Column(JSON)  # 评价指标详情
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)


class EvaluationStandard(Base):
    """Evaluation standard/criteria model."""
    __tablename__ = "evaluation_standards"
    
    id = Column(Integer, primary_key=True, index=True)
    name = Column(String(200), nullable=False)
    evaluation_type = Column(Enum(EvaluationType), nullable=False)
    description = Column(Text)
    criteria = Column(JSON, nullable=False)  # 评价标准详情
    scoring_rules = Column(JSON)  # 评分规则
    dimension_weights = Column(JSON)  # 各维度权重
    is_active = Column(Integer, default=1)
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    records = relationship("EvaluationRecord", back_populates="standard")


class EvaluationRecord(Base):
    """Evaluation record model."""
    __tablename__ = "evaluation_records"
    
    id = Column(Integer, primary_key=True, index=True)
    record_id = Column(String(50), unique=True, index=True)
    user_id = Column(String(50), nullable=False, index=True)
    standard_id = Column(Integer, ForeignKey("evaluation_standards.id"))
    evaluation_type = Column(Enum(EvaluationType), nullable=False)
    
    # 五维评分
    knowledge_mastery = Column(Float, default=0.0)  # 知识掌握度
    problem_solving = Column(Float, default=0.0)    # 问题解决能力
    proof_ability = Column(Float, default=0.0)      # 证明能力
    application = Column(Float, default=0.0)        # 应用能力
    innovation = Column(Float, default=0.0)         # 创新思维
    
    total_score = Column(Float, default=0.0)        # 总分
    weighted_score = Column(Float, default=0.0)     # 加权分
    
    # 详细数据
    raw_data = Column(JSON)  # 原始评估数据
    dimension_scores = Column(JSON)  # 各维度详细得分
    
    # 元数据
    assessor_id = Column(String(50))
    assessment_period = Column(String(50))  # 评估周期
    notes = Column(Text)
    
    created_at = Column(DateTime, default=datetime.utcnow)
    
    standard = relationship("EvaluationStandard", back_populates="records")
    feedback = relationship("FeedbackTemplate", back_populates="evaluation", uselist=False)


class LearningTrajectory(Base):
    """Learning trajectory/history model."""
    __tablename__ = "learning_trajectories"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(String(50), nullable=False, index=True)
    
    # 时间点数据
    record_date = Column(DateTime, nullable=False)
    period = Column(String(50))  # 周期标识
    
    # 各维度历史分数
    knowledge_mastery = Column(Float, default=0.0)
    problem_solving = Column(Float, default=0.0)
    proof_ability = Column(Float, default=0.0)
    application = Column(Float, default=0.0)
    innovation = Column(Float, default=0.0)
    
    # 增值数据
    value_added = Column(JSON)  # 增值数据
    growth_rate = Column(JSON)  # 增长率
    
    # 学习行为数据
    learning_time = Column(Float, default=0.0)  # 学习时长(小时)
    completion_rate = Column(Float, default=0.0)  # 完成率
    engagement_score = Column(Float, default=0.0)  # 参与度
    
    # 元数据
    metadata = Column(JSON)
    created_at = Column(DateTime, default=datetime.utcnow)


class FeedbackTemplate(Base):
    """Feedback template model."""
    __tablename__ = "feedback_templates"
    
    id = Column(Integer, primary_key=True, index=True)
    feedback_id = Column(String(50), unique=True, index=True)
    evaluation_id = Column(Integer, ForeignKey("evaluation_records.id"))
    user_id = Column(String(50), nullable=False)
    
    # 反馈内容
    summary = Column(Text)  # 总体评价
    strengths = Column(JSON)  # 优势
    weaknesses = Column(JSON)  # 待改进
    suggestions = Column(JSON)  # 建议
    
    # 各维度反馈
    dimension_feedback = Column(JSON)
    
    # 学习路径推荐
    recommended_resources = Column(JSON)
    recommended_path = Column(JSON)
    
    # 生成信息
    generated_by = Column(String(50))  # 生成方式: auto/manual
    template_used = Column(String(100))
    
    created_at = Column(DateTime, default=datetime.utcnow)
    
    evaluation = relationship("EvaluationRecord", back_populates="feedback")
