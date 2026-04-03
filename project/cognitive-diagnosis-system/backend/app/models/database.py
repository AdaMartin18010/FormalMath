"""
SQLAlchemy数据库模型
"""
from sqlalchemy import create_engine, Column, String, Integer, Float, Boolean, DateTime, Text, JSON, ForeignKey, Table
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import sessionmaker, relationship
from datetime import datetime

from app.core.config import settings

# 创建引擎
engine = create_engine(
    settings.DATABASE_URL,
    pool_size=settings.DATABASE_POOL_SIZE,
    max_overflow=settings.DATABASE_MAX_OVERFLOW,
    pool_pre_ping=True
)

SessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=engine)
Base = declarative_base()


# 关联表：测试与题目的多对多关系
test_questions = Table(
    'test_questions',
    Base.metadata,
    Column('test_id', String(36), ForeignKey('tests.id')),
    Column('question_id', String(36), ForeignKey('questions.id'))
)


class Student(Base):
    """学生表"""
    __tablename__ = "students"
    
    id = Column(String(36), primary_key=True)
    username = Column(String(50), nullable=False, index=True)
    email = Column(String(100), unique=True, index=True)
    hashed_password = Column(String(255))
    current_level = Column(Integer, default=0)  # L0-L3
    learning_style = Column(String(20))
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关联
    tests = relationship("Test", back_populates="student")
    diagnoses = relationship("DiagnosisResult", back_populates="student")


class Question(Base):
    """题目表"""
    __tablename__ = "questions"
    
    id = Column(String(36), primary_key=True)
    content = Column(Text, nullable=False)
    type = Column(String(10), nullable=False)  # SC/MC/FB/SA/PR
    level = Column(Integer, nullable=False)  # 0-3
    difficulty = Column(Integer, nullable=False)  # 1-5
    branch = Column(String(50))  # 代数学/分析学/几何与拓扑/数学基础
    concepts = Column(JSON)  # 关联知识点
    skills = Column(JSON)  # 考察技能
    options = Column(JSON)  # 选项(选择题)
    answer = Column(Text)  # 正确答案
    explanation = Column(Text)  # 解析
    time_estimate = Column(Integer)  # 预估用时(秒)
    score = Column(Float)  # 分值
    prerequisite_concepts = Column(JSON)  # 先修知识点
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 关联
    responses = relationship("Response", back_populates="question")


class Test(Base):
    """测试记录表"""
    __tablename__ = "tests"
    
    id = Column(String(36), primary_key=True)
    student_id = Column(String(36), ForeignKey("students.id"))
    test_type = Column(String(20))  # diagnostic/practice/exam
    status = Column(String(20), default="pending")  # pending/completed/aborted
    start_time = Column(DateTime)
    end_time = Column(DateTime)
    total_score = Column(Float)
    target_level = Column(Integer)  # 目标层次
    focus_areas = Column(JSON)  # 重点领域
    
    # 关联
    student = relationship("Student", back_populates="tests")
    responses = relationship("Response", back_populates="test")
    diagnosis = relationship("DiagnosisResult", back_populates="test", uselist=False)


class Response(Base):
    """答题记录表"""
    __tablename__ = "responses"
    
    id = Column(String(36), primary_key=True)
    test_id = Column(String(36), ForeignKey("tests.id"))
    question_id = Column(String(36), ForeignKey("questions.id"))
    answer = Column(Text)  # 学生答案
    is_correct = Column(Boolean)
    score = Column(Float)
    time_spent = Column(Integer)  # 用时(秒)
    
    # 关联
    test = relationship("Test", back_populates="responses")
    question = relationship("Question", back_populates="responses")


class DiagnosisResult(Base):
    """诊断结果表"""
    __tablename__ = "diagnosis_results"
    
    id = Column(String(36), primary_key=True)
    student_id = Column(String(36), ForeignKey("students.id"))
    test_id = Column(String(36), ForeignKey("tests.id"))
    knowledge_state = Column(JSON)  # 知识状态
    ability_level = Column(JSON)  # 能力水平
    weak_areas = Column(JSON)  # 薄弱环节
    strong_areas = Column(JSON)  # 优势领域
    suggestions = Column(JSON)  # 学习建议
    confidence = Column(Float)  # 诊断置信度
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 关联
    student = relationship("Student", back_populates="diagnoses")
    test = relationship("Test", back_populates="diagnosis")


class LearningPath(Base):
    """学习路径表"""
    __tablename__ = "learning_paths"
    
    id = Column(String(36), primary_key=True)
    student_id = Column(String(36), ForeignKey("students.id"))
    diagnosis_id = Column(String(36), ForeignKey("diagnosis_results.id"))
    path_data = Column(JSON)  # 学习路径数据
    current_node = Column(String(36))  # 当前学习节点
    progress = Column(Float, default=0.0)  # 进度
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)


# 数据库会话依赖
def get_db():
    """获取数据库会话"""
    db = SessionLocal()
    try:
        yield db
    finally:
        db.close()
