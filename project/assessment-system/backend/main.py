# -*- coding: utf-8 -*-
"""
main.py - FormalMath 评估系统 API 服务

基于 FastAPI 的 RESTful API 服务，提供：
- 学习者管理
- 评价接口
- 反馈接口
- 报告接口
- 数据分析接口
"""

import uuid
import os
from typing import List, Optional, Dict, Any
from datetime import datetime, timedelta
from contextlib import asynccontextmanager

from fastapi import FastAPI, HTTPException, Depends, Query
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field
import uvicorn

# 导入自定义模块
from models import (
    DatabaseManager, Learner, EvaluationRecord, BehaviorRecord,
    Feedback, Report, LearningTrajectory, ErrorPattern, Group,
    AssessmentType, EvaluationLevel, ReportType, FeedbackType, BehaviorType
)
from evaluation_engine import EvaluationSystem, LearningTrajectoryPoint
from feedback_engine import FeedbackSystem
from report_generator import ReportSystem, ReportFormat


# =============================================================================
# 全局配置
# =============================================================================

DATABASE_URL = os.getenv("DATABASE_URL", "sqlite:///./assessment.db")

# 初始化系统组件
db_manager = DatabaseManager(DATABASE_URL)
evaluation_system = EvaluationSystem()
feedback_system = FeedbackSystem()
report_system = ReportSystem()


# =============================================================================
# Pydantic 模型
# =============================================================================

class LearnerCreate(BaseModel):
    """创建学习者请求"""
    name: str = Field(..., min_length=1, max_length=100)
    email: Optional[str] = None


class LearnerResponse(BaseModel):
    """学习者响应"""
    id: str
    name: str
    email: Optional[str]
    created_at: str
    ability_profile: Dict
    knowledge_state: Dict
    
    class Config:
        from_attributes = True


class EvaluationRequest(BaseModel):
    """评价请求"""
    learner_id: str
    assessment_type: str
    scores: Dict[str, float]
    details: Optional[Dict] = None
    evaluator_type: str = "system"  # system, teacher, peer, self


class EvaluationResponse(BaseModel):
    """评价响应"""
    result_id: str
    learner_id: str
    assessment_type: str
    overall_score: float
    level: str
    dimension_scores: Dict
    timestamp: str
    feedback: List[Dict]


class BehaviorRecordRequest(BaseModel):
    """行为记录请求"""
    learner_id: str
    behavior_type: str
    duration: int = 0
    content_id: Optional[str] = None
    metadata: Optional[Dict] = None


class FeedbackResponse(BaseModel):
    """反馈响应"""
    id: str
    type: str
    priority: str
    title: str
    content: str
    suggestions: List[str]
    resources: List[str]
    created_at: str


class ReportRequest(BaseModel):
    """报告请求"""
    learner_id: Optional[str] = None
    group_id: Optional[str] = None
    report_type: str
    period_days: int = 30
    format: str = "json"


class ErrorAnalysisRequest(BaseModel):
    """错误分析请求"""
    learner_id: str
    question_id: str
    user_answer: Any
    correct_answer: Any
    concept_id: str


class RealTimeFeedbackRequest(BaseModel):
    """实时反馈请求"""
    learner_id: str
    consecutive_errors: int = 0
    consecutive_correct: int = 0
    time_spent: int = 0  # 秒
    hint_used: bool = False


# =============================================================================
# 依赖注入
# =============================================================================

def get_db():
    """获取数据库会话"""
    session = db_manager.get_session()
    try:
        yield session
    finally:
        session.close()


# =============================================================================
# FastAPI 应用
# =============================================================================

@asynccontextmanager
async def lifespan(app: FastAPI):
    """应用生命周期管理"""
    # 启动时创建表
    db_manager.create_tables()
    print("✅ 数据库表已创建")
    yield
    # 关闭时清理
    db_manager.close()
    print("👋 数据库连接已关闭")


app = FastAPI(
    title="FormalMath 评估系统 API",
    description="提供多维度学习评估、反馈生成和报告服务",
    version="1.0.0",
    lifespan=lifespan
)

# 配置CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


# =============================================================================
# 学习者管理 API
# =============================================================================

@app.post("/api/v1/learners", response_model=LearnerResponse)
def create_learner(learner: LearnerCreate, db=Depends(get_db)):
    """创建学习者"""
    new_learner = Learner(
        id=str(uuid.uuid4()),
        name=learner.name,
        email=learner.email,
        ability_profile={},
        initial_ability={},
        knowledge_state={},
        preferences={}
    )
    db.add(new_learner)
    db.commit()
    db.refresh(new_learner)
    return new_learner.to_dict()


@app.get("/api/v1/learners/{learner_id}", response_model=LearnerResponse)
def get_learner(learner_id: str, db=Depends(get_db)):
    """获取学习者信息"""
    learner = db.query(Learner).filter(Learner.id == learner_id).first()
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    return learner.to_dict()


@app.put("/api/v1/learners/{learner_id}/ability")
def update_learner_ability(
    learner_id: str,
    ability_data: Dict[str, float],
    db=Depends(get_db)
):
    """更新学习者能力档案"""
    learner = db.query(Learner).filter(Learner.id == learner_id).first()
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    learner.ability_profile = ability_data
    learner.updated_at = datetime.utcnow()
    db.commit()
    
    return {"message": "能力档案已更新", "ability_profile": ability_data}


@app.put("/api/v1/learners/{learner_id}/knowledge")
def update_learner_knowledge(
    learner_id: str,
    knowledge_update: Dict[str, float],
    db=Depends(get_db)
):
    """更新学习者知识状态"""
    learner = db.query(Learner).filter(Learner.id == learner_id).first()
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    if not learner.knowledge_state:
        learner.knowledge_state = {}
    
    learner.knowledge_state.update(knowledge_update)
    learner.updated_at = datetime.utcnow()
    db.commit()
    
    return {"message": "知识状态已更新", "knowledge_state": learner.knowledge_state}


# =============================================================================
# 评价 API
# =============================================================================

@app.post("/api/v1/evaluations/comprehensive", response_model=EvaluationResponse)
def conduct_comprehensive_evaluation(
    request: EvaluationRequest,
    db=Depends(get_db)
):
    """
    进行综合评价
    
    四维评价模型：知识掌握度、技能熟练度、问题解决能力、创新思维能力
    """
    # 验证学习者存在
    learner = db.query(Learner).filter(Learner.id == request.learner_id).first()
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    # 构建评价数据
    eval_data = {
        "knowledge": request.scores.get("knowledge", {}),
        "skill": request.scores.get("skill", {}),
        "problem_solving": request.scores.get("problem_solving", {}),
        "creative": request.scores.get("creative", {})
    }
    
    # 执行评价
    result = evaluation_system.conduct_comprehensive_assessment(
        request.learner_id, eval_data
    )
    
    # 保存评价记录
    record = EvaluationRecord(
        id=result.result_id,
        learner_id=request.learner_id,
        assessment_type=AssessmentType(request.assessment_type),
        overall_score=result.overall_score,
        level=EvaluationLevel(result.level),
        scores={k: v.score for k, v in result.dimension_scores.items()},
        details=result.details,
        evaluator_type=request.evaluator_type
    )
    db.add(record)
    db.commit()
    
    # 生成反馈
    feedback_data = feedback_system.process_evaluation_result(
        request.learner_id, result.to_dict()
    )
    
    # 保存反馈
    for fb in feedback_data.get("feedback_items", []):
        feedback = Feedback(
            id=fb["id"],
            learner_id=request.learner_id,
            evaluation_id=result.result_id,
            feedback_type=FeedbackType(fb["type"]),
            priority=fb["priority"],
            title=fb["title"],
            content=fb["content"],
            suggestions=fb["suggestions"],
            resources=fb["resources"]
        )
        db.add(feedback)
    db.commit()
    
    return {
        **result.to_dict(),
        "feedback": feedback_data.get("feedback_items", [])
    }


@app.post("/api/v1/evaluations/process")
def conduct_process_evaluation(
    learner_id: str,
    period_days: int = 7,
    db=Depends(get_db)
):
    """
    进行过程性评价
    
    基于学习行为数据进行过程性评价
    """
    # 获取学习行为记录
    start_date = datetime.utcnow() - timedelta(days=period_days)
    behaviors = db.query(BehaviorRecord).filter(
        BehaviorRecord.learner_id == learner_id,
        BehaviorRecord.timestamp >= start_date
    ).all()
    
    behavior_records = [b.to_dict() for b in behaviors]
    
    # 执行过程性评价
    result = evaluation_system.conduct_process_assessment(
        learner_id, behavior_records, period_days
    )
    
    # 保存评价记录
    record = EvaluationRecord(
        id=str(uuid.uuid4()),
        learner_id=learner_id,
        assessment_type=AssessmentType.PROCESS,
        overall_score=result["overall_score"],
        level=EvaluationLevel(result["level"]),
        scores={
            "participation": result["participation"],
            "initiative": result["initiative"],
            "consistency": result["consistency"],
            "engagement": result["engagement"]
        },
        details=result["details"]
    )
    db.add(record)
    db.commit()
    
    return result


@app.post("/api/v1/evaluations/value-added")
def conduct_value_added_evaluation(
    learner_id: str,
    period_days: int = 30,
    db=Depends(get_db)
):
    """
    进行增值评价
    
    对比期初和期末数据，计算增值
    """
    # 获取期初和期末的能力数据
    start_date = datetime.utcnow() - timedelta(days=period_days)
    
    records = db.query(EvaluationRecord).filter(
        EvaluationRecord.learner_id == learner_id,
        EvaluationRecord.period_end >= start_date
    ).order_by(EvaluationRecord.period_end).all()
    
    if len(records) < 2:
        raise HTTPException(status_code=400, detail="数据不足，无法计算增值")
    
    baseline = records[0].scores
    current = records[-1].scores
    
    # 计算增值
    result = evaluation_system.conduct_value_added_assessment(
        learner_id, baseline, current
    )
    
    return result.to_dict()


@app.get("/api/v1/evaluations/{learner_id}/history")
def get_evaluation_history(
    learner_id: str,
    assessment_type: Optional[str] = None,
    limit: int = Query(10, ge=1, le=100),
    db=Depends(get_db)
):
    """获取评价历史"""
    query = db.query(EvaluationRecord).filter(
        EvaluationRecord.learner_id == learner_id
    )
    
    if assessment_type:
        query = query.filter(
            EvaluationRecord.assessment_type == AssessmentType(assessment_type)
        )
    
    records = query.order_by(EvaluationRecord.period_end.desc()).limit(limit).all()
    
    return {
        "learner_id": learner_id,
        "count": len(records),
        "records": [r.to_dict() for r in records]
    }


# =============================================================================
# 行为记录 API
# =============================================================================

@app.post("/api/v1/behaviors")
def record_behavior(
    request: BehaviorRecordRequest,
    db=Depends(get_db)
):
    """记录学习行为"""
    # 验证学习者存在
    learner = db.query(Learner).filter(Learner.id == request.learner_id).first()
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    # 创建行为记录
    behavior = BehaviorRecord(
        id=str(uuid.uuid4()),
        learner_id=request.learner_id,
        behavior_type=BehaviorType(request.behavior_type),
        duration=request.duration,
        content_id=request.content_id,
        metadata=request.metadata or {}
    )
    db.add(behavior)
    db.commit()
    
    return {"message": "行为记录已保存", "record_id": behavior.id}


@app.post("/api/v1/behaviors/batch")
def record_behaviors_batch(
    requests: List[BehaviorRecordRequest],
    db=Depends(get_db)
):
    """批量记录学习行为"""
    record_ids = []
    for request in requests:
        behavior = BehaviorRecord(
            id=str(uuid.uuid4()),
            learner_id=request.learner_id,
            behavior_type=BehaviorType(request.behavior_type),
            duration=request.duration,
            content_id=request.content_id,
            metadata=request.metadata or {}
        )
        db.add(behavior)
        record_ids.append(behavior.id)
    
    db.commit()
    return {"message": f"已保存{len(record_ids)}条行为记录", "record_ids": record_ids}


# =============================================================================
# 反馈 API
# =============================================================================

@app.get("/api/v1/feedback/{learner_id}")
def get_feedback(
    learner_id: str,
    unread_only: bool = False,
    limit: int = Query(10, ge=1, le=50),
    db=Depends(get_db)
):
    """获取学习者的反馈"""
    query = db.query(Feedback).filter(Feedback.learner_id == learner_id)
    
    if unread_only:
        query = query.filter(Feedback.is_read == False)
    
    feedbacks = query.order_by(Feedback.created_at.desc()).limit(limit).all()
    
    return {
        "learner_id": learner_id,
        "count": len(feedbacks),
        "feedback": [f.to_dict() for f in feedbacks]
    }


@app.post("/api/v1/feedback/{feedback_id}/read")
def mark_feedback_read(feedback_id: str, db=Depends(get_db)):
    """标记反馈为已读"""
    feedback = db.query(Feedback).filter(Feedback.id == feedback_id).first()
    if not feedback:
        raise HTTPException(status_code=404, detail="反馈不存在")
    
    feedback.is_read = True
    feedback.read_at = datetime.utcnow()
    db.commit()
    
    return {"message": "反馈已标记为已读"}


@app.post("/api/v1/feedback/real-time")
def get_real_time_feedback(request: RealTimeFeedbackRequest):
    """获取实时反馈"""
    interaction_data = {
        "consecutive_errors": request.consecutive_errors,
        "consecutive_correct": request.consecutive_correct,
        "time_spent": request.time_spent,
        "hint_used": request.hint_used
    }
    
    feedback = feedback_system.get_real_time_feedback(
        request.learner_id, interaction_data
    )
    
    if feedback:
        return {"has_feedback": True, "feedback": feedback}
    return {"has_feedback": False}


@app.post("/api/v1/feedback/error-analysis")
def analyze_error(request: ErrorAnalysisRequest, db=Depends(get_db)):
    """分析答题错误"""
    # 获取错误历史
    error_history = db.query(ErrorPattern).filter(
        ErrorPattern.learner_id == request.learner_id,
        ErrorPattern.concept_id == request.concept_id
    ).all()
    
    history_data = [
        {
            "error_type": e.error_type,
            "concept_id": e.concept_id
        }
        for e in error_history
    ]
    
    result = feedback_system.process_error(
        request.learner_id,
        request.question_id,
        request.user_answer,
        request.correct_answer,
        request.concept_id,
        history_data
    )
    
    # 保存错误记录
    error_pattern = ErrorPattern(
        id=str(uuid.uuid4()),
        learner_id=request.learner_id,
        error_type=result["error_analysis"]["error_type"],
        concept_id=request.concept_id,
        occurrence_count=1,
        error_instances=[{
            "question_id": request.question_id,
            "timestamp": datetime.utcnow().isoformat(),
            "user_answer": str(request.user_answer)
        }]
    )
    db.add(error_pattern)
    db.commit()
    
    return result


# =============================================================================
# 报告 API
# =============================================================================

@app.post("/api/v1/reports/generate")
def generate_report(request: ReportRequest, db=Depends(get_db)):
    """生成报告"""
    if request.learner_id:
        # 个人报告
        learner = db.query(Learner).filter(Learner.id == request.learner_id).first()
        if not learner:
            raise HTTPException(status_code=404, detail="学习者不存在")
        
        # 获取评价历史
        start_date = datetime.utcnow() - timedelta(days=request.period_days)
        records = db.query(EvaluationRecord).filter(
            EvaluationRecord.learner_id == request.learner_id,
            EvaluationRecord.period_end >= start_date
        ).all()
        
        # 获取行为摘要
        behaviors = db.query(BehaviorRecord).filter(
            BehaviorRecord.learner_id == request.learner_id,
            BehaviorRecord.timestamp >= start_date
        ).all()
        
        behavior_summary = {
            "total_time": sum(b.duration for b in behaviors),
            "sessions": len(set(b.timestamp.date() for b in behaviors if b.timestamp)),
            "exercises_completed": sum(1 for b in behaviors if b.behavior_type == BehaviorType.EXERCISE_SUBMIT)
        }
        
        report_data = report_system.generate_personal_report(
            learner_id=request.learner_id,
            learner_name=learner.name,
            evaluation_history=[r.to_dict() for r in records],
            current_ability=learner.ability_profile or {},
            knowledge_state=learner.knowledge_state or {},
            behavior_summary=behavior_summary,
            period_days=request.period_days
        )
        
    elif request.group_id:
        # 群体报告
        group = db.query(Group).filter(Group.id == request.group_id).first()
        if not group:
            raise HTTPException(status_code=404, detail="群体不存在")
        
        # 计算群体统计数据
        member_ids = group.member_ids or []
        member_count = len(member_ids)
        
        # 获取成员的评价数据
        aggregate_scores = {}
        distribution = {"expert": 0, "advanced": 0, "proficient": 0, "developing": 0, "beginner": 0}
        
        for member_id in member_ids[:50]:  # 限制处理数量
            learner = db.query(Learner).filter(Learner.id == member_id).first()
            if learner and learner.ability_profile:
                for dim, score in learner.ability_profile.items():
                    if dim not in aggregate_scores:
                        aggregate_scores[dim] = []
                    aggregate_scores[dim].append(score)
        
        # 计算平均值
        for dim, scores in aggregate_scores.items():
            aggregate_scores[dim] = sum(scores) / len(scores) if scores else 0
        
        report_data = report_system.generate_group_report(
            group_id=request.group_id,
            group_name=group.name,
            member_count=member_count,
            aggregate_scores=aggregate_scores,
            distribution=distribution,
            comparison_data={}
        )
    else:
        raise HTTPException(status_code=400, detail="必须指定 learner_id 或 group_id")
    
    # 保存报告记录
    report_record = Report(
        id=report_data["report_id"],
        report_type=ReportType(request.report_type),
        learner_id=request.learner_id,
        group_id=request.group_id,
        title=report_data.get("summary", "评估报告"),
        content=report_data,
        generated_by="system"
    )
    db.add(report_record)
    db.commit()
    
    # 导出为指定格式
    if request.format != "json":
        try:
            format_enum = ReportFormat(request.format)
            exported = report_system.export_report(report_data, format_enum)
            report_data["exported"] = exported
        except ValueError:
            pass
    
    return report_data


@app.get("/api/v1/reports/{report_id}")
def get_report(report_id: str, db=Depends(get_db)):
    """获取报告"""
    report = db.query(Report).filter(Report.id == report_id).first()
    if not report:
        raise HTTPException(status_code=404, detail="报告不存在")
    
    return {
        "report_id": report.id,
        "report_type": report.report_type.value if report.report_type else None,
        "title": report.title,
        "content": report.content,
        "generated_at": report.created_at.isoformat() if report.created_at else None
    }


@app.get("/api/v1/learners/{learner_id}/reports")
def get_learner_reports(
    learner_id: str,
    limit: int = Query(10, ge=1, le=50),
    db=Depends(get_db)
):
    """获取学习者的报告列表"""
    reports = db.query(Report).filter(
        Report.learner_id == learner_id
    ).order_by(Report.created_at.desc()).limit(limit).all()
    
    return {
        "learner_id": learner_id,
        "count": len(reports),
        "reports": [r.to_dict() for r in reports]
    }


# =============================================================================
# 数据分析 API
# =============================================================================

@app.get("/api/v1/analytics/trajectory/{learner_id}")
def analyze_learning_trajectory(
    learner_id: str,
    dimension: str = "overall",
    period_days: int = 90,
    db=Depends(get_db)
):
    """分析学习轨迹"""
    start_date = datetime.utcnow() - timedelta(days=period_days)
    
    records = db.query(EvaluationRecord).filter(
        EvaluationRecord.learner_id == learner_id,
        EvaluationRecord.period_end >= start_date
    ).order_by(EvaluationRecord.period_end).all()
    
    data_points = [
        LearningTrajectoryPoint(
            date=r.period_end,
            score=r.overall_score,
            context=r.assessment_type.value if r.assessment_type else "unknown"
        )
        for r in records
    ]
    
    analysis = evaluation_system.analyze_learning_trajectory(data_points)
    
    return {
        "learner_id": learner_id,
        "dimension": dimension,
        "period_days": period_days,
        "analysis": analysis,
        "data_points": [
            {"date": p.date.isoformat(), "score": p.score, "context": p.context}
            for p in data_points
        ]
    }


@app.get("/api/v1/analytics/errors/{learner_id}")
def get_error_analysis(
    learner_id: str,
    concept_id: Optional[str] = None,
    db=Depends(get_db)
):
    """获取错误分析"""
    query = db.query(ErrorPattern).filter(ErrorPattern.learner_id == learner_id)
    
    if concept_id:
        query = query.filter(ErrorPattern.concept_id == concept_id)
    
    errors = query.order_by(ErrorPattern.occurrence_count.desc()).all()
    
    return {
        "learner_id": learner_id,
        "total_error_types": len(errors),
        "errors": [e.to_dict() for e in errors]
    }


# =============================================================================
# 系统信息 API
# =============================================================================

@app.get("/api/v1/system/info")
def get_system_info():
    """获取系统信息"""
    return {
        "name": "FormalMath 评估系统",
        "version": "1.0.0",
        "features": [
            "多维度评价（知识、技能、问题解决、创新思维）",
            "过程性评价",
            "增值评价",
            "实时反馈",
            "错误分析",
            "学习轨迹追踪",
            "个人/群体报告生成"
        ],
        "assessment_types": [t.value for t in AssessmentType],
        "report_types": [t.value for t in ReportType]
    }


@app.get("/api/v1/system/health")
def health_check():
    """健康检查"""
    return {"status": "healthy", "timestamp": datetime.utcnow().isoformat()}


# =============================================================================
# 主入口
# =============================================================================

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
