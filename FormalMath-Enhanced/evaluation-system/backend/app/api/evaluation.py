"""Evaluation API routes."""
from typing import List, Optional
from datetime import datetime, timedelta

from fastapi import APIRouter, Depends, HTTPException, Query
from sqlalchemy.orm import Session

from app.core.database import get_db
from app.api.schemas import (
    AssessmentRequest, AssessmentResponse,
    ProgressRequest, ProgressResponse,
    ComparisonRequest, ComparisonResponse,
    ReportRequest, ReportResponse,
    FeedbackRequest, FeedbackResponse,
    EvaluationStandardCreate, EvaluationStandardResponse,
    ErrorResponse
)
from app.evaluation.engine import EvaluationEngine
from app.evaluation.feedback import FeedbackEngine
from app.evaluation.report import ReportGenerator
from app.models.evaluation import EvaluationStandard, EvaluationType

router = APIRouter(prefix="/evaluation", tags=["evaluation"])


@router.post("/assess", response_model=AssessmentResponse)
async def create_assessment(
    request: AssessmentRequest,
    db: Session = Depends(get_db)
):
    """Execute comprehensive assessment.
    
    Creates a new evaluation record with five-dimensional scores.
    """
    try:
        engine = EvaluationEngine(db)
        
        scores = {
            'knowledge_mastery': request.scores.knowledge_mastery,
            'problem_solving': request.scores.problem_solving,
            'proof_ability': request.scores.proof_ability,
            'application': request.scores.application,
            'innovation': request.scores.innovation
        }
        
        result = engine.assess(
            user_id=request.user_id,
            assessments=scores,
            evaluation_type=request.evaluation_type,
            period=request.period,
            assessor_id=request.assessor_id,
            notes=request.notes,
            raw_data=request.raw_data
        )
        
        return AssessmentResponse(**result)
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/report/{user_id}", response_model=ReportResponse)
async def get_evaluation_report(
    user_id: str,
    record_id: Optional[str] = None,
    include_history: bool = True,
    db: Session = Depends(get_db)
):
    """Get evaluation report for user.
    
    Returns comprehensive evaluation report including:
    - Executive summary
    - Detailed scores
    - Dimension analysis
    - Strengths and improvements
    - Learning trajectory (if requested)
    """
    try:
        generator = ReportGenerator(db)
        report = generator.generate_json_report(
            user_id=user_id,
            record_id=record_id,
            include_history=include_history
        )
        
        if 'error' in report:
            raise HTTPException(status_code=404, detail=report['error'])
        
        return ReportResponse(**report)
    
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/progress/{user_id}", response_model=ProgressResponse)
async def get_learning_progress(
    user_id: str,
    periods: int = Query(default=6, ge=1, le=24),
    start_date: Optional[str] = None,
    end_date: Optional[str] = None,
    include_growth: bool = True,
    db: Session = Depends(get_db)
):
    """Get learning trajectory/progress for user.
    
    Returns historical assessment data showing progress over time.
    """
    try:
        engine = EvaluationEngine(db)
        
        # Parse dates if provided
        start = None
        end = None
        if start_date:
            start = datetime.fromisoformat(start_date)
        if end_date:
            end = datetime.fromisoformat(end_date)
        
        trajectory = engine.get_learning_trajectory(user_id, start, end)
        
        # Calculate growth analysis
        growth = None
        if include_growth:
            growth = engine.calculate_growth_analysis(user_id, periods)
        
        return ProgressResponse(
            user_id=user_id,
            data_points=len(trajectory),
            trajectory=trajectory,
            growth_analysis=growth
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/feedback", response_model=FeedbackResponse)
async def generate_feedback(
    request: FeedbackRequest,
    db: Session = Depends(get_db)
):
    """Generate personalized feedback.
    
    Creates personalized feedback based on evaluation results including:
    - Strengths identification
    - Areas for improvement
    - Learning suggestions
    - Recommended resources and learning path
    """
    try:
        engine = FeedbackEngine(db)
        result = engine.generate_feedback(
            user_id=request.user_id,
            record_id=request.record_id,
            custom_template=request.custom_template
        )
        
        if 'error' in result:
            raise HTTPException(status_code=404, detail=result['error'])
        
        return FeedbackResponse(**result)
    
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/compare", response_model=ComparisonResponse)
async def compare_to_class(
    request: ComparisonRequest,
    db: Session = Depends(get_db)
):
    """Compare user performance to class average.
    
    Compares user's scores against class average and calculates percentile rank.
    """
    try:
        engine = EvaluationEngine(db)
        result = engine.get_class_comparison(
            user_id=request.user_id,
            class_user_ids=request.class_user_ids
        )
        
        if 'error' in result:
            raise HTTPException(status_code=404, detail=result['error'])
        
        return ComparisonResponse(**result)
    
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


# Additional endpoints

@router.get("/records/{user_id}")
async def get_user_records(
    user_id: str,
    limit: int = Query(default=10, ge=1, le=100),
    db: Session = Depends(get_db)
):
    """Get evaluation records for user."""
    from app.models.evaluation import EvaluationRecord
    
    records = db.query(EvaluationRecord).filter(
        EvaluationRecord.user_id == user_id
    ).order_by(
        EvaluationRecord.created_at.desc()
    ).limit(limit).all()
    
    return {
        'user_id': user_id,
        'count': len(records),
        'records': [
            {
                'record_id': r.record_id,
                'evaluation_type': r.evaluation_type.value,
                'weighted_score': r.weighted_score,
                'grade': 'A' if r.weighted_score >= 90 else 
                        'B' if r.weighted_score >= 80 else
                        'C' if r.weighted_score >= 70 else
                        'D' if r.weighted_score >= 60 else 'F',
                'created_at': r.created_at.isoformat()
            }
            for r in records
        ]
    }


@router.post("/standards", response_model=EvaluationStandardResponse)
async def create_evaluation_standard(
    request: EvaluationStandardCreate,
    db: Session = Depends(get_db)
):
    """Create new evaluation standard/criteria."""
    try:
        standard = EvaluationStandard(
            name=request.name,
            evaluation_type=request.evaluation_type,
            description=request.description,
            criteria=request.criteria,
            scoring_rules=request.scoring_rules,
            dimension_weights=request.dimension_weights
        )
        
        db.add(standard)
        db.commit()
        db.refresh(standard)
        
        return EvaluationStandardResponse(
            id=standard.id,
            name=standard.name,
            evaluation_type=standard.evaluation_type.value,
            description=standard.description,
            criteria=standard.criteria,
            is_active=bool(standard.is_active),
            created_at=standard.created_at
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/standards")
async def list_evaluation_standards(
    evaluation_type: Optional[EvaluationType] = None,
    db: Session = Depends(get_db)
):
    """List evaluation standards."""
    query = db.query(EvaluationStandard)
    
    if evaluation_type:
        query = query.filter(EvaluationStandard.evaluation_type == evaluation_type)
    
    standards = query.filter(EvaluationStandard.is_active == 1).all()
    
    return {
        'count': len(standards),
        'standards': [
            {
                'id': s.id,
                'name': s.name,
                'evaluation_type': s.evaluation_type.value,
                'description': s.description,
                'created_at': s.created_at.isoformat()
            }
            for s in standards
        ]
    }


@router.get("/dimensions")
async def get_assessment_dimensions():
    """Get five-dimensional assessment framework."""
    from app.evaluation.model import EvaluationModel
    
    model = EvaluationModel()
    
    return {
        'dimensions': [
            {
                'key': key,
                'name': model.DIMENSION_NAMES_CN[key],
                'weight': weight,
                'description': {
                    'knowledge_mastery': '对数学概念、定理、公式的理解和掌握程度',
                    'problem_solving': '分析问题、制定策略、解决问题的能力',
                    'proof_ability': '数学证明的逻辑性、严谨性和创造性',
                    'application': '将数学知识应用于实际问题的能力',
                    'innovation': '创造性思维、发散思维和探索精神'
                }[key]
            }
            for key, weight in model.dimensions.items()
        ],
        'total_weight': sum(model.dimensions.values())
    }


@router.get("/statistics/{user_id}")
async def get_user_statistics(
    user_id: str,
    db: Session = Depends(get_db)
):
    """Get comprehensive statistics for user."""
    from app.models.evaluation import EvaluationRecord
    
    records = db.query(EvaluationRecord).filter(
        EvaluationRecord.user_id == user_id
    ).all()
    
    if not records:
        raise HTTPException(status_code=404, detail="No records found")
    
    # Calculate statistics
    scores = {
        'knowledge_mastery': [r.knowledge_mastery for r in records],
        'problem_solving': [r.problem_solving for r in records],
        'proof_ability': [r.proof_ability for r in records],
        'application': [r.application for r in records],
        'innovation': [r.innovation for r in records],
        'weighted': [r.weighted_score for r in records]
    }
    
    import statistics
    
    stats = {}
    for dim, values in scores.items():
        stats[dim] = {
            'count': len(values),
            'mean': round(statistics.mean(values), 2),
            'max': max(values),
            'min': min(values),
            'latest': values[-1] if values else 0
        }
        if len(values) > 1:
            stats[dim]['stdev'] = round(statistics.stdev(values), 2)
    
    return {
        'user_id': user_id,
        'total_evaluations': len(records),
        'date_range': {
            'first': records[0].created_at.isoformat() if records else None,
            'latest': records[-1].created_at.isoformat() if records else None
        },
        'statistics': stats
    }
