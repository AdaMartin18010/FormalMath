"""
诊断相关API路由
"""
from fastapi import APIRouter, Depends, HTTPException, BackgroundTasks
from typing import List, Optional
from sqlalchemy.orm import Session
import uuid
from datetime import datetime

from app.models.database import get_db
from app.models.schemas import (
    StartDiagnosisRequest, StartDiagnosisResponse,
    SubmitAnswersRequest, SubmitAnswersResponse,
    DiagnosisResultResponse, APIResponse,
    QuestionDetail
)
from app.services.question_bank import question_bank
from app.services.hcd_algorithm import HCDAlgorithm, build_default_knowledge_graph, Question as HCDQuestion

router = APIRouter(prefix="/diagnosis", tags=["诊断"])

# 初始化HCD算法
hcd_algorithm = HCDAlgorithm(build_default_knowledge_graph())


@router.post("/start", response_model=APIResponse)
async def start_diagnosis(
    request: StartDiagnosisRequest,
    background_tasks: BackgroundTasks,
    db: Session = Depends(get_db)
):
    """
    开始认知诊断测试
    
    根据学生信息和目标层次，生成个性化测试题目
    """
    try:
        # 生成测试ID
        test_id = str(uuid.uuid4())
        
        # 获取诊断题目
        questions = question_bank.get_diagnostic_questions(
            target_level=request.target_level.value if request.target_level else None,
            count=request.question_count
        )
        
        if not questions:
            raise HTTPException(status_code=404, detail="无法生成题目")
        
        # 转换题目格式
        question_details = [QuestionDetail(**q) for q in questions]
        
        # 计算时间限制（每题平均2分钟）
        time_limit = sum(q.get('time_estimate', 120) for q in questions)
        
        # TODO: 保存测试记录到数据库
        
        response = StartDiagnosisResponse(
            test_id=test_id,
            questions=question_details,
            time_limit=time_limit
        )
        
        return APIResponse(
            success=True,
            message="诊断测试已创建",
            data=response.dict()
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/submit", response_model=APIResponse)
async def submit_answers(
    request: SubmitAnswersRequest,
    background_tasks: BackgroundTasks,
    db: Session = Depends(get_db)
):
    """
    提交答案并获取诊断结果
    
    提交答题结果，系统将自动评分并生成诊断报告
    """
    try:
        # 处理每道题的答案
        responses = []
        correct_count = 0
        
        for ans in request.responses:
            # 检查答案
            result = question_bank.check_answer(ans.question_id, ans.answer)
            
            responses.append({
                'question_id': ans.question_id,
                'is_correct': 1 if result.get('correct') else 0,
                'time_spent': ans.time_spent
            })
            
            if result.get('correct'):
                correct_count += 1
        
        # TODO: 保存答题记录到数据库
        
        return APIResponse(
            success=True,
            message="答案已提交",
            data=SubmitAnswersResponse(
                test_id=request.test_id,
                status="completed",
                completed_count=len(request.responses),
                total_count=len(request.responses),
                message=f"测试完成！答对 {correct_count}/{len(request.responses)} 题"
            ).dict()
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/analyze/{test_id}", response_model=APIResponse)
async def analyze_diagnosis(
    test_id: str,
    background_tasks: BackgroundTasks,
    db: Session = Depends(get_db)
):
    """
    分析诊断结果
    
    对测试数据进行认知诊断分析，生成详细报告
    """
    try:
        # TODO: 从数据库获取答题记录
        # 这里使用模拟数据
        mock_responses = [
            {'question_id': 'Q001', 'is_correct': 1},
            {'question_id': 'Q002', 'is_correct': 1},
            {'question_id': 'Q003', 'is_correct': 0},
            {'question_id': 'Q004', 'is_correct': 1},
            {'question_id': 'Q005', 'is_correct': 0},
        ]
        
        mock_questions = [
            HCDQuestion('Q001', 'SC', 0, 0.3, '基础', ['set_basic']),
            HCDQuestion('Q002', 'SC', 0, 0.3, '基础', ['func_basic']),
            HCDQuestion('Q003', 'SC', 1, 0.5, '基础', ['set_def']),
            HCDQuestion('Q004', 'SC', 1, 0.5, '基础', ['limit_def']),
            HCDQuestion('Q005', 'SC', 2, 0.7, '基础', ['cont_theory']),
        ]
        
        # 执行HCD诊断
        result = hcd_algorithm.diagnose(
            responses=mock_responses,
            questions=mock_questions,
            student_id="student_001"
        )
        
        # 构建响应
        ability_info = {}
        for level, info in result.ability_level.items():
            ability_info[level] = {
                'score': info['score'],
                'level': info['level'],
                'description': info['description'],
                'concept_count': info.get('concept_count', 0),
                'mastered_concepts': info.get('mastered_concepts', 0)
            }
        
        knowledge_state = {}
        for concept, level in result.knowledge_state.items():
            knowledge_state[concept] = {
                'level': level,
                'confidence': result.knowledge_confidence.get(concept, 0.5)
            }
        
        response = DiagnosisResultResponse(
            test_id=test_id,
            student_id=result.student_id,
            knowledge_state=knowledge_state,
            ability_level=ability_info,
            weak_areas=result.weak_areas,
            strong_areas=result.strong_areas,
            suggestions=result.suggestions,
            report_summary=f"诊断完成。整体置信度: {result.overall_confidence:.1%}",
            overall_confidence=result.overall_confidence,
            created_at=datetime.fromisoformat(result.diagnosis_timestamp.replace('Z', '+00:00'))
        )
        
        # TODO: 保存诊断结果到数据库
        
        return APIResponse(
            success=True,
            message="诊断分析完成",
            data=response.dict()
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/result/{test_id}", response_model=APIResponse)
async def get_diagnosis_result(
    test_id: str,
    db: Session = Depends(get_db)
):
    """
    获取诊断结果
    
    获取指定测试的诊断报告
    """
    try:
        # TODO: 从数据库获取诊断结果
        
        # 返回模拟数据
        mock_result = {
            "test_id": test_id,
            "student_id": "student_001",
            "knowledge_state": {
                "set_basic": {"level": 0.92, "confidence": 0.85},
                "func_basic": {"level": 0.88, "confidence": 0.80},
                "limit_basic": {"level": 0.75, "confidence": 0.75}
            },
            "ability_level": {
                "L0": {"score": 0.92, "level": "advanced", "description": "高级"},
                "L1": {"score": 0.78, "level": "intermediate", "description": "中级"},
                "L2": {"score": 0.62, "level": "developing", "description": "发展中"},
                "L3": {"score": 0.35, "level": "beginner", "description": "初学者"}
            },
            "weak_areas": [
                {"concept_id": "galois_theory", "concept_name": "Galois理论", "current_level": 0.25, "target_level": 0.7, "improvement_needed": 0.45}
            ],
            "strong_areas": [
                {"concept_id": "set_basic", "concept_name": "集合基础", "current_level": 0.92}
            ],
            "suggestions": [
                {"type": "foundation", "priority": 1, "title": "加强基础概念学习", "description": "建议先巩固基础知识"}
            ],
            "report_summary": "诊断完成。整体水平：L2 (62%)",
            "overall_confidence": 0.85,
            "created_at": datetime.now().isoformat()
        }
        
        return APIResponse(
            success=True,
            message="获取诊断结果成功",
            data=mock_result
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/questions", response_model=APIResponse)
async def get_questions(
    level: Optional[int] = None,
    branch: Optional[str] = None,
    limit: int = 20,
    db: Session = Depends(get_db)
):
    """
    获取题目列表
    
    可按层次、分支筛选题目
    """
    try:
        questions = question_bank.get_questions(
            level=level,
            branch=branch,
            count=limit
        )
        
        return APIResponse(
            success=True,
            message=f"获取了 {len(questions)} 道题目",
            data={
                "total": len(questions),
                "questions": questions
            }
        )
    
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
