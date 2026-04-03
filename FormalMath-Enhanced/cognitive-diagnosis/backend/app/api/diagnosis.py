"""
诊断API路由
"""

from typing import List, Optional
from fastapi import APIRouter, HTTPException, Depends
from pydantic import BaseModel, Field

from app.models.diagnosis import DiagnosisSession, DiagnosisResponse, DiagnosisReport
from app.services.diagnosis_service import DiagnosisService


router = APIRouter()


# 请求/响应模型
class StartDiagnosisRequest(BaseModel):
    """开始诊断请求"""
    user_id: str = Field(..., description="用户ID")
    question_count: int = Field(20, ge=5, le=50, description="题目数量")
    target_levels: Optional[List[int]] = Field(None, description="目标层次")


class SubmitAnswerRequest(BaseModel):
    """提交答案请求"""
    session_id: str = Field(..., description="诊断会话ID")
    question_id: str = Field(..., description="题目ID")
    answer: any = Field(..., description="用户答案")
    time_spent: int = Field(..., ge=0, description="答题用时(秒)")
    confidence: Optional[float] = Field(None, ge=0.0, le=1.0, description="置信度")


class DiagnosisResponseModel(BaseModel):
    """诊断响应模型"""
    success: bool
    data: dict
    message: str


# 依赖注入
def get_diagnosis_service():
    return DiagnosisService()


@router.post("/start", response_model=DiagnosisResponseModel)
async def start_diagnosis(
    request: StartDiagnosisRequest,
    service: DiagnosisService = Depends(get_diagnosis_service)
):
    """
    开始新的诊断会话
    
    - **user_id**: 用户ID
    - **question_count**: 题目数量 (5-50)
    - **target_levels**: 目标层次 [0,1,2,3]
    """
    try:
        session = service.start_diagnosis(
            user_id=request.user_id,
            question_count=request.question_count,
            target_levels=request.target_levels
        )
        
        return DiagnosisResponseModel(
            success=True,
            data={
                "session_id": session.id,
                "question_count": session.question_count,
                "time_limit": session.time_limit,
                "first_question": service.get_current_question(session.id)
            },
            message="诊断会话创建成功"
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/submit", response_model=DiagnosisResponseModel)
async def submit_answer(
    request: SubmitAnswerRequest,
    service: DiagnosisService = Depends(get_diagnosis_service)
):
    """
    提交答案
    
    - **session_id**: 诊断会话ID
    - **question_id**: 题目ID
    - **answer**: 用户答案
    - **time_spent**: 答题用时(秒)
    - **confidence**: 置信度 (可选)
    """
    try:
        result = service.submit_answer(
            session_id=request.session_id,
            question_id=request.question_id,
            answer=request.answer,
            time_spent=request.time_spent,
            confidence=request.confidence
        )
        
        if not result["success"]:
            raise HTTPException(status_code=400, detail=result["message"])
        
        response_data = {
            "is_correct": result["is_correct"],
            "score": result["score"],
            "progress": result["progress"],
        }
        
        # 如果还有下一题
        if result.get("next_question"):
            response_data["next_question"] = result["next_question"]
        else:
            # 诊断完成
            response_data["completed"] = True
            response_data["report_id"] = result.get("report_id")
        
        return DiagnosisResponseModel(
            success=True,
            data=response_data,
            message="答案提交成功" if not result.get("completed") else "诊断完成"
        )
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/session/{session_id}")
async def get_session_status(
    session_id: str,
    service: DiagnosisService = Depends(get_diagnosis_service)
):
    """获取诊断会话状态"""
    try:
        session = service.get_session(session_id)
        if not session:
            raise HTTPException(status_code=404, detail="诊断会话不存在")
        
        return DiagnosisResponseModel(
            success=True,
            data={
                "session_id": session.id,
                "status": session.status,
                "progress": {
                    "current": session.current_question_index,
                    "total": len(session.question_ids)
                },
                "answered_count": len(session.responses)
            },
            message="获取成功"
        )
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/complete/{session_id}")
async def complete_diagnosis(
    session_id: str,
    service: DiagnosisService = Depends(get_diagnosis_service)
):
    """
    手动完成诊断（生成报告）
    
    通常当用户完成所有题目后会自动生成报告，
    此接口用于用户主动结束诊断时生成报告
    """
    try:
        result = service.complete_diagnosis(session_id)
        
        if not result["success"]:
            raise HTTPException(status_code=400, detail=result["message"])
        
        return DiagnosisResponseModel(
            success=True,
            data={
                "report_id": result["report_id"],
                "summary": result["summary"]
            },
            message="诊断完成，报告已生成"
        )
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
