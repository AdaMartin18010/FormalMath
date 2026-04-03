"""
题目API路由
"""

from typing import List, Optional
from fastapi import APIRouter, HTTPException, Query, Depends
from pydantic import BaseModel

from app.models.question import Question, QuestionType, KnowledgeLevel
from app.services.question_service import QuestionService


router = APIRouter()


class QuestionsResponse(BaseModel):
    """题目列表响应"""
    success: bool
    data: List[dict]
    total: int


def get_question_service():
    return QuestionService()


@router.get("/", response_model=QuestionsResponse)
async def get_questions(
    level: Optional[int] = Query(None, ge=0, le=3, description="知识层次"),
    question_type: Optional[QuestionType] = Query(None, description="题目类型"),
    knowledge_tag: Optional[str] = Query(None, description="知识点标签"),
    limit: int = Query(20, ge=1, le=100),
    offset: int = Query(0, ge=0),
    service: QuestionService = Depends(get_question_service)
):
    """
    获取题目列表
    
    - **level**: 知识层次 (0-3)
    - **question_type**: 题目类型
    - **knowledge_tag**: 知识点标签
    - **limit**: 每页数量
    - **offset**: 偏移量
    """
    try:
        questions = service.get_questions(
            level=level,
            question_type=question_type,
            knowledge_tag=knowledge_tag,
            limit=limit,
            offset=offset
        )
        
        total = service.count_questions(
            level=level,
            question_type=question_type,
            knowledge_tag=knowledge_tag
        )
        
        return QuestionsResponse(
            success=True,
            data=[q.model_dump() for q in questions],
            total=total
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/{question_id}")
async def get_question(
    question_id: str,
    service: QuestionService = Depends(get_question_service)
):
    """获取单个题目详情"""
    try:
        question = service.get_question_by_id(question_id)
        if not question:
            raise HTTPException(status_code=404, detail="题目不存在")
        
        return {
            "success": True,
            "data": question.model_dump()
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/random", response_model=QuestionsResponse)
async def get_random_questions(
    count: int = Query(10, ge=1, le=50),
    level: Optional[int] = Query(None, ge=0, le=3),
    service: QuestionService = Depends(get_question_service)
):
    """获取随机题目"""
    try:
        questions = service.get_random_questions(count=count, level=level)
        
        return QuestionsResponse(
            success=True,
            data=[q.model_dump() for q in questions],
            total=len(questions)
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/knowledge-tags")
async def get_knowledge_tags(
    level: Optional[int] = Query(None, ge=0, le=3),
    service: QuestionService = Depends(get_question_service)
):
    """获取知识点标签列表"""
    try:
        tags = service.get_knowledge_tags(level=level)
        
        return {
            "success": True,
            "data": [tag.model_dump() for tag in tags]
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
