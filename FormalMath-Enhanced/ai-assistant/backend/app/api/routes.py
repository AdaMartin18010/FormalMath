"""
AI助手API路由
提供问答、概念解释、证明提示、学习建议等接口
"""
from typing import Optional, List, Dict, Any
from datetime import datetime

from fastapi import APIRouter, HTTPException, Depends, Query, BackgroundTasks
from pydantic import BaseModel, Field

from ..services.ai_assistant import get_ai_assistant, AIAssistantService
from ..services.conversation_manager import get_conversation_manager, ConversationManager
from ..llm.client import get_llm_client, LLMConfig, LLMProvider


router = APIRouter(prefix="/ai-assistant", tags=["AI学习助手"])


# ========== 请求/响应模型 ==========

class AskRequest(BaseModel):
    """问答请求"""
    question: str = Field(..., description="用户问题", min_length=1, max_length=2000)
    context_id: Optional[str] = Field(None, description="对话上下文ID")
    user_id: Optional[str] = Field(None, description="用户ID")
    stream: bool = Field(False, description="是否流式响应")


class ExplainRequest(BaseModel):
    """概念解释请求"""
    concept: str = Field(..., description="概念名称", min_length=1, max_length=200)
    level: str = Field("intermediate", description="难度级别: beginner/intermediate/advanced")
    context_id: Optional[str] = Field(None, description="对话上下文ID")


class ProofHintRequest(BaseModel):
    """证明提示请求"""
    theorem: str = Field(..., description="定理或命题", min_length=1, max_length=500)
    user_attempt: Optional[str] = Field(None, description="用户的证明尝试")
    context_id: Optional[str] = Field(None, description="对话上下文ID")


class LearningAdviceRequest(BaseModel):
    """学习建议请求"""
    goal: str = Field(..., description="学习目标", min_length=1, max_length=500)
    user_id: Optional[str] = Field(None, description="用户ID")
    context_id: Optional[str] = Field(None, description="对话上下文ID")


class ProblemSolveRequest(BaseModel):
    """问题解答请求"""
    problem: str = Field(..., description="数学问题", min_length=1, max_length=2000)
    show_steps: bool = Field(True, description="是否展示详细步骤")
    context_id: Optional[str] = Field(None, description="对话上下文ID")


class LeanHelpRequest(BaseModel):
    """Lean帮助请求"""
    statement: str = Field(..., description="数学陈述或代码", min_length=1, max_length=2000)
    context_id: Optional[str] = Field(None, description="对话上下文ID")


class ConversationCreateRequest(BaseModel):
    """创建对话请求"""
    user_id: Optional[str] = Field(None, description="用户ID")
    topic: Optional[str] = Field(None, description="对话主题")
    system_prompt: Optional[str] = Field(None, description="自定义系统提示词")


class FeedbackRequest(BaseModel):
    """反馈请求"""
    response_id: str = Field(..., description="响应ID")
    rating: int = Field(..., description="评分 1-5", ge=1, le=5)
    comment: Optional[str] = Field(None, description="评论")


class AssistantResponse(BaseModel):
    """助手响应"""
    answer: str = Field(..., description="回答内容")
    answer_type: str = Field(..., description="回答类型")
    confidence: float = Field(..., description="置信度")
    context_id: Optional[str] = Field(None, description="对话上下文ID")
    suggestions: List[str] = Field(default_factory=list, description="建议的后续问题")
    references: List[Dict] = Field(default_factory=list, description="参考来源")
    latex_formulas: List[str] = Field(default_factory=list, description="LaTeX公式")
    proof_steps: List[str] = Field(default_factory=list, description="证明步骤")
    timestamp: datetime = Field(default_factory=datetime.now)


# ========== 依赖注入 ==========

def get_assistant() -> AIAssistantService:
    """获取AI助手服务"""
    return get_ai_assistant()

def get_conversation_mgr() -> ConversationManager:
    """获取对话管理器"""
    return get_conversation_manager()


# ========== API端点 ==========

@router.post("/ask", response_model=AssistantResponse, summary="通用问答")
async def ask_question(
    request: AskRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    通用问答接口
    
    自动识别问题类型（概念解释、证明提示、学习建议等）并给出回答
    """
    try:
        # 创建或获取对话上下文
        if not request.context_id:
            session = conversation_mgr.create_session(
                user_id=request.user_id,
                topic="general"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
            # 验证上下文存在
            if not conversation_mgr.get_session(context_id):
                raise HTTPException(status_code=404, detail="对话上下文不存在或已过期")
        
        # 添加用户消息
        conversation_mgr.add_message(context_id, 'user', request.question)
        
        # 调用AI助手
        response = await assistant.ask(
            question=request.question,
            context_id=context_id,
            user_id=request.user_id
        )
        
        # 添加助手响应到对话
        conversation_mgr.add_message(context_id, 'assistant', response.answer)
        
        # 更新对话主题
        if response.answer_type == 'concept' and not conversation_mgr.get_session(context_id).current_topic:
            conversation_mgr.update_topic(context_id, request.question[:50])
        
        return AssistantResponse(
            answer=response.answer,
            answer_type=response.answer_type,
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions,
            references=response.references,
            latex_formulas=response.latex_formulas,
            proof_steps=response.proof_steps
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


@router.post("/explain", response_model=AssistantResponse, summary="概念解释")
async def explain_concept(
    request: ExplainRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    解释数学概念
    
    支持不同难度级别：beginner（入门）、intermediate（中级）、advanced（高级）
    """
    try:
        # 创建或获取对话上下文
        if not request.context_id:
            session = conversation_mgr.create_session(
                topic=f"concept:{request.concept}"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
        
        conversation_mgr.add_message(context_id, 'user', f"请解释概念：{request.concept}")
        
        response = await assistant.explain_concept(
            concept=request.concept,
            level=request.level,
            context_id=context_id
        )
        
        conversation_mgr.add_message(context_id, 'assistant', response.answer)
        
        return AssistantResponse(
            answer=response.answer,
            answer_type='concept',
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions,
            latex_formulas=response.latex_formulas
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


@router.post("/proof-hint", response_model=AssistantResponse, summary="证明提示")
async def get_proof_hint(
    request: ProofHintRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    获取证明提示
    
    帮助学生理解如何证明数学命题，提供启发式指导而非直接答案
    """
    try:
        if not request.context_id:
            session = conversation_mgr.create_session(
                topic=f"proof:{request.theorem[:50]}"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
        
        conversation_mgr.add_message(context_id, 'user', f"需要证明提示：{request.theorem}")
        
        response = await assistant.get_proof_hint(
            theorem=request.theorem,
            user_attempt=request.user_attempt,
            context_id=context_id
        )
        
        conversation_mgr.add_message(context_id, 'assistant', response.answer)
        
        return AssistantResponse(
            answer=response.answer,
            answer_type='proof',
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions,
            proof_steps=response.proof_steps,
            latex_formulas=response.latex_formulas
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


@router.post("/learning-advice", response_model=AssistantResponse, summary="学习建议")
async def get_learning_advice(
    request: LearningAdviceRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    获取个性化学习建议
    
    基于用户的学习目标和当前水平提供学习路径建议
    """
    try:
        if not request.context_id:
            session = conversation_mgr.create_session(
                user_id=request.user_id,
                topic=f"learning:{request.goal[:50]}"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
        
        conversation_mgr.add_message(context_id, 'user', f"学习建议：{request.goal}")
        
        response = await assistant.get_learning_advice(
            goal=request.goal,
            user_id=request.user_id,
            context_id=context_id
        )
        
        conversation_mgr.add_message(context_id, 'assistant', response.answer)
        
        return AssistantResponse(
            answer=response.answer,
            answer_type='advice',
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


@router.post("/solve", response_model=AssistantResponse, summary="问题解答")
async def solve_problem(
    request: ProblemSolveRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    解答数学问题
    
    提供详细的解题步骤和解释
    """
    try:
        if not request.context_id:
            session = conversation_mgr.create_session(
                topic=f"problem:{request.problem[:50]}"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
        
        conversation_mgr.add_message(context_id, 'user', f"求解问题：{request.problem}")
        
        response = await assistant.solve_problem(
            problem=request.problem,
            show_steps=request.show_steps,
            context_id=context_id
        )
        
        conversation_mgr.add_message(context_id, 'assistant', response.answer)
        
        return AssistantResponse(
            answer=response.answer,
            answer_type='problem',
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions,
            latex_formulas=response.latex_formulas
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


@router.post("/lean-help", response_model=AssistantResponse, summary="Lean 4帮助")
async def lean_help(
    request: LeanHelpRequest,
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """
    Lean 4形式化帮助
    
    将数学陈述转换为Lean 4代码，或帮助解决形式化中的问题
    """
    try:
        if not request.context_id:
            session = conversation_mgr.create_session(
                topic="lean"
            )
            context_id = session.session_id
        else:
            context_id = request.context_id
        
        conversation_mgr.add_message(context_id, 'user', f"Lean帮助：{request.statement}")
        
        response = await assistant.help_lean_formalization(
            statement=request.statement,
            context_id=context_id
        )
        
        conversation_mgr.add_message(context_id, 'assistant', response.answer, message_type='code')
        
        return AssistantResponse(
            answer=response.answer,
            answer_type='lean',
            confidence=response.confidence,
            context_id=context_id,
            suggestions=response.suggestions
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"处理请求时出错: {str(e)}")


# ========== 对话管理端点 ==========

@router.post("/conversations", summary="创建对话")
async def create_conversation(
    request: ConversationCreateRequest,
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """创建新的对话会话"""
    session = conversation_mgr.create_session(
        user_id=request.user_id,
        topic=request.topic,
        system_prompt=request.system_prompt
    )
    
    return {
        "session_id": session.session_id,
        "created_at": session.created_at.isoformat(),
        "status": session.status.value
    }


@router.get("/conversations/{session_id}", summary="获取对话")
async def get_conversation(
    session_id: str,
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """获取对话详情"""
    session = conversation_mgr.get_session(session_id)
    
    if not session:
        raise HTTPException(status_code=404, detail="对话不存在或已过期")
    
    return {
        "session_id": session.session_id,
        "created_at": session.created_at.isoformat(),
        "last_activity": session.last_activity.isoformat(),
        "status": session.status.value,
        "current_topic": session.current_topic,
        "messages": [m.to_dict() for m in session.messages],
        "latex_formulas": session.latex_formulas
    }


@router.get("/conversations", summary="列出用户对话")
async def list_conversations(
    user_id: Optional[str] = Query(None, description="用户ID"),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """列出用户的所有对话"""
    if not user_id:
        raise HTTPException(status_code=400, detail="需要提供user_id")
    
    sessions = conversation_mgr.get_user_sessions(user_id)
    return {"sessions": sessions}


@router.delete("/conversations/{session_id}", summary="删除对话")
async def delete_conversation(
    session_id: str,
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """删除对话"""
    conversation_mgr.delete_session(session_id)
    return {"message": "对话已删除"}


# ========== 工具端点 ==========

@router.get("/suggest-questions", summary="获取建议问题")
async def suggest_questions(
    topic: str = Query(..., description="主题"),
    k: int = Query(5, description="数量", ge=1, le=10),
    assistant: AIAssistantService = Depends(get_assistant)
):
    """获取针对主题的建议问题"""
    suggestions = assistant.knowledge.suggest_questions(topic, k)
    return {"topic": topic, "suggestions": suggestions}


@router.post("/feedback", summary="提交反馈")
async def submit_feedback(request: FeedbackRequest):
    """提交对AI回答的反馈"""
    # TODO: 实现反馈存储
    return {"message": "反馈已收到", "response_id": request.response_id}


@router.get("/stats", summary="获取统计信息")
async def get_stats(
    assistant: AIAssistantService = Depends(get_assistant),
    conversation_mgr: ConversationManager = Depends(get_conversation_mgr)
):
    """获取AI助手使用统计"""
    return {
        "assistant_stats": assistant.get_stats(),
        "conversation_stats": conversation_mgr.get_stats()
    }
