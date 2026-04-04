"""
搜索API路由
提供语义搜索、公式搜索、问答等功能
"""
from typing import List, Dict, Optional, Any
from fastapi import APIRouter, Depends, HTTPException, Query, Body
from pydantic import BaseModel, Field

from ..services.semantic_search_service import (
    SemanticSearchService, 
    get_semantic_search_service,
    SearchRequest
)

router = APIRouter()


# ========== 请求/响应模型 ==========

class SearchQuery(BaseModel):
    """搜索查询"""
    query: str = Field(..., description="搜索查询文本", min_length=1, max_length=1000)
    search_type: str = Field("hybrid", description="搜索类型: semantic, keyword, hybrid, formula")
    k: int = Field(10, description="返回结果数量", ge=1, le=100)
    rerank: bool = Field(True, description="是否启用重排序")
    filter_metadata: Optional[Dict[str, Any]] = Field(None, description="元数据过滤条件")


class IndexDocumentRequest(BaseModel):
    """索引文档请求"""
    doc_id: str = Field(..., description="文档ID")
    content: str = Field(..., description="文档内容", min_length=1)
    metadata: Optional[Dict[str, Any]] = Field(None, description="文档元数据")
    index_formulas: bool = Field(True, description="是否索引公式")


class IndexBatchRequest(BaseModel):
    """批量索引请求"""
    documents: List[Dict[str, Any]] = Field(..., description="文档列表")


class FormulaSearchQuery(BaseModel):
    """公式搜索查询"""
    latex: str = Field(..., description="LaTeX公式", min_length=1)
    k: int = Field(10, description="返回结果数量", ge=1, le=50)
    match_type: str = Field("all", description="匹配类型: all, exact, structural, variable_independent")


class FormulaCompareRequest(BaseModel):
    """公式比较请求"""
    latex1: str = Field(..., description="第一个LaTeX公式")
    latex2: str = Field(..., description="第二个LaTeX公式")


class QuestionRequest(BaseModel):
    """问答请求"""
    question: str = Field(..., description="问题", min_length=1, max_length=500)
    use_multi_hop: bool = Field(True, description="是否使用多跳推理")


class SuggestQuestionsRequest(BaseModel):
    """建议问题请求"""
    topic: str = Field(..., description="主题", min_length=1)
    k: int = Field(5, description="建议数量", ge=1, le=20)


# ========== API端点 ==========

@router.post("/search", response_model=Dict, summary="执行搜索")
async def search(
    query: SearchQuery,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """
    执行语义搜索
    
    支持以下搜索类型：
    - **semantic**: 纯语义搜索（向量相似度）
    - **keyword**: 纯关键词搜索（BM25）
    - **hybrid**: 混合搜索（语义+关键词）
    - **formula**: 公式搜索（LaTeX结构匹配）
    """
    try:
        request = SearchRequest(
            query=query.query,
            search_type=query.search_type,
            k=query.k,
            filter_metadata=query.filter_metadata,
            rerank=query.rerank
        )
        
        response = service.search(request)
        
        return {
            "success": True,
            "data": {
                "results": response.results,
                "total": response.total,
                "search_type": response.search_type,
                "query_time_ms": round(response.query_time_ms, 2),
                "facets": response.facets
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"搜索失败: {str(e)}")


@router.get("/search", response_model=Dict, summary="执行搜索（GET方式）")
async def search_get(
    q: str = Query(..., description="搜索查询"),
    search_type: str = Query("hybrid", description="搜索类型"),
    k: int = Query(10, description="返回数量"),
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """使用GET方式进行搜索"""
    request = SearchRequest(
        query=q,
        search_type=search_type,
        k=k,
        rerank=True
    )
    
    response = service.search(request)
    
    return {
        "success": True,
        "data": {
            "results": response.results,
            "total": response.total,
            "search_type": response.search_type,
            "query_time_ms": round(response.query_time_ms, 2)
        }
    }


@router.post("/index", response_model=Dict, summary="索引文档")
async def index_document(
    request: IndexDocumentRequest,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """索引单个文档"""
    try:
        service.index_document(
            doc_id=request.doc_id,
            content=request.content,
            metadata=request.metadata,
            index_formulas=request.index_formulas
        )
        
        return {
            "success": True,
            "data": {
                "doc_id": request.doc_id,
                "message": "文档索引成功"
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"索引失败: {str(e)}")


@router.post("/index/batch", response_model=Dict, summary="批量索引文档")
async def index_batch(
    request: IndexBatchRequest,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """批量索引文档"""
    try:
        service.index_documents(request.documents)
        
        return {
            "success": True,
            "data": {
                "indexed_count": len(request.documents),
                "message": "批量索引成功"
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"批量索引失败: {str(e)}")


@router.delete("/index/{doc_id}", response_model=Dict, summary="删除文档索引")
async def delete_document(
    doc_id: str,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """删除文档索引"""
    try:
        service.delete_document(doc_id)
        
        return {
            "success": True,
            "data": {
                "doc_id": doc_id,
                "message": "文档删除成功"
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"删除失败: {str(e)}")


@router.post("/save", response_model=Dict, summary="保存索引")
async def save_index(
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """保存搜索索引到磁盘"""
    try:
        service.save_index()
        
        return {
            "success": True,
            "data": {
                "message": "索引保存成功"
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"保存失败: {str(e)}")


# ========== 公式搜索 ==========

@router.post("/formula", response_model=Dict, summary="公式搜索")
async def search_formula(
    query: FormulaSearchQuery,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """
    搜索数学公式
    
    支持LaTeX公式匹配，包括：
    - 精确匹配
    - 结构相似匹配
    - 变量无关匹配
    """
    try:
        results = service.search_formula(
            latex=query.latex,
            k=query.k,
            match_type=query.match_type
        )
        
        return {
            "success": True,
            "data": {
                "query": query.latex,
                "results": results,
                "total": len(results)
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"公式搜索失败: {str(e)}")


@router.post("/formula/compare", response_model=Dict, summary="比较公式")
async def compare_formulas(
    request: FormulaCompareRequest,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """比较两个LaTeX公式的相似度"""
    try:
        comparison = service.compare_formulas(request.latex1, request.latex2)
        
        return {
            "success": True,
            "data": {
                "formula1": request.latex1,
                "formula2": request.latex2,
                "comparison": comparison
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"公式比较失败: {str(e)}")


# ========== 问答系统 ==========

@router.post("/ask", response_model=Dict, summary="数学问答")
async def ask_question(
    request: QuestionRequest,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """
    数学问答系统
    
    支持：
    - 概念定义查询
    - 定理证明查询
    - 性质应用查询
    - 多跳推理
    """
    try:
        answer = service.ask(
            question=request.question,
            use_multi_hop=request.use_multi_hop
        )
        
        return {
            "success": True,
            "data": answer
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"问答失败: {str(e)}")


@router.post("/suggest-questions", response_model=Dict, summary="获取建议问题")
async def suggest_questions(
    request: SuggestQuestionsRequest,
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """基于主题获取建议问题"""
    try:
        suggestions = service.suggest_questions(request.topic, request.k)
        
        return {
            "success": True,
            "data": {
                "topic": request.topic,
                "suggestions": suggestions
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取建议失败: {str(e)}")


# ========== 统计信息 ==========

@router.get("/stats", response_model=Dict, summary="搜索统计")
async def get_stats(
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """获取搜索系统统计信息"""
    try:
        stats = service.get_stats()
        
        return {
            "success": True,
            "data": stats
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取统计失败: {str(e)}")


# ========== 自动补全 ==========

@router.get("/suggest", response_model=Dict, summary="搜索建议")
async def search_suggest(
    q: str = Query(..., description="查询前缀", min_length=1),
    k: int = Query(5, description="建议数量", ge=1, le=20),
    service: SemanticSearchService = Depends(get_semantic_search_service)
):
    """搜索自动补全建议"""
    try:
        # 简单的搜索建议：基于已有文档的标题或关键词
        results = service.vector_store.search(q, k=k*2)
        
        suggestions = []
        seen = set()
        
        for r in results:
            content = r.document.content
            # 提取前几个词作为建议
            words = content.split()[:5]
            suggestion = ' '.join(words)
            
            if suggestion not in seen and q.lower() in suggestion.lower():
                suggestions.append(suggestion)
                seen.add(suggestion)
                
                if len(suggestions) >= k:
                    break
        
        return {
            "success": True,
            "data": {
                "query": q,
                "suggestions": suggestions
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取建议失败: {str(e)}")
