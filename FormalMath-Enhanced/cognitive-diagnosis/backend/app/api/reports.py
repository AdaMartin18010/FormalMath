"""
报告API路由
"""

from typing import Optional
from fastapi import APIRouter, HTTPException, Query, Depends
from pydantic import BaseModel

from app.services.report_service import ReportService


router = APIRouter()


class ReportListResponse(BaseModel):
    """报告列表响应"""
    success: bool
    data: list
    total: int


def get_report_service():
    return ReportService()


@router.get("/user/{user_id}", response_model=ReportListResponse)
async def get_user_reports(
    user_id: str,
    limit: int = Query(10, ge=1, le=50),
    offset: int = Query(0, ge=0),
    service: ReportService = Depends(get_report_service)
):
    """获取用户的所有诊断报告"""
    try:
        reports = service.get_user_reports(user_id, limit=limit, offset=offset)
        total = service.count_user_reports(user_id)
        
        return ReportListResponse(
            success=True,
            data=[r.model_dump() for r in reports],
            total=total
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/{report_id}")
async def get_report(
    report_id: str,
    service: ReportService = Depends(get_report_service)
):
    """
    获取诊断报告详情
    
    包含：
    - 知识状态
    - 能力水平评估
    - 学习建议
    - 可视化数据
    """
    try:
        report = service.get_report_by_id(report_id)
        if not report:
            raise HTTPException(status_code=404, detail="报告不存在")
        
        return {
            "success": True,
            "data": report.model_dump()
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/{report_id}/summary")
async def get_report_summary(
    report_id: str,
    service: ReportService = Depends(get_report_service)
):
    """获取报告摘要（简化版）"""
    try:
        summary = service.get_report_summary(report_id)
        if not summary:
            raise HTTPException(status_code=404, detail="报告不存在")
        
        return {
            "success": True,
            "data": summary
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/{report_id}/comparison")
async def compare_reports(
    report_id: str,
    compare_with: Optional[str] = Query(None, description="对比的报告ID"),
    service: ReportService = Depends(get_report_service)
):
    """
    报告对比分析
    
    对比两次诊断的进步情况
    """
    try:
        comparison = service.compare_reports(report_id, compare_with)
        
        return {
            "success": True,
            "data": comparison
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/{report_id}/export")
async def export_report(
    report_id: str,
    format: str = Query("json", regex="^(json|pdf|html)$"),
    service: ReportService = Depends(get_report_service)
):
    """
    导出报告
    
    - **format**: 导出格式 (json/pdf/html)
    """
    try:
        exported = service.export_report(report_id, format=format)
        
        return {
            "success": True,
            "data": {
                "format": format,
                "content": exported
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
