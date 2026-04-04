"""
分页服务
"""
from typing import TypeVar, Generic, List, Optional
from pydantic import BaseModel
from sqlalchemy.orm import Query
from fastapi import Request
from urllib.parse import urlencode

T = TypeVar('T')


class PaginatedResponse(BaseModel, Generic[T]):
    """分页响应模型"""
    items: List[T]
    total: int
    page: int
    page_size: int
    pages: int
    has_next: bool
    has_prev: bool
    next_url: Optional[str] = None
    prev_url: Optional[str] = None


class PaginationParams:
    """分页参数"""
    def __init__(self, page: int = 1, page_size: int = 20):
        self.page = page
        self.page_size = page_size
        self.offset = (page - 1) * page_size


def paginate_query(
    query: Query,
    page: int,
    page_size: int,
    request: Request = None
) -> PaginatedResponse:
    """
    对SQLAlchemy查询进行分页
    
    Args:
        query: SQLAlchemy查询对象
        page: 页码（从1开始）
        page_size: 每页数量
        request: FastAPI请求对象（用于生成导航URL）
    
    Returns:
        分页响应对象
    """
    # 获取总数
    total = query.count()
    
    # 计算分页
    pages = (total + page_size - 1) // page_size if total > 0 else 1
    has_next = page < pages
    has_prev = page > 1
    
    # 执行分页查询
    offset = (page - 1) * page_size
    items = query.offset(offset).limit(page_size).all()
    
    # 构建导航URL
    next_url = None
    prev_url = None
    
    if request:
        base_url = str(request.url).split('?')[0]
        query_params = dict(request.query_params)
        
        if has_next:
            query_params['page'] = page + 1
            next_url = f"{base_url}?{urlencode(query_params)}"
        
        if has_prev:
            query_params['page'] = page - 1
            prev_url = f"{base_url}?{urlencode(query_params)}"
    
    return PaginatedResponse(
        items=items,
        total=total,
        page=page,
        page_size=page_size,
        pages=pages,
        has_next=has_next,
        has_prev=has_prev,
        next_url=next_url,
        prev_url=prev_url
    )


def paginate_list(
    items: List[T],
    page: int,
    page_size: int,
    request: Request = None
) -> PaginatedResponse:
    """
    对列表进行分页
    
    Args:
        items: 数据列表
        page: 页码
        page_size: 每页数量
        request: FastAPI请求对象
    
    Returns:
        分页响应对象
    """
    total = len(items)
    pages = (total + page_size - 1) // page_size if total > 0 else 1
    has_next = page < pages
    has_prev = page > 1
    
    offset = (page - 1) * page_size
    paginated_items = items[offset:offset + page_size]
    
    # 构建导航URL
    next_url = None
    prev_url = None
    
    if request:
        base_url = str(request.url).split('?')[0]
        query_params = dict(request.query_params)
        
        if has_next:
            query_params['page'] = page + 1
            next_url = f"{base_url}?{urlencode(query_params)}"
        
        if has_prev:
            query_params['page'] = page - 1
            prev_url = f"{base_url}?{urlencode(query_params)}"
    
    return PaginatedResponse(
        items=paginated_items,
        total=total,
        page=page,
        page_size=page_size,
        pages=pages,
        has_next=has_next,
        has_prev=has_prev,
        next_url=next_url,
        prev_url=prev_url
    )
