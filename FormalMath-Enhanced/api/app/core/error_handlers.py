"""
全局错误处理器

提供统一的错误处理和响应格式
"""
import logging
import traceback
import uuid
from datetime import datetime
from typing import Dict, Any, Optional
from fastapi import Request, status
from fastapi.responses import JSONResponse
from fastapi.exceptions import RequestValidationError
from sqlalchemy.exc import SQLAlchemyError, OperationalError, TimeoutError as DBTimeoutError
from pydantic import ValidationError

from app.core.config import settings

logger = logging.getLogger(__name__)


class APIException(Exception):
    """API自定义异常基类"""
    
    def __init__(
        self,
        message: str,
        status_code: int = 500,
        error_code: str = "INTERNAL_ERROR",
        details: Optional[Dict[str, Any]] = None
    ):
        self.message = message
        self.status_code = status_code
        self.error_code = error_code
        self.details = details or {}
        super().__init__(self.message)


class NotFoundException(APIException):
    """资源未找到异常"""
    
    def __init__(self, resource: str, resource_id: str):
        super().__init__(
            message=f"{resource} '{resource_id}' 未找到",
            status_code=status.HTTP_404_NOT_FOUND,
            error_code="NOT_FOUND",
            details={"resource": resource, "resource_id": resource_id}
        )


class ValidationException(APIException):
    """验证异常"""
    
    def __init__(self, message: str, details: Optional[Dict[str, Any]] = None):
        super().__init__(
            message=message,
            status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
            error_code="VALIDATION_ERROR",
            details=details
        )


class AuthenticationException(APIException):
    """认证异常"""
    
    def __init__(self, message: str = "认证失败"):
        super().__init__(
            message=message,
            status_code=status.HTTP_401_UNAUTHORIZED,
            error_code="AUTHENTICATION_ERROR"
        )


class AuthorizationException(APIException):
    """授权异常"""
    
    def __init__(self, message: str = "权限不足"):
        super().__init__(
            message=message,
            status_code=status.HTTP_403_FORBIDDEN,
            error_code="AUTHORIZATION_ERROR"
        )


class RateLimitException(APIException):
    """速率限制异常"""
    
    def __init__(self, message: str = "请求过于频繁", retry_after: int = 60):
        super().__init__(
            message=message,
            status_code=status.HTTP_429_TOO_MANY_REQUESTS,
            error_code="RATE_LIMIT_EXCEEDED",
            details={"retry_after": retry_after}
        )


class DatabaseException(APIException):
    """数据库异常"""
    
    def __init__(self, message: str = "数据库操作失败"):
        super().__init__(
            message=message,
            status_code=status.HTTP_503_SERVICE_UNAVAILABLE,
            error_code="DATABASE_ERROR"
        )


def generate_error_response(
    message: str,
    status_code: int,
    error_code: str,
    details: Optional[Dict[str, Any]] = None,
    exc: Optional[Exception] = None
) -> Dict[str, Any]:
    """生成标准错误响应"""
    error_id = str(uuid.uuid4())[:8]
    
    response = {
        "success": False,
        "error": {
            "code": error_code,
            "message": message,
            "error_id": error_id,
            "timestamp": datetime.utcnow().isoformat()
        }
    }
    
    if details:
        response["error"]["details"] = details
    
    # 调试模式下添加更多信息
    if settings.DEBUG and exc:
        response["error"]["debug"] = {
            "type": type(exc).__name__,
            "args": getattr(exc, "args", []),
            "traceback": traceback.format_exc().split("\n") if exc else None
        }
    
    return response


async def api_exception_handler(request: Request, exc: APIException) -> JSONResponse:
    """处理API自定义异常"""
    logger.warning(
        f"API异常: {exc.error_code} - {exc.message}",
        extra={
            "error_code": exc.error_code,
            "status_code": exc.status_code,
            "path": request.url.path,
            "method": request.method
        }
    )
    
    response = generate_error_response(
        message=exc.message,
        status_code=exc.status_code,
        error_code=exc.error_code,
        details=exc.details,
        exc=exc if settings.DEBUG else None
    )
    
    headers = {}
    if exc.error_code == "RATE_LIMIT_EXCEEDED" and exc.details:
        headers["Retry-After"] = str(exc.details.get("retry_after", 60))
    
    return JSONResponse(
        status_code=exc.status_code,
        content=response,
        headers=headers
    )


async def validation_exception_handler(
    request: Request,
    exc: RequestValidationError
) -> JSONResponse:
    """处理请求验证异常"""
    logger.warning(
        f"验证错误: {request.url.path}",
        extra={"errors": exc.errors()}
    )
    
    # 格式化验证错误
    errors = []
    for error in exc.errors():
        error_detail = {
            "field": ".".join(str(x) for x in error["loc"]),
            "message": error["msg"],
            "type": error["type"]
        }
        if "input" in error:
            error_detail["input"] = str(error["input"])[:100]  # 限制长度
        errors.append(error_detail)
    
    response = generate_error_response(
        message="请求参数验证失败",
        status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
        error_code="VALIDATION_ERROR",
        details={"errors": errors}
    )
    
    return JSONResponse(
        status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
        content=response
    )


async def sqlalchemy_exception_handler(
    request: Request,
    exc: SQLAlchemyError
) -> JSONResponse:
    """处理SQLAlchemy数据库异常"""
    error_id = str(uuid.uuid4())[:8]
    
    logger.error(
        f"数据库错误 [{error_id}]: {str(exc)}",
        extra={
            "error_id": error_id,
            "path": request.url.path,
            "method": request.method
        },
        exc_info=True
    )
    
    # 根据异常类型确定状态码
    if isinstance(exc, OperationalError):
        status_code = status.HTTP_503_SERVICE_UNAVAILABLE
        message = "数据库连接失败，请稍后重试"
    elif isinstance(exc, DBTimeoutError):
        status_code = status.HTTP_504_GATEWAY_TIMEOUT
        message = "数据库查询超时，请稍后重试"
    else:
        status_code = status.HTTP_500_INTERNAL_SERVER_ERROR
        message = "数据库操作失败"
    
    response = generate_error_response(
        message=message,
        status_code=status_code,
        error_code="DATABASE_ERROR",
        details={"error_id": error_id}
    )
    
    return JSONResponse(
        status_code=status_code,
        content=response
    )


async def general_exception_handler(request: Request, exc: Exception) -> JSONResponse:
    """处理通用异常"""
    error_id = str(uuid.uuid4())[:8]
    
    # 记录详细错误信息（内部）
    logger.error(
        f"未处理异常 [{error_id}]: {str(exc)}",
        extra={
            "error_id": error_id,
            "path": request.url.path,
            "method": request.method,
            "exception_type": type(exc).__name__
        },
        exc_info=True
    )
    
    # 生产环境返回通用错误消息
    if settings.DEBUG:
        message = str(exc)
        details = {
            "exception_type": type(exc).__name__,
            "traceback": traceback.format_exc().split("\n")
        }
    else:
        message = "服务器内部错误，请稍后重试"
        details = {"error_id": error_id}
    
    response = generate_error_response(
        message=message,
        status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
        error_code="INTERNAL_ERROR",
        details=details,
        exc=exc if settings.DEBUG else None
    )
    
    return JSONResponse(
        status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
        content=response
    )


async def http_exception_handler(request: Request, exc) -> JSONResponse:
    """处理HTTP异常（覆盖FastAPI默认）"""
    from fastapi.exceptions import HTTPException
    
    if isinstance(exc, HTTPException):
        # 转换为标准格式
        if isinstance(exc.detail, dict):
            # 已经是我们的格式
            return JSONResponse(
                status_code=exc.status_code,
                content={"success": False, "error": exc.detail}
            )
        
        response = generate_error_response(
            message=exc.detail if isinstance(exc.detail, str) else str(exc.detail),
            status_code=exc.status_code,
            error_code=f"HTTP_{exc.status_code}"
        )
        
        return JSONResponse(
            status_code=exc.status_code,
            content=response,
            headers=getattr(exc, "headers", None) or {}
        )
    
    # 其他情况使用通用处理
    return await general_exception_handler(request, exc)


def register_error_handlers(app):
    """注册所有错误处理器到FastAPI应用"""
    
    # 自定义API异常
    app.add_exception_handler(APIException, api_exception_handler)
    
    # 请求验证异常
    app.add_exception_handler(RequestValidationError, validation_exception_handler)
    
    # Pydantic验证异常
    app.add_exception_handler(ValidationError, validation_exception_handler)
    
    # 数据库异常
    app.add_exception_handler(SQLAlchemyError, sqlalchemy_exception_handler)
    
    # HTTP异常（覆盖默认）
    from fastapi.exceptions import HTTPException
    app.add_exception_handler(HTTPException, http_exception_handler)
    
    # 通用异常（最后注册）
    app.add_exception_handler(Exception, general_exception_handler)
    
    logger.info("错误处理器注册完成")
