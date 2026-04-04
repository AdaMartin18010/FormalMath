"""
输入验证中间件

防止各种注入攻击和恶意输入
"""
import re
import json
import logging
from typing import Dict, List, Optional, Any
from fastapi import Request, HTTPException
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class InputValidationMiddleware(BaseHTTPMiddleware):
    """
    输入验证中间件
    
    验证内容：
    - 请求体大小限制
    - JSON格式验证
    - 参数类型验证
    - 特殊字符过滤
    """
    
    def __init__(
        self,
        app: ASGIApp,
        max_body_size: int = 10 * 1024 * 1024,  # 10MB
        max_json_depth: int = 10,
        max_string_length: int = 10000,
        allowed_content_types: Optional[List[str]] = None,
        block_patterns: Optional[List[str]] = None
    ):
        super().__init__(app)
        self.max_body_size = max_body_size
        self.max_json_depth = max_json_depth
        self.max_string_length = max_string_length
        self.allowed_content_types = allowed_content_types or [
            "application/json",
            "application/x-www-form-urlencoded",
            "multipart/form-data",
            "text/plain",
            "application/xml",
        ]
        
        # 危险的输入模式
        self.block_patterns = block_patterns or [
            r"<script[^>]*>",
            r"javascript:",
            r"on\w+\s*=",
            r"vbscript:",
            r"data:text/html",
            r"expression\s*\(",
        ]
        self._compiled_patterns = [re.compile(p, re.IGNORECASE) for p in self.block_patterns]
    
    def _check_content_type(self, content_type: Optional[str]) -> bool:
        """检查Content-Type是否允许"""
        if not content_type:
            return True
        
        # 移除charset等参数
        main_type = content_type.split(";")[0].strip().lower()
        return main_type in self.allowed_content_types
    
    def _check_json_depth(self, obj: Any, depth: int = 0) -> bool:
        """检查JSON嵌套深度"""
        if depth > self.max_json_depth:
            return False
        
        if isinstance(obj, dict):
            for value in obj.values():
                if not self._check_json_depth(value, depth + 1):
                    return False
        elif isinstance(obj, list):
            for item in obj:
                if not self._check_json_depth(item, depth + 1):
                    return False
        
        return True
    
    def _check_string_length(self, obj: Any) -> bool:
        """检查字符串长度"""
        if isinstance(obj, str) and len(obj) > self.max_string_length:
            return False
        
        if isinstance(obj, dict):
            for value in obj.values():
                if not self._check_string_length(value):
                    return False
        elif isinstance(obj, list):
            for item in obj:
                if not self._check_string_length(item):
                    return False
        
        return True
    
    def _check_malicious_patterns(self, text: str) -> Optional[str]:
        """检查恶意模式"""
        for pattern in self._compiled_patterns:
            match = pattern.search(text)
            if match:
                return match.group()
        return None
    
    async def _validate_body(self, request: Request) -> Optional[bytes]:
        """验证请求体"""
        body = await request.body()
        
        # 检查大小
        if len(body) > self.max_body_size:
            raise HTTPException(
                status_code=413,
                detail={
                    "error": "Payload Too Large",
                    "message": f"请求体超过最大限制 {self.max_body_size} 字节"
                }
            )
        
        # 检查Content-Type
        content_type = request.headers.get("content-type")
        if not self._check_content_type(content_type):
            raise HTTPException(
                status_code=415,
                detail={
                    "error": "Unsupported Media Type",
                    "message": f"不支持的Content-Type: {content_type}"
                }
            )
        
        # 验证JSON内容
        if content_type and "application/json" in content_type:
            try:
                data = json.loads(body)
                
                # 检查JSON深度
                if not self._check_json_depth(data):
                    raise HTTPException(
                        status_code=400,
                        detail={
                            "error": "Invalid JSON",
                            "message": f"JSON嵌套深度超过限制 {self.max_json_depth}"
                        }
                    )
                
                # 检查字符串长度
                if not self._check_string_length(data):
                    raise HTTPException(
                        status_code=400,
                        detail={
                            "error": "Invalid Input",
                            "message": f"字符串长度超过限制 {self.max_string_length}"
                        }
                    )
                
            except json.JSONDecodeError as e:
                raise HTTPException(
                    status_code=400,
                    detail={
                        "error": "Invalid JSON",
                        "message": f"JSON解析错误: {str(e)}"
                    }
                )
        
        return body
    
    async def dispatch(self, request: Request, call_next):
        """处理请求"""
        # 验证查询参数
        query_params = str(request.query_params)
        malicious = self._check_malicious_patterns(query_params)
        if malicious:
            logger.warning(
                f"检测到恶意查询参数: {malicious[:50]}... "
                f"from {request.client.host}"
            )
            raise HTTPException(
                status_code=400,
                detail={
                    "error": "Invalid Input",
                    "message": "查询参数包含非法内容"
                }
            )
        
        # 验证请求体（对于特定方法）
        if request.method in ["POST", "PUT", "PATCH"]:
            await self._validate_body(request)
        
        return await call_next(request)


class ParameterValidationMiddleware(BaseHTTPMiddleware):
    """
    参数验证中间件
    
    验证URL参数、查询参数等
    """
    
    # 常见的ID参数模式
    UUID_PATTERN = re.compile(
        r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$',
        re.IGNORECASE
    )
    
    # 允许的ID格式
    ALLOWED_ID_PATTERN = re.compile(r'^[a-zA-Z0-9_\-]+$')
    
    def __init__(
        self,
        app: ASGIApp,
        max_param_length: int = 100,
        allow_special_chars: bool = False
    ):
        super().__init__(app)
        self.max_param_length = max_param_length
        self.allow_special_chars = allow_special_chars
    
    def _validate_param(self, name: str, value: str) -> bool:
        """验证单个参数"""
        # 检查长度
        if len(value) > self.max_param_length:
            return False
        
        # 检查特殊字符
        if not self.allow_special_chars:
            if not self.ALLOWED_ID_PATTERN.match(value):
                return False
        
        return True
    
    async def dispatch(self, request: Request, call_next):
        """处理请求"""
        # 验证路径参数（从URL路径中提取）
        path = request.url.path
        path_parts = path.split("/")
        
        for part in path_parts:
            if part and not self._validate_param("path_part", part):
                raise HTTPException(
                    status_code=400,
                    detail={
                        "error": "Invalid Parameter",
                        "message": f"路径参数包含非法字符或过长"
                    }
                )
        
        # 验证查询参数
        for key, value in request.query_params.items():
            if not self._validate_param(key, value):
                raise HTTPException(
                    status_code=400,
                    detail={
                        "error": "Invalid Parameter",
                        "message": f"查询参数 '{key}' 包含非法内容"
                    }
                )
        
        return await call_next(request)
