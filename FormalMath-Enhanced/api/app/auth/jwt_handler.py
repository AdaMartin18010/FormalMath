"""
JWT认证处理模块

提供完整的JWT令牌管理功能：
- 访问令牌和刷新令牌的创建
- 令牌验证和解码
- 令牌黑名单管理
- 自动刷新机制
"""

import uuid
from datetime import datetime, timedelta, timezone
from typing import Optional, Dict, Any, List
from enum import Enum

from jose import JWTError, jwt
from passlib.context import CryptContext
from pydantic import BaseModel, Field

from ..core.config import settings
from ..cache.redis_cache import cache


# JWT配置
JWT_ALGORITHM = "HS256"
ACCESS_TOKEN_EXPIRE_MINUTES = 30
REFRESH_TOKEN_EXPIRE_DAYS = 7
TOKEN_ISSUER = "formalmath-api"
TOKEN_AUDIENCE = "formalmath-users"

# 密码哈希上下文
pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto")


class TokenType(str, Enum):
    """令牌类型"""
    ACCESS = "access"
    REFRESH = "refresh"
    VERIFICATION = "verification"
    PASSWORD_RESET = "password_reset"


class TokenData(BaseModel):
    """令牌数据模型"""
    user_id: int
    username: str
    email: str
    roles: List[str] = Field(default_factory=list)
    permissions: List[str] = Field(default_factory=list)
    token_type: TokenType = TokenType.ACCESS
    jti: str = Field(default_factory=lambda: str(uuid.uuid4()))
    iat: Optional[datetime] = None
    exp: Optional[datetime] = None
    
    class Config:
        json_encoders = {
            datetime: lambda v: v.isoformat()
        }


class TokenPair(BaseModel):
    """令牌对（访问令牌 + 刷新令牌）"""
    access_token: str
    refresh_token: str
    token_type: str = "bearer"
    expires_in: int  # 访问令牌过期时间（秒）
    refresh_expires_in: int  # 刷新令牌过期时间（秒）


class TokenBlacklist:
    """令牌黑名单管理"""
    
    BLACKLIST_PREFIX = "jwt_blacklist:"
    
    @classmethod
    async def blacklist_token(cls, jti: str, exp: datetime) -> bool:
        """
        将令牌加入黑名单
        
        Args:
            jti: 令牌唯一标识
            exp: 令牌过期时间
            
        Returns:
            是否成功加入黑名单
        """
        try:
            # 计算剩余有效期
            now = datetime.now(timezone.utc)
            if isinstance(exp, datetime) and exp.tzinfo is None:
                exp = exp.replace(tzinfo=timezone.utc)
            ttl = int((exp - now).total_seconds())
            
            if ttl > 0:
                await cache.set(
                    f"{cls.BLACKLIST_PREFIX}{jti}",
                    "revoked",
                    ttl=ttl
                )
            return True
        except Exception as e:
            # 记录错误但不中断流程
            print(f"Token blacklist error: {e}")
            return False
    
    @classmethod
    async def is_blacklisted(cls, jti: str) -> bool:
        """
        检查令牌是否在黑名单中
        
        Args:
            jti: 令牌唯一标识
            
        Returns:
            是否在黑名单中
        """
        try:
            result = await cache.get(f"{cls.BLACKLIST_PREFIX}{jti}")
            return result is not None
        except Exception:
            # 如果Redis不可用，假设令牌有效（降级处理）
            return False


def create_access_token(
    user_id: int,
    username: str,
    email: str,
    roles: List[str] = None,
    permissions: List[str] = None,
    expires_delta: Optional[timedelta] = None,
    additional_claims: Optional[Dict[str, Any]] = None
) -> str:
    """
    创建访问令牌
    
    Args:
        user_id: 用户ID
        username: 用户名
        email: 邮箱
        roles: 用户角色列表
        permissions: 用户权限列表
        expires_delta: 自定义过期时间
        additional_claims: 额外声明
        
    Returns:
        JWT访问令牌
    """
    if expires_delta is None:
        expires_delta = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    
    now = datetime.now(timezone.utc)
    expire = now + expires_delta
    jti = str(uuid.uuid4())
    
    # 构建payload
    payload = {
        "sub": str(user_id),  # 主题（用户ID）
        "username": username,
        "email": email,
        "roles": roles or [],
        "permissions": permissions or [],
        "type": TokenType.ACCESS.value,
        "jti": jti,
        "iat": now,  # 签发时间
        "exp": expire,  # 过期时间
        "iss": TOKEN_ISSUER,  # 签发者
        "aud": TOKEN_AUDIENCE,  # 受众
    }
    
    # 添加额外声明
    if additional_claims:
        payload.update(additional_claims)
    
    # 获取密钥
    secret_key = settings.SECRET_KEY if hasattr(settings, 'SECRET_KEY') else "your-secret-key-change-in-production"
    
    return jwt.encode(payload, secret_key, algorithm=JWT_ALGORITHM)


def create_refresh_token(
    user_id: int,
    username: str,
    expires_delta: Optional[timedelta] = None
) -> str:
    """
    创建刷新令牌
    
    Args:
        user_id: 用户ID
        username: 用户名
        expires_delta: 自定义过期时间
        
    Returns:
        JWT刷新令牌
    """
    if expires_delta is None:
        expires_delta = timedelta(days=REFRESH_TOKEN_EXPIRE_DAYS)
    
    now = datetime.now(timezone.utc)
    expire = now + expires_delta
    jti = str(uuid.uuid4())
    
    payload = {
        "sub": str(user_id),
        "username": username,
        "type": TokenType.REFRESH.value,
        "jti": jti,
        "iat": now,
        "exp": expire,
        "iss": TOKEN_ISSUER,
        "aud": TOKEN_AUDIENCE,
    }
    
    secret_key = settings.SECRET_KEY if hasattr(settings, 'SECRET_KEY') else "your-secret-key-change-in-production"
    
    # 存储刷新令牌元数据到Redis（用于撤销）
    cache_key = f"refresh_token:{user_id}:{jti}"
    cache.set(cache_key, {
        "user_id": user_id,
        "username": username,
        "created_at": now.isoformat(),
        "expires_at": expire.isoformat()
    }, ttl=int(expires_delta.total_seconds()))
    
    return jwt.encode(payload, secret_key, algorithm=JWT_ALGORITHM)


def create_token_pair(
    user_id: int,
    username: str,
    email: str,
    roles: List[str] = None,
    permissions: List[str] = None
) -> TokenPair:
    """
    创建令牌对（访问令牌 + 刷新令牌）
    
    Args:
        user_id: 用户ID
        username: 用户名
        email: 邮箱
        roles: 用户角色列表
        permissions: 用户权限列表
        
    Returns:
        令牌对
    """
    access_token = create_access_token(
        user_id=user_id,
        username=username,
        email=email,
        roles=roles,
        permissions=permissions
    )
    
    refresh_token = create_refresh_token(
        user_id=user_id,
        username=username
    )
    
    return TokenPair(
        access_token=access_token,
        refresh_token=refresh_token,
        token_type="bearer",
        expires_in=ACCESS_TOKEN_EXPIRE_MINUTES * 60,
        refresh_expires_in=REFRESH_TOKEN_EXPIRE_DAYS * 24 * 60 * 60
    )


def decode_token(token: str) -> Optional[Dict[str, Any]]:
    """
    解码令牌（不验证）
    
    Args:
        token: JWT令牌
        
    Returns:
        解码后的payload，失败返回None
    """
    try:
        return jwt.get_unverified_claims(token)
    except JWTError:
        return None


def verify_token(
    token: str,
    expected_type: TokenType = TokenType.ACCESS
) -> Optional[TokenData]:
    """
    验证令牌
    
    Args:
        token: JWT令牌
        expected_type: 期望的令牌类型
        
    Returns:
        验证通过的令牌数据，失败返回None
    """
    try:
        secret_key = settings.SECRET_KEY if hasattr(settings, 'SECRET_KEY') else "your-secret-key-change-in-production"
        
        payload = jwt.decode(
            token,
            secret_key,
            algorithms=[JWT_ALGORITHM],
            issuer=TOKEN_ISSUER,
            audience=TOKEN_AUDIENCE
        )
        
        # 验证令牌类型
        token_type = payload.get("type")
        if token_type != expected_type.value:
            return None
        
        return TokenData(
            user_id=int(payload.get("sub")),
            username=payload.get("username"),
            email=payload.get("email"),
            roles=payload.get("roles", []),
            permissions=payload.get("permissions", []),
            token_type=expected_type,
            jti=payload.get("jti"),
            iat=payload.get("iat"),
            exp=payload.get("exp")
        )
        
    except JWTError:
        return None


async def revoke_token(token: str) -> bool:
    """
    撤销令牌
    
    Args:
        token: JWT令牌
        
    Returns:
        是否成功撤销
    """
    try:
        payload = decode_token(token)
        if not payload:
            return False
        
        jti = payload.get("jti")
        exp = payload.get("exp")
        
        if jti and exp:
            exp_datetime = datetime.fromtimestamp(exp, tz=timezone.utc)
            return await TokenBlacklist.blacklist_token(jti, exp_datetime)
        
        return False
    except Exception:
        return False


async def refresh_access_token(refresh_token: str) -> Optional[TokenPair]:
    """
    使用刷新令牌获取新的令牌对
    
    Args:
        refresh_token: 刷新令牌
        
    Returns:
        新的令牌对，失败返回None
    """
    # 验证刷新令牌
    token_data = verify_token(refresh_token, TokenType.REFRESH)
    if not token_data:
        return None
    
    # 检查是否已被撤销
    if await TokenBlacklist.is_blacklisted(token_data.jti):
        return None
    
    # 这里应该从数据库获取用户信息
    # 简化处理，实际实现需要查询数据库
    # user = await get_user_by_id(token_data.user_id)
    # if not user:
    #     return None
    
    # 撤销旧的刷新令牌
    await revoke_token(refresh_token)
    
    # 创建新的令牌对
    return create_token_pair(
        user_id=token_data.user_id,
        username=token_data.username,
        email="",  # 需要从数据库获取
        roles=[],  # 需要从数据库获取
        permissions=[]  # 需要从数据库获取
    )


# 同步版本的密码哈希函数（用于与SQLAlchemy兼容）
def hash_password(password: str) -> str:
    """哈希密码"""
    return pwd_context.hash(password)


def verify_password(plain_password: str, hashed_password: str) -> bool:
    """验证密码"""
    return pwd_context.verify(plain_password, hashed_password)
