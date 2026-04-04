"""
FormalMath 认证系统

提供生产级的用户认证功能：
- JWT认证
- OAuth集成（Google/GitHub）
- 密码策略
- 双因素认证（2FA）
- 基于角色的权限管理（RBAC）
"""

from .jwt_handler import (
    create_access_token,
    create_refresh_token,
    verify_token,
    decode_token,
    TokenData,
    TokenPair
)
from .password_policy import (
    PasswordPolicy,
    PasswordStrength,
    validate_password,
    hash_password,
    verify_password
)
from .two_factor_auth import (
    TwoFactorAuth,
    TOTPMethod,
    SMSMethod,
    EmailMethod,
    TwoFactorMethod
)
from .oauth_providers import (
    OAuthProvider,
    GoogleOAuth,
    GitHubOAuth,
    OAuthUserInfo
)
from .permissions import (
    Permission,
    Role,
    RoleManager,
    require_permissions,
    require_role
)
from .dependencies import (
    get_current_user,
    get_current_active_user,
    require_permissions as dep_require_permissions,
    require_role as dep_require_role
)

__all__ = [
    # JWT
    "create_access_token",
    "create_refresh_token", 
    "verify_token",
    "decode_token",
    "TokenData",
    "TokenPair",
    # Password
    "PasswordPolicy",
    "PasswordStrength",
    "validate_password",
    "hash_password",
    "verify_password",
    # 2FA
    "TwoFactorAuth",
    "TOTPMethod",
    "SMSMethod",
    "EmailMethod",
    "TwoFactorMethod",
    # OAuth
    "OAuthProvider",
    "GoogleOAuth",
    "GitHubOAuth",
    "OAuthUserInfo",
    # Permissions
    "Permission",
    "Role",
    "RoleManager",
    "require_permissions",
    "require_role",
    # Dependencies
    "get_current_user",
    "get_current_active_user",
    "dep_require_permissions",
    "dep_require_role"
]
