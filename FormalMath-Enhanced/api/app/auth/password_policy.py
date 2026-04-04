"""
密码策略模块

提供生产级密码安全功能：
- 密码强度验证
- 密码哈希（bcrypt/Argon2）
- 密码历史检查
- 常见密码黑名单
- 熵值计算
"""

import re
import math
import secrets
import string
from enum import Enum
from typing import List, Set, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime, timedelta

from passlib.context import CryptContext
from zxcvbn import zxcvbn


class PasswordStrength(Enum):
    """密码强度等级"""
    VERY_WEAK = 0
    WEAK = 1
    FAIR = 2
    GOOD = 3
    STRONG = 4
    VERY_STRONG = 5


@dataclass
class PasswordValidationResult:
    """密码验证结果"""
    is_valid: bool
    strength: PasswordStrength
    score: int  # 0-4 (zxcvbn score)
    entropy: float
    warnings: List[str]
    suggestions: List[str]
    crack_time_display: str
    crack_time_seconds: float


class PasswordPolicy:
    """密码策略管理器"""
    
    # 默认配置
    DEFAULT_MIN_LENGTH = 8
    DEFAULT_MAX_LENGTH = 128
    DEFAULT_MIN_STRENGTH = PasswordStrength.FAIR
    
    # 字符类型要求
    REQUIRE_UPPERCASE = True
    REQUIRE_LOWERCASE = True
    REQUIRE_DIGITS = True
    REQUIRE_SPECIAL = True
    
    # 特殊字符集
    SPECIAL_CHARS = "!@#$%^&*()_+-=[]{}|;:,.<>?"
    
    # 常见弱密码列表（生产环境应使用更大的列表）
    COMMON_PASSWORDS = {
        "password", "123456", "12345678", "qwerty", "abc123",
        "monkey", "letmein", "dragon", "111111", "baseball",
        "iloveyou", "trustno1", "sunshine", "princess", "admin",
        "welcome", "shadow", "ashley", "football", "jesus",
        "michael", "ninja", "mustang", "password1", "123456789",
        "adobe123", "admin123", "root", "toor", "guest"
    }
    
    def __init__(
        self,
        min_length: int = DEFAULT_MIN_LENGTH,
        max_length: int = DEFAULT_MAX_LENGTH,
        min_strength: PasswordStrength = DEFAULT_MIN_STRENGTH,
        require_uppercase: bool = True,
        require_lowercase: bool = True,
        require_digits: bool = True,
        require_special: bool = True,
        max_repeated_chars: int = 3,
        prevent_username_in_password: bool = True,
        password_history_count: int = 5,
        min_password_age_days: int = 1,
        max_password_age_days: int = 90
    ):
        """
        初始化密码策略
        
        Args:
            min_length: 最小长度
            max_length: 最大长度
            min_strength: 最小强度要求
            require_uppercase: 是否要求大写字母
            require_lowercase: 是否要求小写字母
            require_digits: 是否要求数字
            require_special: 是否要求特殊字符
            max_repeated_chars: 最大连续重复字符数
            prevent_username_in_password: 禁止密码中包含用户名
            password_history_count: 密码历史记录数量
            min_password_age_days: 最小密码使用时间（天）
            max_password_age_days: 最大密码使用时间（天）
        """
        self.min_length = min_length
        self.max_length = max_length
        self.min_strength = min_strength
        self.require_uppercase = require_uppercase
        self.require_lowercase = require_lowercase
        self.require_digits = require_digits
        self.require_special = require_special
        self.max_repeated_chars = max_repeated_chars
        self.prevent_username_in_password = prevent_username_in_password
        self.password_history_count = password_history_count
        self.min_password_age = timedelta(days=min_password_age_days)
        self.max_password_age = timedelta(days=max_password_age_days)
        
        # 密码哈希上下文（支持bcrypt和Argon2）
        self.pwd_context = CryptContext(
            schemes=["bcrypt", "argon2"],
            deprecated="auto",
            bcrypt__rounds=12,
            argon2__time_cost=3,
            argon2__memory_cost=65536,
            argon2__parallelism=4
        )
    
    def validate(
        self,
        password: str,
        username: str = "",
        email: str = "",
        previous_passwords: List[str] = None
    ) -> PasswordValidationResult:
        """
        验证密码是否符合策略
        
        Args:
            password: 待验证密码
            username: 用户名（用于检查）
            email: 邮箱（用于检查）
            previous_passwords: 历史密码哈希列表
            
        Returns:
            验证结果
        """
        warnings = []
        suggestions = []
        
        # 基本长度检查
        if len(password) < self.min_length:
            warnings.append(f"密码长度至少为 {self.min_length} 个字符")
        
        if len(password) > self.max_length:
            warnings.append(f"密码长度不能超过 {self.max_length} 个字符")
        
        # 字符类型检查
        if self.require_uppercase and not re.search(r'[A-Z]', password):
            warnings.append("密码必须包含至少一个大写字母")
        
        if self.require_lowercase and not re.search(r'[a-z]', password):
            warnings.append("密码必须包含至少一个小写字母")
        
        if self.require_digits and not re.search(r'\d', password):
            warnings.append("密码必须包含至少一个数字")
        
        if self.require_special and not re.search(r'[!@#$%^&*()_+\-=\[\]{}|;:,.<>?]', password):
            warnings.append("密码必须包含至少一个特殊字符")
        
        # 检查连续重复字符
        if self._has_repeated_chars(password, self.max_repeated_chars):
            warnings.append(f"密码不能包含超过 {self.max_repeated_chars} 个连续重复的字符")
        
        # 检查常见密码
        if password.lower() in self.COMMON_PASSWORDS:
            warnings.append("此密码过于常见，容易被猜测")
            suggestions.append("使用独特的、难以猜测的密码")
        
        # 检查用户名/邮箱
        if self.prevent_username_in_password:
            if username and username.lower() in password.lower():
                warnings.append("密码不能包含用户名")
            if email:
                email_prefix = email.split('@')[0].lower()
                if email_prefix in password.lower():
                    warnings.append("密码不能包含邮箱前缀")
        
        # 检查键盘序列
        if self._is_keyboard_sequence(password):
            warnings.append("密码包含键盘序列，安全性较低")
        
        # 检查历史密码
        if previous_passwords:
            for prev_hash in previous_passwords:
                if self.pwd_context.verify(password, prev_hash):
                    warnings.append("不能使用最近使用过的密码")
                    break
        
        # 使用zxcvbn进行高级分析
        user_inputs = []
        if username:
            user_inputs.append(username)
        if email:
            user_inputs.append(email)
        
        result = zxcvbn(password, user_inputs=user_inputs)
        score = result['score']  # 0-4
        
        # 转换为PasswordStrength
        strength_map = {
            0: PasswordStrength.VERY_WEAK,
            1: PasswordStrength.WEAK,
            2: PasswordStrength.FAIR,
            3: PasswordStrength.GOOD,
            4: PasswordStrength.STRONG
        }
        strength = strength_map.get(score, PasswordStrength.VERY_WEAK)
        
        # 添加zxcvbn的建议
        if result['feedback']['warning']:
            suggestions.append(result['feedback']['warning'])
        suggestions.extend(result['feedback']['suggestions'])
        
        # 计算熵值
        entropy = self._calculate_entropy(password)
        
        # 确定是否有效
        is_valid = (
            len(warnings) == 0 and
            strength.value >= self.min_strength.value and
            score >= 2
        )
        
        return PasswordValidationResult(
            is_valid=is_valid,
            strength=strength,
            score=score,
            entropy=entropy,
            warnings=warnings,
            suggestions=suggestions[:3],  # 限制建议数量
            crack_time_display=result['crack_times_display']['offline_slow_hashing_1e4_per_second'],
            crack_time_seconds=result['crack_times_seconds']['offline_slow_hashing_1e4_per_second']
        )
    
    def _has_repeated_chars(self, password: str, max_repeats: int) -> bool:
        """检查是否有过多连续重复字符"""
        count = 1
        for i in range(1, len(password)):
            if password[i] == password[i-1]:
                count += 1
                if count > max_repeats:
                    return True
            else:
                count = 1
        return False
    
    def _is_keyboard_sequence(self, password: str) -> bool:
        """检查是否包含键盘序列"""
        # 常见键盘序列
        sequences = [
            "qwertyuiop",
            "asdfghjkl",
            "zxcvbnm",
            "1234567890",
            "0987654321"
        ]
        
        lower_pass = password.lower()
        for seq in sequences:
            for i in range(len(seq) - 3):
                if seq[i:i+4] in lower_pass:
                    return True
        return False
    
    def _calculate_entropy(self, password: str) -> float:
        """计算密码熵值"""
        # 确定字符集大小
        charset_size = 0
        if re.search(r'[a-z]', password):
            charset_size += 26
        if re.search(r'[A-Z]', password):
            charset_size += 26
        if re.search(r'\d', password):
            charset_size += 10
        if re.search(r'[^a-zA-Z0-9]', password):
            charset_size += 33
        
        if charset_size == 0:
            return 0.0
        
        # 熵 = 长度 * log2(字符集大小)
        return len(password) * math.log2(charset_size)
    
    def hash_password(self, password: str) -> str:
        """哈希密码"""
        return self.pwd_context.hash(password)
    
    def verify_password(self, plain_password: str, hashed_password: str) -> bool:
        """验证密码"""
        return self.pwd_context.verify(plain_password, hashed_password)
    
    def generate_secure_password(self, length: int = 16) -> str:
        """
        生成安全密码
        
        Args:
            length: 密码长度
            
        Returns:
            安全随机密码
        """
        # 确保包含所有要求的字符类型
        password_chars = []
        
        if self.require_uppercase:
            password_chars.append(secrets.choice(string.ascii_uppercase))
        if self.require_lowercase:
            password_chars.append(secrets.choice(string.ascii_lowercase))
        if self.require_digits:
            password_chars.append(secrets.choice(string.digits))
        if self.require_special:
            password_chars.append(secrets.choice(self.SPECIAL_CHARS))
        
        # 填充剩余长度
        all_chars = ""
        if self.require_uppercase:
            all_chars += string.ascii_uppercase
        if self.require_lowercase:
            all_chars += string.ascii_lowercase
        if self.require_digits:
            all_chars += string.digits
        if self.require_special:
            all_chars += self.SPECIAL_CHARS
        
        for _ in range(length - len(password_chars)):
            password_chars.append(secrets.choice(all_chars))
        
        # 打乱顺序
        secrets.SystemRandom().shuffle(password_chars)
        
        return ''.join(password_chars)
    
    def is_password_expired(self, last_changed: datetime) -> bool:
        """检查密码是否已过期"""
        return datetime.utcnow() - last_changed > self.max_password_age
    
    def can_change_password(self, last_changed: datetime) -> bool:
        """检查是否可以更改密码（最小使用期限）"""
        return datetime.utcnow() - last_changed >= self.min_password_age


# 全局默认策略实例
default_policy = PasswordPolicy()


def validate_password(
    password: str,
    username: str = "",
    email: str = "",
    policy: Optional[PasswordPolicy] = None
) -> PasswordValidationResult:
    """
    验证密码（使用默认策略）
    
    Args:
        password: 待验证密码
        username: 用户名
        email: 邮箱
        policy: 自定义策略（可选）
        
    Returns:
        验证结果
    """
    if policy is None:
        policy = default_policy
    return policy.validate(password, username, email)


def hash_password(password: str, policy: Optional[PasswordPolicy] = None) -> str:
    """哈希密码"""
    if policy is None:
        policy = default_policy
    return policy.hash_password(password)


def verify_password(plain_password: str, hashed_password: str, policy: Optional[PasswordPolicy] = None) -> bool:
    """验证密码"""
    if policy is None:
        policy = default_policy
    return policy.verify_password(plain_password, hashed_password)
