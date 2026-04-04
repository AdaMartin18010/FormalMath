"""
邮件模板管理系统
支持多语言、变量替换和模板继承
"""
import os
import json
from typing import Dict, Any, Optional, List
from dataclasses import dataclass
from pathlib import Path
from string import Template
from functools import lru_cache
import aiofiles

from ..core.email_config import email_settings


@dataclass
class EmailTemplate:
    """邮件模板数据结构"""
    name: str
    subject: str
    html_content: str
    text_content: Optional[str] = None
    language: str = "zh_CN"
    description: str = ""
    variables: List[str] = None
    
    def __post_init__(self):
        if self.variables is None:
            self.variables = []


class TemplateManager:
    """邮件模板管理器"""
    
    # 内置模板定义
    BUILTIN_TEMPLATES = {
        "welcome": {
            "subject": "欢迎加入 FormalMath - 开启您的数学学习之旅",
            "description": "新用户注册欢迎邮件",
            "variables": ["username", "verification_link"],
        },
        "verification": {
            "subject": "验证您的邮箱地址",
            "description": "邮箱验证邮件",
            "variables": ["username", "verification_code", "expires_minutes"],
        },
        "password_reset": {
            "subject": "密码重置请求",
            "description": "密码重置邮件",
            "variables": ["username", "reset_link", "expires_hours"],
        },
        "learning_reminder": {
            "subject": "今日学习提醒 - 保持学习节奏",
            "description": "学习提醒邮件",
            "variables": ["username", "streak_days", "recommended_concepts"],
        },
        "achievement_unlocked": {
            "subject": "恭喜！您解锁了新成就",
            "description": "成就解锁通知",
            "variables": ["username", "achievement_name", "achievement_description", "badge_icon"],
        },
        "learning_path_complete": {
            "subject": "恭喜完成学习路径！",
            "description": "学习路径完成通知",
            "variables": ["username", "path_name", "completed_nodes", "total_nodes", "certificate_link"],
        },
        "weekly_report": {
            "subject": "您的学习周报 - 本周学习成果",
            "description": "每周学习报告",
            "variables": [
                "username",
                "week_start",
                "week_end",
                "study_hours",
                "concepts_learned",
                "quizzes_completed",
                "accuracy_rate",
            ],
        },
        "new_follower": {
            "subject": "您有新的关注者",
            "description": "新关注者通知",
            "variables": ["username", "follower_name", "follower_profile_link"],
        },
        "challenge_invitation": {
            "subject": "您收到了一个挑战邀请",
            "description": "挑战邀请邮件",
            "variables": [
                "username",
                "challenger_name",
                "challenge_name",
                "challenge_description",
                "accept_link",
            ],
        },
        "system_maintenance": {
            "subject": "系统维护通知",
            "description": "系统维护公告",
            "variables": ["maintenance_time", "expected_duration", "affected_services"],
        },
        "security_alert": {
            "subject": "安全提醒 - 检测到异常登录",
            "description": "安全警报邮件",
            "variables": ["username", "login_time", "login_location", "device_info", "secure_account_link"],
        },
    }
    
    def __init__(self):
        self.templates: Dict[str, Dict[str, EmailTemplate]] = {}
        self.template_dir = Path(email_settings.EMAIL_TEMPLATE_DIR)
        self._load_builtin_templates()
    
    def _load_builtin_templates(self):
        """加载内置模板"""
        for template_name, template_info in self.BUILTIN_TEMPLATES.items():
            for lang in ["zh_CN", "en_US"]:
                template = self._create_builtin_template(
                    template_name, template_info, lang
                )
                if template_name not in self.templates:
                    self.templates[template_name] = {}
                self.templates[template_name][lang] = template
    
    def _create_builtin_template(
        self,
        name: str,
        info: Dict[str, Any],
        language: str,
    ) -> EmailTemplate:
        """创建内置模板"""
        
        # 根据语言和模板名称生成内容
        html_content = self._generate_template_html(name, language)
        text_content = self._generate_template_text(name, language)
        
        subject = info["subject"]
        if language == "en_US":
            subject = self._translate_subject(subject, name)
        
        return EmailTemplate(
            name=name,
            subject=subject,
            html_content=html_content,
            text_content=text_content,
            language=language,
            description=info["description"],
            variables=info["variables"],
        )
    
    def _generate_template_html(self, name: str, language: str) -> str:
        """生成模板 HTML 内容"""
        
        base_html = """<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{subject}}</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; margin: 0; padding: 0; background-color: #f5f5f5; }
        .container { max-width: 600px; margin: 0 auto; background-color: #ffffff; }
        .header { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); padding: 40px 20px; text-align: center; }
        .header h1 { color: #ffffff; margin: 0; font-size: 24px; }
        .content { padding: 40px 30px; }
        .footer { background-color: #f8f9fa; padding: 20px; text-align: center; font-size: 12px; color: #6c757d; }
        .btn { display: inline-block; padding: 12px 30px; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); color: #ffffff; text-decoration: none; border-radius: 5px; margin: 20px 0; }
        .highlight { background-color: #e7f3ff; padding: 15px; border-left: 4px solid #667eea; margin: 15px 0; }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>{{header_title}}</h1>
        </div>
        <div class="content">
            {{body_content}}
        </div>
        <div class="footer">
            <p>{{footer_text}}</p>
            <p>{{unsubscribe_text}}</p>
        </div>
    </div>
</body>
</html>"""
        
        # 根据模板类型替换内容
        content_map = self._get_template_content_map(name, language)
        
        html = base_html
        for key, value in content_map.items():
            html = html.replace(f"{{{{{key}}}}}", value)
        
        return html
    
    def _generate_template_text(self, name: str, language: str) -> str:
        """生成模板纯文本内容"""
        content_map = self._get_template_content_map(name, language)
        return f"""{content_map['header_title']}

{content_map['body_content_text']}

---
{content_map['footer_text']}
"""
    
    def _get_template_content_map(self, name: str, language: str) -> Dict[str, str]:
        """获取模板内容映射"""
        
        is_zh = language == "zh_CN"
        
        content_maps = {
            "welcome": {
                "header_title": "欢迎加入 FormalMath" if is_zh else "Welcome to FormalMath",
                "body_content": """
                <p>您好 {{username}}，</p>
                <p>欢迎加入 FormalMath！我们很高兴您开启数学学习之旅。</p>
                <div class="highlight">
                    <p><strong>下一步：</strong>请验证您的邮箱地址以解锁全部功能。</p>
                </div>
                <p style="text-align: center;">
                    <a href="{{verification_link}}" class="btn">验证邮箱</a>
                </p>
                <p>如果您有任何问题，请随时联系我们的支持团队。</p>
                <p>祝您学习愉快！<br>FormalMath 团队</p>
                """ if is_zh else """
                <p>Hi {{username}},</p>
                <p>Welcome to FormalMath! We're excited to have you start your math learning journey.</p>
                <div class="highlight">
                    <p><strong>Next Step:</strong> Please verify your email address to unlock all features.</p>
                </div>
                <p style="text-align: center;">
                    <a href="{{verification_link}}" class="btn">Verify Email</a>
                </p>
                <p>If you have any questions, please contact our support team.</p>
                <p>Happy learning!<br>The FormalMath Team</p>
                """,
                "body_content_text": """您好 {{username}}，
欢迎加入 FormalMath！我们很高兴您开启数学学习之旅。

下一步：请验证您的邮箱地址以解锁全部功能。
验证链接：{{verification_link}}

如果您有任何问题，请随时联系我们的支持团队。

祝您学习愉快！
FormalMath 团队""" if is_zh else """Hi {{username}},
Welcome to FormalMath! We're excited to have you start your math learning journey.

Next Step: Please verify your email address to unlock all features.
Verification Link: {{verification_link}}

If you have any questions, please contact our support team.

Happy learning!
The FormalMath Team""",
                "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
                "unsubscribe_text": "管理邮件偏好 | 隐私政策" if is_zh else "Email Preferences | Privacy Policy",
            },
            "verification": {
                "header_title": "邮箱验证" if is_zh else "Email Verification",
                "body_content": """
                <p>您好 {{username}}，</p>
                <p>您的验证码是：</p>
                <div class="highlight" style="text-align: center;">
                    <h2 style="margin: 0; letter-spacing: 10px;">{{verification_code}}</h2>
                </div>
                <p>此验证码将在 {{expires_minutes}} 分钟后过期。</p>
                <p>如果您没有请求此验证码，请忽略此邮件。</p>
                """ if is_zh else """
                <p>Hi {{username}},</p>
                <p>Your verification code is:</p>
                <div class="highlight" style="text-align: center;">
                    <h2 style="margin: 0; letter-spacing: 10px;">{{verification_code}}</h2>
                </div>
                <p>This code will expire in {{expires_minutes}} minutes.</p>
                <p>If you didn't request this code, please ignore this email.</p>
                """,
                "body_content_text": """您好 {{username}}，
您的验证码是：{{verification_code}}

此验证码将在 {{expires_minutes}} 分钟后过期。

如果您没有请求此验证码，请忽略此邮件。""" if is_zh else """Hi {{username}},
Your verification code is: {{verification_code}}

This code will expire in {{expires_minutes}} minutes.

If you didn't request this code, please ignore this email.""",
                "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
                "unsubscribe_text": "",
            },
            "password_reset": {
                "header_title": "密码重置" if is_zh else "Password Reset",
                "body_content": """
                <p>您好 {{username}}，</p>
                <p>我们收到了您的密码重置请求。</p>
                <p style="text-align: center;">
                    <a href="{{reset_link}}" class="btn">重置密码</a>
                </p>
                <p>此链接将在 {{expires_hours}} 小时后过期。</p>
                <p>如果您没有请求重置密码，请忽略此邮件或联系支持团队。</p>
                """ if is_zh else """
                <p>Hi {{username}},</p>
                <p>We received a request to reset your password.</p>
                <p style="text-align: center;">
                    <a href="{{reset_link}}" class="btn">Reset Password</a>
                </p>
                <p>This link will expire in {{expires_hours}} hours.</p>
                <p>If you didn't request a password reset, please ignore this email or contact support.</p>
                """,
                "body_content_text": """您好 {{username}}，
我们收到了您的密码重置请求。

重置链接：{{reset_link}}

此链接将在 {{expires_hours}} 小时后过期。

如果您没有请求重置密码，请忽略此邮件或联系支持团队。""" if is_zh else """Hi {{username}},
We received a request to reset your password.

Reset Link: {{reset_link}}

This link will expire in {{expires_hours}} hours.

If you didn't request a password reset, please ignore this email or contact support.""",
                "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
                "unsubscribe_text": "",
            },
            "learning_reminder": {
                "header_title": "学习提醒" if is_zh else "Learning Reminder",
                "body_content": """
                <p>您好 {{username}}，</p>
                <p>您已连续学习 <strong>{{streak_days}}</strong> 天！继续保持这个好习惯。</p>
                <div class="highlight">
                    <p><strong>今日推荐：</strong></p>
                    <p>{{recommended_concepts}}</p>
                </div>
                <p style="text-align: center;">
                    <a href="https://formalmath.edu/learn" class="btn">开始学习</a>
                </p>
                """ if is_zh else """
                <p>Hi {{username}},</p>
                <p>You've been learning for <strong>{{streak_days}}</strong> consecutive days! Keep up the good habit.</p>
                <div class="highlight">
                    <p><strong>Today's Recommendations:</strong></p>
                    <p>{{recommended_concepts}}</p>
                </div>
                <p style="text-align: center;">
                    <a href="https://formalmath.edu/learn" class="btn">Start Learning</a>
                </p>
                """,
                "body_content_text": """您好 {{username}}，
您已连续学习 {{streak_days}} 天！继续保持这个好习惯。

今日推荐：{{recommended_concepts}}

开始学习：https://formalmath.edu/learn""" if is_zh else """Hi {{username}},
You've been learning for {{streak_days}} consecutive days! Keep up the good habit.

Today's Recommendations: {{recommended_concepts}}

Start Learning: https://formalmath.edu/learn""",
                "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
                "unsubscribe_text": "管理邮件偏好" if is_zh else "Email Preferences",
            },
            "achievement_unlocked": {
                "header_title": "成就解锁！" if is_zh else "Achievement Unlocked!",
                "body_content": """
                <p>恭喜 {{username}}！</p>
                <div class="highlight" style="text-align: center;">
                    <div style="font-size: 48px; margin: 20px 0;">{{badge_icon}}</div>
                    <h2>{{achievement_name}}</h2>
                    <p>{{achievement_description}}</p>
                </div>
                <p style="text-align: center;">
                    <a href="https://formalmath.edu/achievements" class="btn">查看所有成就</a>
                </p>
                """ if is_zh else """
                <p>Congratulations {{username}}!</p>
                <div class="highlight" style="text-align: center;">
                    <div style="font-size: 48px; margin: 20px 0;">{{badge_icon}}</div>
                    <h2>{{achievement_name}}</h2>
                    <p>{{achievement_description}}</p>
                </div>
                <p style="text-align: center;">
                    <a href="https://formalmath.edu/achievements" class="btn">View All Achievements</a>
                </p>
                """,
                "body_content_text": """恭喜 {{username}}！

🏆 {{achievement_name}}
{{achievement_description}}

查看所有成就：https://formalmath.edu/achievements""" if is_zh else """Congratulations {{username}}!

🏆 {{achievement_name}}
{{achievement_description}}

View All Achievements: https://formalmath.edu/achievements""",
                "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
                "unsubscribe_text": "管理邮件偏好" if is_zh else "Email Preferences",
            },
        }
        
        # 默认内容
        default_map = {
            "header_title": "FormalMath" if is_zh else "FormalMath",
            "body_content": "<p>{{content}}</p>",
            "body_content_text": "{{content}}",
            "footer_text": "此邮件由 FormalMath 自动发送" if is_zh else "This email was sent automatically by FormalMath",
            "unsubscribe_text": "管理邮件偏好 | 隐私政策" if is_zh else "Email Preferences | Privacy Policy",
        }
        
        return content_maps.get(name, default_map)
    
    def _translate_subject(self, subject: str, template_name: str) -> str:
        """翻译主题"""
        translations = {
            "welcome": "Welcome to FormalMath - Start Your Math Journey",
            "verification": "Verify Your Email Address",
            "password_reset": "Password Reset Request",
            "learning_reminder": "Daily Learning Reminder - Keep Up the Pace",
            "achievement_unlocked": "Congratulations! You've Unlocked a New Achievement",
            "learning_path_complete": "Congratulations on Completing Your Learning Path!",
            "weekly_report": "Your Weekly Learning Report",
            "new_follower": "You Have a New Follower",
            "challenge_invitation": "You've Received a Challenge Invitation",
            "system_maintenance": "System Maintenance Notice",
            "security_alert": "Security Alert - Unusual Login Detected",
        }
        return translations.get(template_name, subject)
    
    def get_template(
        self,
        template_name: str,
        language: str = None,
    ) -> Optional[EmailTemplate]:
        """
        获取邮件模板
        
        Args:
            template_name: 模板名称
            language: 语言代码，默认使用配置
        
        Returns:
            邮件模板对象
        """
        lang = language or email_settings.EMAIL_DEFAULT_LANGUAGE
        
        if template_name not in self.templates:
            return None
        
        # 尝试获取指定语言的模板
        if lang in self.templates[template_name]:
            return self.templates[template_name][lang]
        
        # 回退到默认语言
        if email_settings.EMAIL_DEFAULT_LANGUAGE in self.templates[template_name]:
            return self.templates[template_name][email_settings.EMAIL_DEFAULT_LANGUAGE]
        
        # 返回第一个可用语言
        return next(iter(self.templates[template_name].values()))
    
    def render_template(
        self,
        template_name: str,
        variables: Dict[str, Any],
        language: str = None,
    ) -> Dict[str, str]:
        """
        渲染邮件模板
        
        Args:
            template_name: 模板名称
            variables: 模板变量
            language: 语言代码
        
        Returns:
            包含 subject、html、text 的字典
        """
        template = self.get_template(template_name, language)
        
        if not template:
            raise ValueError(f"Template not found: {template_name}")
        
        # 使用 Jinja2 风格的模板替换
        subject = self._render_string(template.subject, variables)
        html_content = self._render_string(template.html_content, variables)
        text_content = None
        if template.text_content:
            text_content = self._render_string(template.text_content, variables)
        
        return {
            "subject": subject,
            "html": html_content,
            "text": text_content,
        }
    
    def _render_string(self, template_str: str, variables: Dict[str, Any]) -> str:
        """渲染字符串模板"""
        result = template_str
        for key, value in variables.items():
            placeholder = f"{{{{{key}}}}}"
            result = result.replace(placeholder, str(value))
        return result
    
    def list_templates(self) -> List[Dict[str, Any]]:
        """列出所有可用模板"""
        result = []
        for name, langs in self.templates.items():
            template_info = {
                "name": name,
                "languages": list(langs.keys()),
                "description": next(iter(langs.values())).description,
                "variables": next(iter(langs.values())).variables,
            }
            result.append(template_info)
        return result
    
    async def load_custom_templates(self):
        """从文件加载自定义模板"""
        if not self.template_dir.exists():
            return
        
        for template_file in self.template_dir.glob("*.json"):
            try:
                async with aiofiles.open(template_file, "r", encoding="utf-8") as f:
                    content = await f.read()
                    data = json.loads(content)
                
                template = EmailTemplate(
                    name=data["name"],
                    subject=data["subject"],
                    html_content=data["html_content"],
                    text_content=data.get("text_content"),
                    language=data.get("language", "zh_CN"),
                    description=data.get("description", ""),
                    variables=data.get("variables", []),
                )
                
                if template.name not in self.templates:
                    self.templates[template.name] = {}
                self.templates[template.name][template.language] = template
                
            except Exception as e:
                print(f"Failed to load template {template_file}: {e}")
    
    async def save_template(self, template: EmailTemplate):
        """保存自定义模板到文件"""
        self.template_dir.mkdir(parents=True, exist_ok=True)
        
        file_path = self.template_dir / f"{template.name}_{template.language}.json"
        
        data = {
            "name": template.name,
            "subject": template.subject,
            "html_content": template.html_content,
            "text_content": template.text_content,
            "language": template.language,
            "description": template.description,
            "variables": template.variables,
        }
        
        async with aiofiles.open(file_path, "w", encoding="utf-8") as f:
            await f.write(json.dumps(data, ensure_ascii=False, indent=2))
        
        # 更新内存中的模板
        if template.name not in self.templates:
            self.templates[template.name] = {}
        self.templates[template.name][template.language] = template


@lru_cache()
def get_template_manager() -> TemplateManager:
    """获取模板管理器实例"""
    return TemplateManager()
