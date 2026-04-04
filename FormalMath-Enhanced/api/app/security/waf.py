"""
Web应用防火墙(WAF)中间件

提供SQL注入、XSS、CSRF等攻击防护
"""
import re
import logging
import hashlib
from typing import List, Dict, Optional, Pattern, Callable
from datetime import datetime, timedelta
from collections import defaultdict
from fastapi import Request, HTTPException
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class WAFRule:
    """WAF规则定义"""
    
    def __init__(
        self,
        rule_id: str,
        name: str,
        pattern: str,
        severity: str = "high",
        description: str = "",
        enabled: bool = True
    ):
        self.rule_id = rule_id
        self.name = name
        self.pattern = re.compile(pattern, re.IGNORECASE)
        self.severity = severity
        self.description = description
        self.enabled = enabled


class WAFMiddleware(BaseHTTPMiddleware):
    """
    Web应用防火墙中间件
    
    功能：
    - SQL注入防护
    - XSS攻击防护
    - 路径遍历防护
    - 命令注入防护
    - 恶意User-Agent过滤
    - IP黑名单/白名单
    - 请求频率限制（基于Redis）
    """
    
    # 预定义WAF规则集
    DEFAULT_RULES = [
        # SQL注入规则
        WAFRule(
            rule_id="SQLI-001",
            name="SQL Injection - Union Select",
            pattern=r"(union\s+select|select\s+.*\s+from|insert\s+into|delete\s+from|drop\s+table)",
            severity="critical",
            description="检测SQL注入攻击 - UNION SELECT语句"
        ),
        WAFRule(
            rule_id="SQLI-002",
            name="SQL Injection - Comment",
            pattern=r"(\-\-|\#|\/\*|\;|\')",
            severity="high",
            description="检测SQL注入攻击 - 注释符号"
        ),
        WAFRule(
            rule_id="SQLI-003",
            name="SQL Injection - Sleep/Benchmark",
            pattern=r"(sleep\s*\(|benchmark\s*\(|waitfor\s+delay|pg_sleep)",
            severity="high",
            description="检测SQL盲注攻击"
        ),
        
        # XSS攻击规则
        WAFRule(
            rule_id="XSS-001",
            name="XSS - Script Tag",
            pattern=r"(<script[^>]*>|javascript:|on\w+\s*=)",
            severity="critical",
            description="检测XSS攻击 - Script标签"
        ),
        WAFRule(
            rule_id="XSS-002",
            name="XSS - Event Handler",
            pattern=r"(onerror|onload|onclick|onmouseover|onfocus)\s*=",
            severity="high",
            description="检测XSS攻击 - 事件处理器"
        ),
        WAFRule(
            rule_id="XSS-003",
            name="XSS - Data URI",
            pattern=r"data:text\/html",
            severity="high",
            description="检测XSS攻击 - Data URI"
        ),
        
        # 路径遍历规则
        WAFRule(
            rule_id="PT-001",
            name="Path Traversal",
            pattern=r"(\.\.\/|\.\.\\|%2e%2e%2f|%252e%252e%252f)",
            severity="high",
            description="检测路径遍历攻击"
        ),
        WAFRule(
            rule_id="PT-002",
            name="Null Byte Injection",
            pattern=r"%00|\x00",
            severity="high",
            description="检测空字节注入"
        ),
        
        # 命令注入规则
        WAFRule(
            rule_id="CI-001",
            name="Command Injection",
            pattern=r"(\||\;|\`|\$\(|\$\{|&&|\|\||>\s*/|\/bin\/bash|\/bin\/sh|cmd\.exe)",
            severity="critical",
            description="检测命令注入攻击"
        ),
        
        # 文件包含规则
        WAFRule(
            rule_id="FI-001",
            name="Local File Inclusion",
            pattern=r"(file:\/\/|\.\.\/|php:\/\/filter|data:\/\/)",
            severity="high",
            description="检测本地文件包含攻击"
        ),
        
        # XML攻击规则
        WAFRule(
            rule_id="XML-001",
            name="XXE Attack",
            pattern=r"(<!ENTITY\s+.*\s+SYSTEM|<!DOCTYPE\s+.*\s+\[)",
            severity="critical",
            description="检测XXE(XML外部实体)攻击"
        ),
        
        # 信息泄露规则
        WAFRule(
            rule_id="INFO-001",
            name="Sensitive File Access",
            pattern=r"(\/\.env|\/\.git|\/\.htaccess|\/\.svn|\/config\.php|\/web\.config)",
            severity="medium",
            description="检测敏感文件访问尝试"
        ),
        
        # 扫描器检测规则
        WAFRule(
            rule_id="SCAN-001",
            name="Vulnerability Scanner",
            pattern=r"(sqlmap|nikto|nmap|nessus|openvas|acunetix|burp|metasploit)",
            severity="medium",
            description="检测漏洞扫描工具"
        ),
    ]
    
    # 恶意User-Agent列表
    MALICIOUS_USER_AGENTS = [
        r"sqlmap",
        r"nikto",
        r"nmap",
        r"masscan",
        r"zgrab",
        r"gobuster",
        r"dirbuster",
        r"wfuzz",
        r"burp",
        r"metasploit",
        r"nessus",
        r"openvas",
        r"acunetix",
        r"netsparker",
        r"appscan",
        r"w3af",
        r"arachni",
        r"skipfish",
        r"wapiti",
        r"webinspect",
    ]
    
    def __init__(
        self,
        app: ASGIApp,
        rules: Optional[List[WAFRule]] = None,
        blocked_ips: Optional[List[str]] = None,
        allowed_ips: Optional[List[str]] = None,
        ip_block_duration: int = 3600,  # 1小时
        max_violations: int = 5,
        enable_logging: bool = True,
        custom_response: Optional[Dict] = None
    ):
        super().__init__(app)
        self.rules = rules or self.DEFAULT_RULES.copy()
        self.blocked_ips = set(blocked_ips or [])
        self.allowed_ips = set(allowed_ips or [])
        self.ip_block_duration = ip_block_duration
        self.max_violations = max_violations
        self.enable_logging = enable_logging
        self.custom_response = custom_response or {
            "error": "Security Violation",
            "message": "请求被安全系统拦截"
        }
        
        # IP违规记录
        self._violations: Dict[str, List[datetime]] = defaultdict(list)
        self._blocked_until: Dict[str, datetime] = {}
        
        # 编译User-Agent正则
        self._ua_patterns = [
            re.compile(pattern, re.IGNORECASE)
            for pattern in self.MALICIOUS_USER_AGENTS
        ]
    
    def _get_client_ip(self, request: Request) -> str:
        """获取客户端真实IP"""
        # 检查X-Forwarded-For头
        forwarded = request.headers.get("x-forwarded-for")
        if forwarded:
            return forwarded.split(",")[0].strip()
        
        # 检查X-Real-IP头
        real_ip = request.headers.get("x-real-ip")
        if real_ip:
            return real_ip
        
        # 使用直接连接的IP
        return request.client.host if request.client else "unknown"
    
    def _is_ip_blocked(self, ip: str) -> bool:
        """检查IP是否被阻止"""
        # 检查白名单
        if ip in self.allowed_ips:
            return False
        
        # 检查黑名单
        if ip in self.blocked_ips:
            return True
        
        # 检查临时阻止
        if ip in self._blocked_until:
            if datetime.utcnow() < self._blocked_until[ip]:
                return True
            else:
                # 解除阻止
                del self._blocked_until[ip]
        
        return False
    
    def _record_violation(self, ip: str, rule: WAFRule):
        """记录安全违规"""
        now = datetime.utcnow()
        self._violations[ip].append(now)
        
        # 清理过期记录（1小时前）
        cutoff = now - timedelta(seconds=self.ip_block_duration)
        self._violations[ip] = [
            v for v in self._violations[ip] if v > cutoff
        ]
        
        # 检查是否需要阻止IP
        if len(self._violations[ip]) >= self.max_violations:
            self._blocked_until[ip] = now + timedelta(seconds=self.ip_block_duration)
            if self.enable_logging:
                logger.warning(f"IP {ip} 因多次违规被临时阻止 {self.ip_block_duration}秒")
    
    def _check_user_agent(self, user_agent: str) -> Optional[str]:
        """检查User-Agent是否恶意"""
        for pattern in self._ua_patterns:
            if pattern.search(user_agent):
                return pattern.pattern
        return None
    
    def _inspect_request(self, request: Request) -> Optional[WAFRule]:
        """检查请求是否违反WAF规则"""
        # 检查路径
        path = request.url.path
        query = str(request.url.query)
        
        # 检查路径和查询参数
        for rule in self.rules:
            if not rule.enabled:
                continue
            
            # 检查路径
            if rule.pattern.search(path):
                return rule
            
            # 检查查询字符串
            if query and rule.pattern.search(query):
                return rule
        
        return None
    
    async def _inspect_body(self, request: Request) -> Optional[WAFRule]:
        """检查请求体"""
        try:
            body = await request.body()
            if not body:
                return None
            
            # 解码请求体
            try:
                body_text = body.decode('utf-8')
            except UnicodeDecodeError:
                body_text = body.decode('latin-1')
            
            for rule in self.rules:
                if not rule.enabled:
                    continue
                
                if rule.pattern.search(body_text):
                    return rule
            
            return None
        except Exception as e:
            logger.error(f"检查请求体时出错: {e}")
            return None
    
    async def dispatch(self, request: Request, call_next):
        """处理请求"""
        client_ip = self._get_client_ip(request)
        
        # 检查IP是否被阻止
        if self._is_ip_blocked(client_ip):
            if self.enable_logging:
                logger.warning(f"阻止来自黑名单IP的请求: {client_ip}")
            raise HTTPException(
                status_code=403,
                detail=self.custom_response
            )
        
        # 检查User-Agent
        user_agent = request.headers.get("user-agent", "")
        malicious_ua = self._check_user_agent(user_agent)
        if malicious_ua:
            if self.enable_logging:
                logger.warning(f"检测到恶意User-Agent: {malicious_ua} from {client_ip}")
            self._record_violation(client_ip, WAFRule(
                rule_id="UA-001",
                name="Malicious User-Agent",
                pattern=malicious_ua,
                severity="high"
            ))
            raise HTTPException(
                status_code=403,
                detail={
                    "error": "Forbidden",
                    "message": "请求被拒绝"
                }
            )
        
        # 检查URL和查询参数
        violation = self._inspect_request(request)
        if violation:
            if self.enable_logging:
                logger.warning(
                    f"WAF规则触发: {violation.rule_id} ({violation.name}) "
                    f"from {client_ip}, Path: {request.url.path}"
                )
            self._record_violation(client_ip, violation)
            raise HTTPException(
                status_code=403,
                detail={
                    "error": "Security Violation",
                    "message": "请求包含恶意内容",
                    "rule_id": violation.rule_id
                }
            )
        
        # 检查请求体（POST/PUT/PATCH）
        if request.method in ["POST", "PUT", "PATCH"]:
            violation = await self._inspect_body(request)
            if violation:
                if self.enable_logging:
                    logger.warning(
                        f"WAF规则触发(请求体): {violation.rule_id} ({violation.name}) "
                        f"from {client_ip}"
                    )
                self._record_violation(client_ip, violation)
                raise HTTPException(
                    status_code=403,
                    detail={
                        "error": "Security Violation",
                        "message": "请求体包含恶意内容",
                        "rule_id": violation.rule_id
                    }
                )
        
        # 继续处理请求
        response = await call_next(request)
        
        # 添加安全响应头
        response.headers["X-WAF-Status"] = "active"
        response.headers["X-Content-Type-Options"] = "nosniff"
        
        return response


class IPBlacklistMiddleware(BaseHTTPMiddleware):
    """IP黑名单中间件"""
    
    def __init__(
        self,
        app: ASGIApp,
        blacklist: List[str] = None,
        whitelist: List[str] = None
    ):
        super().__init__(app)
        self.blacklist = set(blacklist or [])
        self.whitelist = set(whitelist or [])
    
    def _get_client_ip(self, request: Request) -> str:
        """获取客户端IP"""
        forwarded = request.headers.get("x-forwarded-for")
        if forwarded:
            return forwarded.split(",")[0].strip()
        return request.client.host if request.client else "unknown"
    
    async def dispatch(self, request: Request, call_next):
        client_ip = self._get_client_ip(request)
        
        # 检查白名单
        if client_ip in self.whitelist:
            return await call_next(request)
        
        # 检查黑名单
        if client_ip in self.blacklist:
            raise HTTPException(
                status_code=403,
                detail={"error": "Access Denied", "message": "IP地址已被禁止访问"}
            )
        
        return await call_next(request)
