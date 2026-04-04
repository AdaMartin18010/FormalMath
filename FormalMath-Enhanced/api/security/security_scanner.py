"""
安全扫描工具

用于扫描代码、配置和依赖中的安全漏洞
"""
import os
import re
import json
import ast
import logging
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class SecurityIssue:
    """安全问题定义"""
    severity: str  # critical, high, medium, low, info
    category: str
    file: str
    line: int
    message: str
    recommendation: str
    code_snippet: Optional[str] = None


class SecurityScanner:
    """
    安全扫描器
    
    扫描内容：
    - 敏感信息泄露（密码、密钥等）
    - 不安全的代码模式
    - 依赖漏洞
    - 配置问题
    """
    
    # 敏感信息模式
    SENSITIVE_PATTERNS = {
        'password': [
            r'password\s*=\s*["\'][^"\']+["\']',
            r'passwd\s*=\s*["\'][^"\']+["\']',
            r'pwd\s*=\s*["\'][^"\']+["\']',
        ],
        'secret_key': [
            r'secret[_\-]?key\s*=\s*["\'][^"\']+["\']',
            r'api[_\-]?key\s*=\s*["\'][^"\']+["\']',
            r'auth[_\-]?token\s*=\s*["\'][^"\']+["\']',
        ],
        'private_key': [
            r'-----BEGIN (RSA |DSA |EC |OPENSSH )?PRIVATE KEY-----',
            r'private[_\-]?key\s*=\s*["\'][^"\']+["\']',
        ],
        'credential': [
            r'aws_access_key_id\s*=\s*["\'][^"\']+["\']',
            r'aws_secret_access_key\s*=\s*["\'][^"\']+["\']',
            r'database[_\-]?url\s*=\s*["\'][^"\']*://[^"\']+["\']',
        ],
    }
    
    # 不安全代码模式
    INSECURE_PATTERNS = {
        'eval': [
            r'\beval\s*\(',
            r'\bexec\s*\(',
        ],
        'pickle': [
            r'pickle\.loads?\s*\(',
            r'cPickle\.loads?\s*\(',
        ],
        'yaml': [
            r'yaml\.load\s*\([^,)]*\)',
        ],
        'sql': [
            r'\.execute\s*\(["\'].*%s',
            r'\.execute\s*\(["\'].*\+',
            r'\.execute\s*\(f["\']',
        ],
        'subprocess': [
            r'subprocess\.call\s*\([^)]*shell\s*=\s*True',
            r'subprocess\.Popen\s*\([^)]*shell\s*=\s*True',
            r'os\.system\s*\(',
            r'os\.popen\s*\(',
        ],
        'debug': [
            r'debug\s*=\s*True',
            r'DEBUG\s*=\s*True',
        ],
        'cors': [
            r'allow_origins\s*=\s*\[?["\']\*["\']',
            r'CORS_ORIGINS\s*=\s*\[?["\']\*["\']',
        ],
    }
    
    # 危险文件模式
    DANGEROUS_FILES = [
        r'\.env$',
        r'\.env\.local$',
        r'\.env\.production$',
        r'\.htpasswd$',
        r'\.netrc$',
        r'id_rsa$',
        r'id_dsa$',
        r'\.pem$',
        r'\.key$',
        r'credentials\.json$',
        r'secrets\.json$',
    ]
    
    def __init__(self, project_path: str):
        self.project_path = Path(project_path)
        self.issues: List[SecurityIssue] = []
    
    def scan_all(self) -> List[SecurityIssue]:
        """执行完整的安全扫描"""
        logger.info("开始安全扫描...")
        
        self.scan_sensitive_info()
        self.scan_insecure_patterns()
        self.scan_dangerous_files()
        self.scan_dependencies()
        self.scan_configuration()
        
        logger.info(f"扫描完成，发现 {len(self.issues)} 个问题")
        return self.issues
    
    def scan_sensitive_info(self):
        """扫描敏感信息泄露"""
        logger.info("扫描敏感信息...")
        
        python_files = list(self.project_path.rglob("*.py"))
        config_files = list(self.project_path.rglob("*.env*"))
        config_files.extend(self.project_path.rglob("*.yaml"))
        config_files.extend(self.project_path.rglob("*.yml"))
        config_files.extend(self.project_path.rglob("*.json"))
        
        for file_path in python_files + config_files:
            if self._should_skip_file(file_path):
                continue
            
            try:
                content = file_path.read_text(encoding='utf-8', errors='ignore')
                lines = content.split('\n')
                
                for category, patterns in self.SENSITIVE_PATTERNS.items():
                    for pattern in patterns:
                        for i, line in enumerate(lines, 1):
                            if re.search(pattern, line, re.IGNORECASE):
                                # 排除注释和示例
                                if not line.strip().startswith('#') and 'example' not in line.lower():
                                    self.issues.append(SecurityIssue(
                                        severity='critical' if category == 'private_key' else 'high',
                                        category='sensitive_data',
                                        file=str(file_path.relative_to(self.project_path)),
                                        line=i,
                                        message=f"发现可能的{category}泄露",
                                        recommendation="使用环境变量或密钥管理服务存储敏感信息",
                                        code_snippet=line.strip()
                                    ))
            except Exception as e:
                logger.warning(f"无法读取文件 {file_path}: {e}")
    
    def scan_insecure_patterns(self):
        """扫描不安全的代码模式"""
        logger.info("扫描不安全代码模式...")
        
        python_files = list(self.project_path.rglob("*.py"))
        
        for file_path in python_files:
            if self._should_skip_file(file_path):
                continue
            
            try:
                content = file_path.read_text(encoding='utf-8', errors='ignore')
                lines = content.split('\n')
                
                for category, patterns in self.INSECURE_PATTERNS.items():
                    for pattern in patterns:
                        for i, line in enumerate(lines, 1):
                            if re.search(pattern, line, re.IGNORECASE):
                                # 排除注释
                                if not line.strip().startswith('#'):
                                    severity = self._get_severity_for_pattern(category)
                                    self.issues.append(SecurityIssue(
                                        severity=severity,
                                        category='insecure_code',
                                        file=str(file_path.relative_to(self.project_path)),
                                        line=i,
                                        message=f"发现不安全的{category}使用",
                                        recommendation=self._get_recommendation(category),
                                        code_snippet=line.strip()
                                    ))
            except Exception as e:
                logger.warning(f"无法读取文件 {file_path}: {e}")
    
    def scan_dangerous_files(self):
        """扫描危险文件"""
        logger.info("扫描危险文件...")
        
        for pattern in self.DANGEROUS_FILES:
            for file_path in self.project_path.rglob("*"):
                if file_path.is_file() and re.search(pattern, file_path.name):
                    self.issues.append(SecurityIssue(
                        severity='high',
                        category='dangerous_file',
                        file=str(file_path.relative_to(self.project_path)),
                        line=0,
                        message=f"发现敏感文件: {file_path.name}",
                        recommendation="将敏感文件添加到.gitignore，并使用权限控制访问"
                    ))
    
    def scan_dependencies(self):
        """扫描依赖漏洞"""
        logger.info("扫描依赖...")
        
        req_file = self.project_path / "requirements.txt"
        if req_file.exists():
            try:
                content = req_file.read_text()
                # 检查常见的有漏洞的包
                vulnerable_packages = {
                    'requests': ('2.20.0', 'CVE-2018-18074'),
                    'urllib3': ('1.24.2', 'CVE-2019-11324'),
                    'pyyaml': ('5.1', 'CVE-2019-14276'),
                    'jinja2': ('2.10.1', 'CVE-2019-10906'),
                    'flask': ('1.0', 'CVE-2018-1000656'),
                    'django': ('2.0', 'CVE-2018-14574'),
                }
                
                for package, (min_version, cve) in vulnerable_packages.items():
                    if package in content.lower():
                        self.issues.append(SecurityIssue(
                            severity='medium',
                            category='vulnerable_dependency',
                            file='requirements.txt',
                            line=0,
                            message=f"包 {package} 可能存在已知漏洞 ({cve})",
                            recommendation=f"请升级到 {min_version} 或更高版本"
                        ))
            except Exception as e:
                logger.warning(f"无法读取依赖文件: {e}")
    
    def scan_configuration(self):
        """扫描配置问题"""
        logger.info("扫描配置...")
        
        # 检查DEBUG模式
        config_files = list(self.project_path.rglob("config.py"))
        config_files.extend(self.project_path.rglob("settings.py"))
        config_files.extend(self.project_path.rglob(".env"))
        
        for file_path in config_files:
            try:
                content = file_path.read_text()
                if 'DEBUG = True' in content or 'DEBUG=True' in content:
                    self.issues.append(SecurityIssue(
                        severity='medium',
                        category='configuration',
                        file=str(file_path.relative_to(self.project_path)),
                        line=0,
                        message="生产环境启用DEBUG模式",
                        recommendation="生产环境应禁用DEBUG模式"
                    ))
            except Exception as e:
                logger.warning(f"无法读取配置文件 {file_path}: {e}")
        
        # 检查HTTPS配置
        nginx_conf = self.project_path / "nginx_ssl.conf"
        if not nginx_conf.exists():
            self.issues.append(SecurityIssue(
                severity='medium',
                category='configuration',
                file='',
                line=0,
                message="未找到Nginx SSL配置文件",
                recommendation="配置HTTPS以确保通信安全"
            ))
    
    def _should_skip_file(self, file_path: Path) -> bool:
        """检查是否应该跳过文件"""
        skip_dirs = ['__pycache__', '.git', '.venv', 'venv', 'node_modules', '.pytest_cache']
        return any(part in skip_dirs for part in file_path.parts)
    
    def _get_severity_for_pattern(self, category: str) -> str:
        """获取模式对应的严重级别"""
        severity_map = {
            'eval': 'critical',
            'pickle': 'high',
            'yaml': 'high',
            'sql': 'critical',
            'subprocess': 'high',
            'debug': 'medium',
            'cors': 'medium',
        }
        return severity_map.get(category, 'medium')
    
    def _get_recommendation(self, category: str) -> str:
        """获取修复建议"""
        recommendations = {
            'eval': '避免使用eval()，使用ast.literal_eval()替代或重新设计代码',
            'pickle': '避免对不可信数据使用pickle，使用JSON替代',
            'yaml': '使用yaml.safe_load()替代yaml.load()',
            'sql': '使用参数化查询防止SQL注入',
            'subprocess': '避免使用shell=True，对用户输入进行严格验证',
            'debug': '生产环境禁用DEBUG模式',
            'cors': '明确指定允许的CORS来源，不要使用通配符',
        }
        return recommendations.get(category, '检查并修复代码')
    
    def generate_report(self, output_path: str = None) -> str:
        """生成安全扫描报告"""
        report = {
            'scan_time': datetime.now().isoformat(),
            'project_path': str(self.project_path),
            'total_issues': len(self.issues),
            'severity_counts': self._count_by_severity(),
            'category_counts': self._count_by_category(),
            'issues': [asdict(issue) for issue in self.issues]
        }
        
        json_report = json.dumps(report, indent=2, ensure_ascii=False)
        
        if output_path:
            Path(output_path).write_text(json_report, encoding='utf-8')
            logger.info(f"报告已保存到: {output_path}")
        
        return json_report
    
    def _count_by_severity(self) -> Dict[str, int]:
        """按严重级别统计问题"""
        counts = {'critical': 0, 'high': 0, 'medium': 0, 'low': 0, 'info': 0}
        for issue in self.issues:
            counts[issue.severity] = counts.get(issue.severity, 0) + 1
        return counts
    
    def _count_by_category(self) -> Dict[str, int]:
        """按类别统计问题"""
        counts = {}
        for issue in self.issues:
            counts[issue.category] = counts.get(issue.category, 0) + 1
        return counts


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath API 安全扫描工具')
    parser.add_argument('path', help='项目路径')
    parser.add_argument('-o', '--output', help='输出报告路径')
    parser.add_argument('--format', choices=['json', 'text'], default='json', help='输出格式')
    
    args = parser.parse_args()
    
    scanner = SecurityScanner(args.path)
    scanner.scan_all()
    
    if args.format == 'json':
        report = scanner.generate_report(args.output)
        if not args.output:
            print(report)
    else:
        # 文本格式
        print(f"\n{'='*60}")
        print("FormalMath API 安全扫描报告")
        print(f"{'='*60}")
        print(f"扫描时间: {datetime.now().isoformat()}")
        print(f"项目路径: {args.path}")
        print(f"发现问题: {len(scanner.issues)} 个")
        print(f"\n严重级别统计:")
        for severity, count in scanner._count_by_severity().items():
            print(f"  {severity.upper()}: {count}")
        
        print(f"\n{'-'*60}")
        print("详细问题列表:")
        print(f"{'-'*60}")
        
        for issue in scanner.issues:
            print(f"\n[{issue.severity.upper()}] {issue.category}")
            print(f"  文件: {issue.file}:{issue.line}")
            print(f"  描述: {issue.message}")
            print(f"  建议: {issue.recommendation}")
            if issue.code_snippet:
                print(f"  代码: {issue.code_snippet[:100]}")


if __name__ == '__main__':
    main()
