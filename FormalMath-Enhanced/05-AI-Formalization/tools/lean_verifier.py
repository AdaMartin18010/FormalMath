"""
Lean4验证器模块
用于自动验证Lean4代码语法和类型检查
"""

import os
import re
import json
import logging
import tempfile
import subprocess
from typing import Optional, Dict, Any, List, Tuple
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class VerificationStatus(Enum):
    """验证状态"""
    SUCCESS = "success"
    SYNTAX_ERROR = "syntax_error"
    TYPE_ERROR = "type_error"
    TIMEOUT = "timeout"
    RUNTIME_ERROR = "runtime_error"
    UNKNOWN = "unknown"


@dataclass
class LeanError:
    """Lean错误信息"""
    line: int
    column: int
    message: str
    error_type: str
    severity: str = "error"  # error, warning, info


@dataclass
class VerificationResult:
    """验证结果"""
    status: VerificationStatus
    is_valid: bool
    errors: List[LeanError] = field(default_factory=list)
    warnings: List[LeanError] = field(default_factory=list)
    elapsed_time_ms: float = 0.0
    lean_version: str = ""
    mathlib_version: str = ""
    stdout: str = ""
    stderr: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class LeanProjectConfig:
    """Lean项目配置"""
    project_path: str
    lake_file: str = "lakefile.lean"
    mathlib_path: Optional[str] = None
    timeout_seconds: int = 60
    lean_exe: str = "lean"
    lake_exe: str = "lake"


class LeanVerifier:
    """
    Lean4验证器
    
    功能：
    - 自动验证Lean4代码语法
    - 调用Mathlib4进行类型检查
    - 生成验证报告
    """
    
    # Mathlib4常用导入
    COMMON_IMPORTS = [
        "import Mathlib.Data.Nat.Basic",
        "import Mathlib.Data.Int.Basic",
        "import Mathlib.Data.Real.Basic",
        "import Mathlib.Data.Set.Basic",
        "import Mathlib.Algebra.Group.Basic",
        "import Mathlib.Algebra.Ring.Basic",
        "import Mathlib.Topology.Basic",
        "import Mathlib.Analysis.NormedSpace.Basic",
        "import Mathlib.NumberTheory.Divisors",
        "import Mathlib.Combinatorics.SimpleGraph.Basic"
    ]
    
    def __init__(self, config: Optional[LeanProjectConfig] = None):
        """
        初始化验证器
        
        Args:
            config: 项目配置，如果为None则使用默认配置
        """
        if config is None:
            config = LeanProjectConfig(
                project_path=os.getenv("LEAN_PROJECT_PATH", "."),
                timeout_seconds=int(os.getenv("LEAN_TIMEOUT", "60"))
            )
        
        self.config = config
        self._check_lean_installation()
    
    def _check_lean_installation(self) -> None:
        """检查Lean安装"""
        try:
            result = subprocess.run(
                [self.config.lean_exe, "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            version = result.stdout.strip() or result.stderr.strip()
            logger.info(f"Lean version: {version}")
        except FileNotFoundError:
            logger.warning(f"Lean executable '{self.config.lean_exe}' not found. "
                          "Please ensure Lean 4 is installed.")
        except Exception as e:
            logger.warning(f"Could not check Lean version: {e}")
    
    def _create_temp_file(self, code: str, suffix: str = ".lean") -> str:
        """创建临时文件"""
        with tempfile.NamedTemporaryFile(
            mode='w', 
            suffix=suffix, 
            delete=False,
            encoding='utf-8'
        ) as f:
            f.write(code)
            return f.name
    
    def _parse_lean_output(self, stdout: str, stderr: str) -> Tuple[List[LeanError], List[LeanError]]:
        """
        解析Lean输出，提取错误和警告
        
        Lean错误格式示例：
        /path/to/file.lean:10:5: error: unknown identifier 'x'
        /path/to/file.lean:15:3: warning: unused variable
        """
        errors = []
        warnings = []
        
        # 合并stdout和stderr
        output = stdout + "\n" + stderr
        
        # 正则表达式匹配错误/警告
        pattern = r'([^:]+):(\d+):(\d+):\s*(error|warning|info):\s*(.+?)(?=\n[^\s]|\Z)'
        matches = re.findall(pattern, output, re.DOTALL)
        
        for match in matches:
            file_path, line, col, severity, message = match
            error_info = LeanError(
                line=int(line),
                column=int(col),
                message=message.strip().replace('\n', ' '),
                error_type="lean",
                severity=severity
            )
            
            if severity == "error":
                errors.append(error_info)
            elif severity == "warning":
                warnings.append(error_info)
        
        return errors, warnings
    
    def verify(self, code: str, use_temp_file: bool = True) -> VerificationResult:
        """
        验证Lean4代码
        
        Args:
            code: Lean4代码字符串
            use_temp_file: 是否使用临时文件
            
        Returns:
            验证结果
        """
        import time
        start_time = time.time()
        
        temp_file = None
        
        try:
            if use_temp_file:
                temp_file = self._create_temp_file(code)
                file_path = temp_file
            else:
                # 假设code是文件路径
                file_path = code
            
            # 构建Lean命令
            cmd = [
                self.config.lean_exe,
                file_path,
                "--json"  # JSON输出格式（如果支持）
            ]
            
            logger.info(f"Running: {' '.join(cmd)}")
            
            # 执行验证
            process = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.config.timeout_seconds,
                cwd=self.config.project_path
            )
            
            elapsed = (time.time() - start_time) * 1000
            
            # 解析输出
            errors, warnings = self._parse_lean_output(process.stdout, process.stderr)
            
            # 确定状态
            if process.returncode == 0 and not errors:
                status = VerificationStatus.SUCCESS
                is_valid = True
            elif errors:
                if any("expected" in e.message.lower() or "syntax" in e.message.lower() 
                       for e in errors):
                    status = VerificationStatus.SYNTAX_ERROR
                else:
                    status = VerificationStatus.TYPE_ERROR
                is_valid = False
            else:
                status = VerificationStatus.UNKNOWN
                is_valid = False
            
            return VerificationResult(
                status=status,
                is_valid=is_valid,
                errors=errors,
                warnings=warnings,
                elapsed_time_ms=elapsed,
                stdout=process.stdout,
                stderr=process.stderr
            )
            
        except subprocess.TimeoutExpired:
            elapsed = (time.time() - start_time) * 1000
            return VerificationResult(
                status=VerificationStatus.TIMEOUT,
                is_valid=False,
                elapsed_time_ms=elapsed,
                errors=[LeanError(0, 0, "Verification timeout", "timeout")],
                stderr="Timeout"
            )
            
        except Exception as e:
            elapsed = (time.time() - start_time) * 1000
            return VerificationResult(
                status=VerificationStatus.RUNTIME_ERROR,
                is_valid=False,
                elapsed_time_ms=elapsed,
                errors=[LeanError(0, 0, str(e), "runtime")],
                stderr=str(e)
            )
            
        finally:
            if temp_file and os.path.exists(temp_file):
                try:
                    os.unlink(temp_file)
                except Exception:
                    pass
    
    def verify_with_mathlib(self, code: str) -> VerificationResult:
        """
        使用Mathlib4验证代码
        
        自动添加必要的Mathlib导入
        """
        # 检查是否已有导入
        if not any(line.strip().startswith("import") for line in code.split('\n')):
            # 添加默认导入
            imports = "import Mathlib\n"
            code = imports + code
        
        return self.verify(code)
    
    def batch_verify(self, codes: List[str]) -> List[VerificationResult]:
        """批量验证"""
        results = []
        for i, code in enumerate(codes):
            logger.info(f"Verifying {i+1}/{len(codes)}...")
            result = self.verify(code)
            results.append(result)
        return results
    
    def generate_report(self, result: VerificationResult, 
                       output_format: str = "markdown") -> str:
        """
        生成验证报告
        
        Args:
            result: 验证结果
            output_format: 输出格式 (markdown, json, html)
            
        Returns:
            报告字符串
        """
        if output_format == "json":
            return json.dumps({
                "status": result.status.value,
                "is_valid": result.is_valid,
                "elapsed_time_ms": result.elapsed_time_ms,
                "errors": [
                    {
                        "line": e.line,
                        "column": e.column,
                        "message": e.message,
                        "severity": e.severity
                    }
                    for e in result.errors
                ],
                "warnings": [
                    {
                        "line": e.line,
                        "column": e.column,
                        "message": e.message
                    }
                    for e in result.warnings
                ]
            }, indent=2, ensure_ascii=False)
        
        elif output_format == "html":
            html = f"""<!DOCTYPE html>
<html>
<head>
    <title>Lean Verification Report</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .success {{ color: green; }}
        .error {{ color: red; }}
        .warning {{ color: orange; }}
        table {{ border-collapse: collapse; width: 100%; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #4CAF50; color: white; }}
    </style>
</head>
<body>
    <h1>Lean 4 Verification Report</h1>
    <p><strong>Status:</strong> <span class="{'success' if result.is_valid else 'error'}">{result.status.value}</span></p>
    <p><strong>Elapsed Time:</strong> {result.elapsed_time_ms:.2f} ms</p>
    
    <h2>Errors ({len(result.errors)})</h2>
    {"<p>No errors found.</p>" if not result.errors else """
    <table>
        <tr><th>Line</th><th>Column</th><th>Message</th></tr>
        """ + "".join(f"<tr><td>{e.line}</td><td>{e.column}</td><td>{e.message}</td></tr>" for e in result.errors) + """
    </table>
    """}
    
    <h2>Warnings ({len(result.warnings)})</h2>
    {"<p>No warnings.</p>" if not result.warnings else """
    <table>
        <tr><th>Line</th><th>Column</th><th>Message</th></tr>
        """ + "".join(f"<tr><td>{e.line}</td><td>{e.column}</td><td>{e.message}</td></tr>" for e in result.warnings) + """
    </table>
    """}
</body>
</html>"""
            return html
        
        else:  # markdown
            md = f"""# Lean 4 Verification Report

## Summary

- **Status**: {'✅ PASSED' if result.is_valid else '❌ FAILED'}
- **Elapsed Time**: {result.elapsed_time_ms:.2f} ms
- **Total Errors**: {len(result.errors)}
- **Total Warnings**: {len(result.warnings)}

## Errors

"""
            if result.errors:
                md += "| Line | Column | Message |\n"
                md += "|------|--------|----------|\n"
                for e in result.errors:
                    md += f"| {e.line} | {e.column} | {e.message} |\n"
            else:
                md += "No errors found.\n"
            
            md += "\n## Warnings\n\n"
            if result.warnings:
                md += "| Line | Column | Message |\n"
                md += "|------|--------|----------|\n"
                for w in result.warnings:
                    md += f"| {w.line} | {w.column} | {w.message} |\n"
            else:
                md += "No warnings.\n"
            
            return md
    
    def fix_common_errors(self, code: str, errors: List[LeanError]) -> str:
        """
        尝试自动修复常见错误
        
        Args:
            code: 原始代码
            errors: 错误列表
            
        Returns:
            修复后的代码
        """
        lines = code.split('\n')
        
        for error in errors:
            # 修复常见导入错误
            if "unknown namespace" in error.message.lower() or \
               "unknown identifier" in error.message.lower():
                # 尝试添加缺失的导入
                missing = re.search(r"'([^']+)'", error.message)
                if missing:
                    module = missing.group(1)
                    # 尝试推断正确的导入
                    if module.startswith("Nat"):
                        lines.insert(0, "import Mathlib.Data.Nat.Basic")
                    elif module.startswith("Int"):
                        lines.insert(0, "import Mathlib.Data.Int.Basic")
                    elif module.startswith("Real"):
                        lines.insert(0, "import Mathlib.Data.Real.Basic")
        
        return '\n'.join(lines)
    
    def interactive_verify(self) -> None:
        """交互式验证（用于测试）"""
        print("=" * 60)
        print("Lean 4 Verifier")
        print("=" * 60)
        print("\nEnter Lean 4 code (end with 'EOF' on a new line):")
        
        lines = []
        while True:
            line = input()
            if line.strip() == 'EOF':
                break
            lines.append(line)
        
        code = '\n'.join(lines)
        
        print("\nVerifying...")
        result = self.verify(code)
        
        print("\n" + self.generate_report(result, "markdown"))


# 便捷函数
def verify_lean_code(code: str) -> bool:
    """
    快速验证Lean代码
    
    Args:
        code: Lean 4代码
        
    Returns:
        是否验证通过
    """
    verifier = LeanVerifier()
    result = verifier.verify(code)
    return result.is_valid


def check_syntax(code: str) -> Tuple[bool, List[str]]:
    """
    检查Lean代码语法
    
    Args:
        code: Lean 4代码
        
    Returns:
        (是否通过, 错误信息列表)
    """
    verifier = LeanVerifier()
    result = verifier.verify(code)
    
    if result.is_valid:
        return True, []
    else:
        return False, [f"Line {e.line}:{e.column}: {e.message}" for e in result.errors]


if __name__ == "__main__":
    verifier = LeanVerifier()
    verifier.interactive_verify()
