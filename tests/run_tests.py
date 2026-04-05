#!/usr/bin/env python3
"""
FormalMath项目测试运行器

功能:
- 支持选择特定测试模块
- 生成HTML测试报告
- 支持CI/CD集成
- 支持覆盖率报告

作者: FormalMath项目
版本: 1.0.0
"""

import os
import sys
import json
import time
import argparse
import unittest
import subprocess
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional, Any
from dataclasses import dataclass, field, asdict
from html import escape

# 添加当前目录到路径
sys.path.insert(0, str(Path(__file__).parent))

try:
    from test_suite import (
        create_test_suite, 
        create_specific_suite,
        DocumentFormatTests,
        Lean4CodeTests,
        ContentConsistencyTests
    )
except ImportError as e:
    print(f"错误: 无法导入test_suite模块: {e}")
    sys.exit(1)


# ============================================================================
# 配置
# ============================================================================

PROJECT_ROOT = Path(__file__).parent.parent
OUTPUT_DIR = Path(__file__).parent / "output"
COVERAGE_DIR = OUTPUT_DIR / "coverage"
REPORT_DIR = OUTPUT_DIR / "reports"

# 确保输出目录存在
OUTPUT_DIR.mkdir(exist_ok=True)
COVERAGE_DIR.mkdir(exist_ok=True)
REPORT_DIR.mkdir(exist_ok=True)


# ============================================================================
# 数据结构
# ============================================================================

@dataclass
class TestCaseResult:
    """单个测试用例结果"""
    name: str
    test_class: str
    status: str  # 'passed', 'failed', 'error', 'skipped'
    message: str = ""
    duration: float = 0.0
    details: Dict = field(default_factory=dict)


@dataclass
class TestRunResult:
    """测试运行结果"""
    start_time: datetime
    end_time: Optional[datetime] = None
    total_tests: int = 0
    passed: int = 0
    failed: int = 0
    errors: int = 0
    skipped: int = 0
    duration: float = 0.0
    test_results: List[TestCaseResult] = field(default_factory=list)
    coverage: Optional[float] = None
    
    @property
    def success_rate(self) -> float:
        if self.total_tests == 0:
            return 0.0
        return (self.passed / self.total_tests) * 100


# ============================================================================
# HTML报告生成器
# ============================================================================

class HTMLReportGenerator:
    """HTML测试报告生成器"""
    
    def __init__(self, result: TestRunResult):
        self.result = result
        
    def generate(self) -> str:
        """生成完整HTML报告"""
        html = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath测试报告 - {self.result.start_time.strftime('%Y-%m-%d %H:%M:%S')}</title>
    <style>
        :root {{
            --color-success: #28a745;
            --color-failure: #dc3545;
            --color-error: #fd7e14;
            --color-skipped: #6c757d;
            --color-primary: #007bff;
            --bg-light: #f8f9fa;
            --border-color: #dee2e6;
        }}
        
        * {{
            box-sizing: border-box;
            margin: 0;
            padding: 0;
        }}
        
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background-color: var(--bg-light);
            padding: 20px;
        }}
        
        .container {{
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            padding: 30px;
        }}
        
        h1 {{
            color: var(--color-primary);
            border-bottom: 2px solid var(--color-primary);
            padding-bottom: 10px;
            margin-bottom: 20px;
        }}
        
        h2 {{
            color: #555;
            margin: 25px 0 15px 0;
            font-size: 1.5em;
        }}
        
        .summary {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
            gap: 15px;
            margin: 20px 0;
        }}
        
        .summary-card {{
            padding: 20px;
            border-radius: 8px;
            text-align: center;
            color: white;
            font-weight: bold;
        }}
        
        .summary-card.total {{ background: var(--color-primary); }}
        .summary-card.passed {{ background: var(--color-success); }}
        .summary-card.failed {{ background: var(--color-failure); }}
        .summary-card.errors {{ background: var(--color-error); }}
        .summary-card.skipped {{ background: var(--color-skipped); }}
        .summary-card.coverage {{ background: #17a2b8; }}
        
        .summary-card .number {{
            font-size: 2em;
            display: block;
            margin-bottom: 5px;
        }}
        
        .progress-bar {{
            width: 100%;
            height: 30px;
            background: var(--border-color);
            border-radius: 15px;
            overflow: hidden;
            margin: 20px 0;
        }}
        
        .progress-fill {{
            height: 100%;
            background: linear-gradient(90deg, var(--color-success) 0%, #20c997 100%);
            display: flex;
            align-items: center;
            justify-content: center;
            color: white;
            font-weight: bold;
            transition: width 0.5s ease;
        }}
        
        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 20px 0;
            font-size: 0.9em;
        }}
        
        th, td {{
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid var(--border-color);
        }}
        
        th {{
            background: var(--bg-light);
            font-weight: 600;
            color: #555;
        }}
        
        tr:hover {{
            background: rgba(0,123,255,0.05);
        }}
        
        .status {{
            padding: 4px 12px;
            border-radius: 12px;
            font-size: 0.85em;
            font-weight: 600;
            text-transform: uppercase;
        }}
        
        .status.passed {{
            background: rgba(40, 167, 69, 0.1);
            color: var(--color-success);
        }}
        
        .status.failed {{
            background: rgba(220, 53, 69, 0.1);
            color: var(--color-failure);
        }}
        
        .status.error {{
            background: rgba(253, 126, 20, 0.1);
            color: var(--color-error);
        }}
        
        .status.skipped {{
            background: rgba(108, 117, 125, 0.1);
            color: var(--color-skipped);
        }}
        
        .details {{
            background: var(--bg-light);
            padding: 10px;
            border-radius: 4px;
            margin-top: 10px;
            font-family: 'Courier New', monospace;
            font-size: 0.85em;
            white-space: pre-wrap;
            max-height: 200px;
            overflow-y: auto;
        }}
        
        .timestamp {{
            color: #666;
            font-size: 0.9em;
            margin-bottom: 20px;
        }}
        
        .footer {{
            margin-top: 30px;
            padding-top: 20px;
            border-top: 1px solid var(--border-color);
            text-align: center;
            color: #666;
            font-size: 0.9em;
        }}
        
        .filter-buttons {{
            margin: 20px 0;
        }}
        
        .filter-btn {{
            padding: 8px 16px;
            margin: 0 5px;
            border: 1px solid var(--border-color);
            background: white;
            border-radius: 4px;
            cursor: pointer;
            transition: all 0.3s;
        }}
        
        .filter-btn:hover {{
            background: var(--bg-light);
        }}
        
        .filter-btn.active {{
            background: var(--color-primary);
            color: white;
            border-color: var(--color-primary);
        }}
        
        @media (max-width: 768px) {{
            .container {{
                padding: 15px;
            }}
            
            table {{
                font-size: 0.8em;
            }}
            
            th, td {{
                padding: 8px;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>📊 FormalMath 测试报告</h1>
        
        <div class="timestamp">
            测试时间: {self.result.start_time.strftime('%Y-%m-%d %H:%M:%S')} | 
            持续时间: {self.result.duration:.2f}秒 | 
            测试套件: FormalMath自动化测试套件 v1.0.0
        </div>
        
        {self._generate_summary()}
        {self._generate_progress_bar()}
        {self._generate_results_table()}
        
        <div class="footer">
            <p>Generated by FormalMath Test Runner</p>
            <p>项目地址: https://github.com/formalmath/formalmath</p>
        </div>
    </div>
    
    <script>
        function filterResults(status) {{
            const rows = document.querySelectorAll('.result-row');
            const buttons = document.querySelectorAll('.filter-btn');
            
            buttons.forEach(btn => btn.classList.remove('active'));
            event.target.classList.add('active');
            
            rows.forEach(row => {{
                if (status === 'all' || row.dataset.status === status) {{
                    row.style.display = '';
                }} else {{
                    row.style.display = 'none';
                }}
            }});
        }}
    </script>
</body>
</html>"""
        return html
    
    def _generate_summary(self) -> str:
        """生成摘要部分"""
        coverage_display = f"{self.result.coverage:.1f}%" if self.result.coverage else "N/A"
        
        return f"""
        <div class="summary">
            <div class="summary-card total">
                <span class="number">{self.result.total_tests}</span>
                <span>总测试数</span>
            </div>
            <div class="summary-card passed">
                <span class="number">{self.result.passed}</span>
                <span>通过</span>
            </div>
            <div class="summary-card failed">
                <span class="number">{self.result.failed}</span>
                <span>失败</span>
            </div>
            <div class="summary-card errors">
                <span class="number">{self.result.errors}</span>
                <span>错误</span>
            </div>
            <div class="summary-card skipped">
                <span class="number">{self.result.skipped}</span>
                <span>跳过</span>
            </div>
            <div class="summary-card coverage">
                <span class="number">{coverage_display}</span>
                <span>覆盖率</span>
            </div>
        </div>
        """
    
    def _generate_progress_bar(self) -> str:
        """生成进度条"""
        success_rate = self.result.success_rate
        color = "var(--color-success)" if success_rate >= 80 else "var(--color-warning)" if success_rate >= 60 else "var(--color-failure)"
        
        return f"""
        <div class="progress-bar">
            <div class="progress-fill" style="width: {success_rate}%; background: {color};">
                {success_rate:.1f}%
            </div>
        </div>
        """
    
    def _generate_results_table(self) -> str:
        """生成结果表格"""
        rows = ""
        for tr in self.result.test_results:
            status_class = tr.status.lower()
            details_html = ""
            if tr.message or tr.details:
                details = escape(tr.message)
                if tr.details:
                    details += "\n" + escape(json.dumps(tr.details, indent=2, ensure_ascii=False))
                details_html = f'<div class="details">{details}</div>'
            
            rows += f"""
            <tr class="result-row" data-status="{tr.status}">
                <td>{escape(tr.test_class)}</td>
                <td>{escape(tr.name)}</td>
                <td><span class="status {status_class}">{tr.status.upper()}</span></td>
                <td>{tr.duration:.3f}s</td>
                <td>{details_html}</td>
            </tr>
            """
        
        return f"""
        <h2>📋 详细结果</h2>
        <div class="filter-buttons">
            <button class="filter-btn active" onclick="filterResults('all')">全部</button>
            <button class="filter-btn" onclick="filterResults('passed')">通过</button>
            <button class="filter-btn" onclick="filterResults('failed')">失败</button>
            <button class="filter-btn" onclick="filterResults('error')">错误</button>
            <button class="filter-btn" onclick="filterResults('skipped')">跳过</button>
        </div>
        <table>
            <thead>
                <tr>
                    <th>测试类</th>
                    <th>测试名称</th>
                    <th>状态</th>
                    <th>耗时</th>
                    <th>详情</th>
                </tr>
            </thead>
            <tbody>
                {rows}
            </tbody>
        </table>
        """


# ============================================================================
# 测试运行器
# ============================================================================

class TestRunner:
    """测试运行器主类"""
    
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.result = TestRunResult(start_time=datetime.now())
        
    def run(self) -> TestRunResult:
        """运行测试"""
        print("=" * 60)
        print("FormalMath 自动化测试套件")
        print("=" * 60)
        
        start_time = time.time()
        
        # 创建测试套件
        if self.args.module:
            print(f"\n运行测试模块: {self.args.module}")
            suite = create_specific_suite(self.args.module)
        else:
            print("\n运行全部测试模块")
            suite = create_test_suite()
        
        # 运行测试
        runner = unittest.TextTestRunner(verbosity=self.args.verbosity)
        test_result = runner.run(suite)
        
        # 收集结果
        self._collect_results(test_result)
        
        # 计算覆盖率（如果启用）
        if self.args.coverage:
            self.result.coverage = self._calculate_coverage()
        
        # 记录结束时间
        self.result.end_time = datetime.now()
        self.result.duration = time.time() - start_time
        
        # 生成报告
        if self.args.html:
            self._generate_html_report()
        
        if self.args.json:
            self._generate_json_report()
        
        # 输出摘要
        self._print_summary()
        
        return self.result
    
    def _collect_results(self, test_result: unittest.TestResult):
        """收集测试结果"""
        # 统计
        self.result.total_tests = test_result.testsRun
        self.result.passed = test_result.testsRun - len(test_result.failures) - len(test_result.errors) - len(test_result.skipped)
        self.result.failed = len(test_result.failures)
        self.result.errors = len(test_result.errors)
        self.result.skipped = len(test_result.skipped)
        
        # 详细结果
        for test, traceback in test_result.failures:
            self.result.test_results.append(TestCaseResult(
                name=str(test).split(' ')[0],
                test_class=test.__class__.__name__,
                status='failed',
                message=traceback
            ))
        
        for test, traceback in test_result.errors:
            self.result.test_results.append(TestCaseResult(
                name=str(test).split(' ')[0],
                test_class=test.__class__.__name__,
                status='error',
                message=traceback
            ))
        
        for test in test_result.skipped:
            self.result.test_results.append(TestCaseResult(
                name=str(test[0]).split(' ')[0],
                test_class=test[0].__class__.__name__,
                status='skipped',
                message=test[1] if len(test) > 1 else ""
            ))
        
        # 成功的测试需要从测试类中收集
        # 这里简化处理
    
    def _calculate_coverage(self) -> Optional[float]:
        """计算测试覆盖率"""
        try:
            # 尝试使用coverage工具
            result = subprocess.run(
                [sys.executable, "-m", "coverage", "run", "--source=.", "-m", "unittest", "discover"],
                capture_output=True,
                text=True,
                cwd=str(PROJECT_ROOT)
            )
            
            result = subprocess.run(
                [sys.executable, "-m", "coverage", "report", "-m"],
                capture_output=True,
                text=True,
                cwd=str(PROJECT_ROOT)
            )
            
            # 解析覆盖率输出
            for line in result.stdout.split('\n'):
                if 'TOTAL' in line:
                    parts = line.split()
                    if len(parts) >= 4:
                        coverage_str = parts[3].replace('%', '')
                        return float(coverage_str)
            
            return None
        except Exception as e:
            print(f"覆盖率计算失败: {e}")
            return None
    
    def _generate_html_report(self):
        """生成HTML报告"""
        generator = HTMLReportGenerator(self.result)
        html_content = generator.generate()
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = REPORT_DIR / f"test_report_{timestamp}.html"
        
        report_file.write_text(html_content, encoding='utf-8')
        print(f"\n📄 HTML报告已生成: {report_file}")
        
        # 同时生成最新报告
        latest_file = REPORT_DIR / "test_report_latest.html"
        latest_file.write_text(html_content, encoding='utf-8')
    
    def _generate_json_report(self):
        """生成JSON报告"""
        data = asdict(self.result)
        data['start_time'] = self.result.start_time.isoformat()
        data['end_time'] = self.result.end_time.isoformat() if self.result.end_time else None
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = REPORT_DIR / f"test_report_{timestamp}.json"
        
        report_file.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding='utf-8')
        print(f"📄 JSON报告已生成: {report_file}")
        
        # 同时生成最新报告
        latest_file = REPORT_DIR / "test_report_latest.json"
        latest_file.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding='utf-8')
    
    def _print_summary(self):
        """打印测试摘要"""
        print("\n" + "=" * 60)
        print("测试摘要")
        print("=" * 60)
        print(f"总测试数:   {self.result.total_tests}")
        print(f"通过:       {self.result.passed} ✓")
        print(f"失败:       {self.result.failed} ✗")
        print(f"错误:       {self.result.errors} ⚠")
        print(f"跳过:       {self.result.skipped} ⏭")
        print(f"成功率:     {self.result.success_rate:.1f}%")
        if self.result.coverage:
            print(f"覆盖率:     {self.result.coverage:.1f}%")
        print(f"持续时间:   {self.result.duration:.2f}秒")
        print("=" * 60)
        
        if self.result.success_rate >= 80:
            print("✅ 测试结果: 通过 (达到80%目标)")
        else:
            print("❌ 测试结果: 未通过 (未达到80%目标)")


# ============================================================================
# 命令行参数
# ============================================================================

def create_argument_parser() -> argparse.ArgumentParser:
    """创建命令行参数解析器"""
    parser = argparse.ArgumentParser(
        description="FormalMath项目自动化测试运行器",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 运行所有测试
  python run_tests.py
  
  # 运行特定模块测试
  python run_tests.py --module document
  python run_tests.py --module lean4
  python run_tests.py --module content
  
  # 生成HTML报告
  python run_tests.py --html
  
  # 生成JSON报告
  python run_tests.py --json
  
  # 启用覆盖率分析
  python run_tests.py --coverage
  
  # CI模式 (简洁输出，启用所有报告)
  python run_tests.py --ci
        """
    )
    
    parser.add_argument(
        '-m', '--module',
        choices=['document', 'lean4', 'content', 'all'],
        default='all',
        help='选择测试模块 (默认: all)'
    )
    
    parser.add_argument(
        '--html',
        action='store_true',
        help='生成HTML测试报告'
    )
    
    parser.add_argument(
        '--json',
        action='store_true',
        help='生成JSON测试报告'
    )
    
    parser.add_argument(
        '--coverage',
        action='store_true',
        help='计算测试覆盖率'
    )
    
    parser.add_argument(
        '-v', '--verbosity',
        type=int,
        choices=[0, 1, 2],
        default=1,
        help='测试输出详细程度 (默认: 1)'
    )
    
    parser.add_argument(
        '--ci',
        action='store_true',
        help='CI模式: 启用所有报告并简洁输出'
    )
    
    parser.add_argument(
        '--fail-fast',
        action='store_true',
        help='遇到第一个失败时停止'
    )
    
    return parser


def main():
    """主函数"""
    parser = create_argument_parser()
    args = parser.parse_args()
    
    # CI模式设置
    if args.ci:
        args.html = True
        args.json = True
        args.coverage = True
        args.verbosity = 1
    
    # 调整module参数
    if args.module == 'all':
        args.module = None
    
    # 运行测试
    runner = TestRunner(args)
    result = runner.run()
    
    # 返回退出码
    if result.success_rate >= 80 and result.failed == 0 and result.errors == 0:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == '__main__':
    main()
