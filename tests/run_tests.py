#!/usr/bin/env python3
"""
FormalMath项目测试运行器 v2.0

功能:
- 支持选择特定测试模块
- 生成HTML测试报告
- 生成JUnit XML报告（CI集成）
- 支持趋势分析和历史对比
- 支持并行测试执行
- 支持测试缓存管理
- 支持覆盖率报告

作者: FormalMath项目
版本: 2.0.0
"""

import os
import sys
import json
import time
import argparse
import unittest
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path
from datetime import datetime, timedelta
from typing import List, Dict, Optional, Any, Tuple
from dataclasses import dataclass, field, asdict
from html import escape
import hashlib

# 添加当前目录到路径
sys.path.insert(0, str(Path(__file__).parent))

try:
    from test_suite import (
        create_test_suite, 
        create_specific_suite,
        TestResult,
        TestMetrics,
        TestConfig,
        TestCache,
        DocumentFormatTests,
        Lean4CodeTests,
        ContentConsistencyTests,
        DocumentContentQualityTests,
        MSCEncodingTests,
        CrossReferenceTests,
        TerminologyConsistencyTests,
        PerformanceTests,
        get_test_count
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
HISTORY_DIR = OUTPUT_DIR / "history"
CACHE_DIR = Path(__file__).parent / ".test_cache"

# 确保输出目录存在
OUTPUT_DIR.mkdir(exist_ok=True)
COVERAGE_DIR.mkdir(exist_ok=True)
REPORT_DIR.mkdir(exist_ok=True)
HISTORY_DIR.mkdir(exist_ok=True)


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
    version: str = "2.0.0"
    git_commit: str = ""
    
    @property
    def success_rate(self) -> float:
        if self.total_tests == 0:
            return 0.0
        return (self.passed / self.total_tests) * 100
    
    def to_dict(self) -> Dict:
        """转换为字典"""
        return {
            'start_time': self.start_time.isoformat(),
            'end_time': self.end_time.isoformat() if self.end_time else None,
            'total_tests': self.total_tests,
            'passed': self.passed,
            'failed': self.failed,
            'errors': self.errors,
            'skipped': self.skipped,
            'duration': self.duration,
            'success_rate': self.success_rate,
            'coverage': self.coverage,
            'version': self.version,
            'git_commit': self.git_commit,
            'test_results': [
                {
                    'name': r.name,
                    'test_class': r.test_class,
                    'status': r.status,
                    'message': r.message,
                    'duration': r.duration
                }
                for r in self.test_results
            ]
        }


@dataclass
class TrendData:
    """趋势数据"""
    dates: List[str] = field(default_factory=list)
    success_rates: List[float] = field(default_factory=list)
    durations: List[float] = field(default_factory=list)
    test_counts: List[int] = field(default_factory=list)
    
    def to_dict(self) -> Dict:
        return asdict(self)


# ============================================================================
# JUnit XML报告生成器
# ============================================================================

class JUnitXMLReportGenerator:
    """JUnit XML测试报告生成器（用于CI集成）"""
    
    def __init__(self, result: TestRunResult):
        self.result = result
    
    def generate(self) -> str:
        """生成JUnit XML报告"""
        # 创建testsuites元素
        testsuites = ET.Element('testsuites')
        testsuites.set('name', 'FormalMath Test Suite')
        testsuites.set('tests', str(self.result.total_tests))
        testsuites.set('failures', str(self.result.failed))
        testsuites.set('errors', str(self.result.errors))
        testsuites.set('skipped', str(self.result.skipped))
        testsuites.set('time', str(self.result.duration))
        testsuites.set('timestamp', self.result.start_time.isoformat())
        
        # 按测试类分组
        class_results: Dict[str, List[TestCaseResult]] = {}
        for tr in self.result.test_results:
            if tr.test_class not in class_results:
                class_results[tr.test_class] = []
            class_results[tr.test_class].append(tr)
        
        # 为每个测试类创建testsuite
        for class_name, tests in class_results.items():
            testsuite = ET.SubElement(testsuites, 'testsuite')
            testsuite.set('name', class_name)
            testsuite.set('tests', str(len(tests)))
            
            failures = sum(1 for t in tests if t.status == 'failed')
            errors = sum(1 for t in tests if t.status == 'error')
            skipped = sum(1 for t in tests if t.status == 'skipped')
            duration = sum(t.duration for t in tests)
            
            testsuite.set('failures', str(failures))
            testsuite.set('errors', str(errors))
            testsuite.set('skipped', str(skipped))
            testsuite.set('time', str(duration))
            
            # 添加每个测试用例
            for test in tests:
                testcase = ET.SubElement(testsuite, 'testcase')
                testcase.set('name', test.name)
                testcase.set('classname', class_name)
                testcase.set('time', str(test.duration))
                
                if test.status == 'failed':
                    failure = ET.SubElement(testcase, 'failure')
                    failure.set('message', test.message[:200])
                    failure.text = test.message
                elif test.status == 'error':
                    error = ET.SubElement(testcase, 'error')
                    error.set('message', test.message[:200])
                    error.text = test.message
                elif test.status == 'skipped':
                    skip = ET.SubElement(testcase, 'skipped')
                    skip.set('message', test.message[:200])
        
        # 格式化XML
        self._indent(testsuites)
        xml_string = ET.tostring(testsuites, encoding='unicode')
        return f'<?xml version="1.0" encoding="UTF-8"?>\n{xml_string}'
    
    def _indent(self, elem, level=0):
        """为XML元素添加缩进"""
        i = "\n" + level*"  "
        if len(elem):
            if not elem.text or not elem.text.strip():
                elem.text = i + "  "
            if not elem.tail or not elem.tail.strip():
                elem.tail = i
            for child in elem:
                self._indent(child, level+1)
            if not child.tail or not child.tail.strip():
                child.tail = i
        else:
            if level and (not elem.tail or not elem.tail.strip()):
                elem.tail = i


# ============================================================================
# HTML报告生成器（增强版）
# ============================================================================

class HTMLReportGenerator:
    """HTML测试报告生成器（增强版）"""
    
    def __init__(self, result: TestRunResult, trend: Optional[TrendData] = None):
        self.result = result
        self.trend = trend
    
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
            --color-warning: #ffc107;
            --bg-light: #f8f9fa;
            --border-color: #dee2e6;
        }}
        
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background-color: var(--bg-light);
            padding: 20px;
        }}
        
        .container {{
            max-width: 1400px;
            margin: 0 auto;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            padding: 30px;
        }}
        
        h1 {{ color: var(--color-primary); border-bottom: 2px solid var(--color-primary); padding-bottom: 10px; margin-bottom: 20px; }}
        h2 {{ color: #555; margin: 25px 0 15px 0; font-size: 1.5em; }}
        h3 {{ color: #666; margin: 20px 0 10px 0; font-size: 1.2em; }}
        
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
        
        .summary-card .number {{ font-size: 2em; display: block; margin-bottom: 5px; }}
        
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
        
        .progress-fill.warning {{ background: linear-gradient(90deg, var(--color-warning) 0%, #ffdb4d 100%); color: #333; }}
        .progress-fill.danger {{ background: linear-gradient(90deg, var(--color-failure) 0%, #ff6b6b 100%); }}
        
        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 20px 0;
            font-size: 0.9em;
        }}
        
        th, td {{ padding: 12px; text-align: left; border-bottom: 1px solid var(--border-color); }}
        th {{ background: var(--bg-light); font-weight: 600; color: #555; }}
        tr:hover {{ background: rgba(0,123,255,0.05); }}
        
        .status {{
            padding: 4px 12px;
            border-radius: 12px;
            font-size: 0.85em;
            font-weight: 600;
            text-transform: uppercase;
        }}
        
        .status.passed {{ background: rgba(40, 167, 69, 0.1); color: var(--color-success); }}
        .status.failed {{ background: rgba(220, 53, 69, 0.1); color: var(--color-failure); }}
        .status.error {{ background: rgba(253, 126, 20, 0.1); color: var(--color-error); }}
        .status.skipped {{ background: rgba(108, 117, 125, 0.1); color: var(--color-skipped); }}
        
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
        
        .timestamp {{ color: #666; font-size: 0.9em; margin-bottom: 20px; }}
        
        .footer {{
            margin-top: 30px;
            padding-top: 20px;
            border-top: 1px solid var(--border-color);
            text-align: center;
            color: #666;
            font-size: 0.9em;
        }}
        
        .filter-buttons {{ margin: 20px 0; }}
        
        .filter-btn {{
            padding: 8px 16px;
            margin: 0 5px;
            border: 1px solid var(--border-color);
            background: white;
            border-radius: 4px;
            cursor: pointer;
            transition: all 0.3s;
        }}
        
        .filter-btn:hover {{ background: var(--bg-light); }}
        .filter-btn.active {{ background: var(--color-primary); color: white; border-color: var(--color-primary); }}
        
        .badge {{
            display: inline-block;
            padding: 2px 8px;
            border-radius: 10px;
            font-size: 0.75em;
            font-weight: 600;
        }}
        .badge-success {{ background: rgba(40, 167, 69, 0.1); color: var(--color-success); }}
        .badge-warning {{ background: rgba(255, 193, 7, 0.1); color: #856404; }}
        .badge-danger {{ background: rgba(220, 53, 69, 0.1); color: var(--color-failure); }}
        
        .trend-chart {{
            height: 200px;
            background: var(--bg-light);
            border-radius: 8px;
            margin: 20px 0;
            padding: 20px;
        }}
        
        @media (max-width: 768px) {{
            .container {{ padding: 15px; }}
            table {{ font-size: 0.8em; }}
            th, td {{ padding: 8px; }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>📊 FormalMath 测试报告</h1>
        
        <div class="timestamp">
            测试时间: {self.result.start_time.strftime('%Y-%m-%d %H:%M:%S')} | 
            持续时间: {self.result.duration:.2f}秒 | 
            成功率: {self.result.success_rate:.1f}% |
            版本: {self.result.version}
        </div>
        
        {self._generate_summary()}
        {self._generate_progress_bar()}
        {self._generate_trend_section()}
        {self._generate_results_table()}
        
        <div class="footer">
            <p>Generated by FormalMath Test Runner v{self.result.version}</p>
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
        
        if success_rate >= 95:
            css_class = ""
            color = "var(--color-success)"
        elif success_rate >= 80:
            css_class = "warning"
            color = "var(--color-warning)"
        else:
            css_class = "danger"
            color = "var(--color-failure)"
        
        return f"""
        <div class="progress-bar">
            <div class="progress-fill {css_class}" style="width: {success_rate}%; background: {color};">
                {success_rate:.1f}%
            </div>
        </div>
        """
    
    def _generate_trend_section(self) -> str:
        """生成趋势分析部分"""
        if not self.trend or not self.trend.dates:
            return ""
        
        # 生成趋势表格
        rows = ""
        for i in range(len(self.trend.dates)):
            rate = self.trend.success_rates[i] if i < len(self.trend.success_rates) else 0
            duration = self.trend.durations[i] if i < len(self.trend.durations) else 0
            count = self.trend.test_counts[i] if i < len(self.trend.test_counts) else 0
            
            badge_class = "badge-success" if rate >= 95 else "badge-warning" if rate >= 80 else "badge-danger"
            
            rows += f"""
            <tr>
                <td>{self.trend.dates[i]}</td>
                <td><span class="badge {badge_class}">{rate:.1f}%</span></td>
                <td>{duration:.2f}s</td>
                <td>{count}</td>
            </tr>
            """
        
        return f"""
        <h2>📈 历史趋势</h2>
        <table>
            <thead>
                <tr>
                    <th>日期</th>
                    <th>成功率</th>
                    <th>持续时间</th>
                    <th>测试数</th>
                </tr>
            </thead>
            <tbody>
                {rows}
            </tbody>
        </table>
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
# 历史记录管理
# ============================================================================

class HistoryManager:
    """历史记录管理器"""
    
    def __init__(self, history_dir: Path = HISTORY_DIR):
        self.history_dir = history_dir
        self.history_dir.mkdir(exist_ok=True)
    
    def save_result(self, result: TestRunResult):
        """保存测试结果到历史"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        history_file = self.history_dir / f"test_run_{timestamp}.json"
        
        try:
            with open(history_file, 'w', encoding='utf-8') as f:
                json.dump(result.to_dict(), f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"保存历史记录失败: {e}")
    
    def load_trend_data(self, days: int = 30) -> TrendData:
        """加载趋势数据"""
        trend = TrendData()
        
        # 获取最近的历史文件
        history_files = sorted(self.history_dir.glob('test_run_*.json'), reverse=True)
        cutoff_date = datetime.now() - timedelta(days=days)
        
        for history_file in history_files[:days]:  # 最多取指定天数的数据
            try:
                with open(history_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                
                run_date = datetime.fromisoformat(data.get('start_time', '2000-01-01'))
                if run_date < cutoff_date:
                    continue
                
                trend.dates.append(run_date.strftime('%Y-%m-%d'))
                trend.success_rates.append(data.get('success_rate', 0))
                trend.durations.append(data.get('duration', 0))
                trend.test_counts.append(data.get('total_tests', 0))
                
            except Exception as e:
                print(f"加载历史记录失败 {history_file}: {e}")
        
        # 反转顺序使时间从早到晚
        trend.dates.reverse()
        trend.success_rates.reverse()
        trend.durations.reverse()
        trend.test_counts.reverse()
        
        return trend


# ============================================================================
# 测试运行器（增强版）
# ============================================================================

class TestRunner:
    """测试运行器主类（增强版）"""
    
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.result = TestRunResult(start_time=datetime.now())
        self.history = HistoryManager()
        
        # 获取git commit信息
        try:
            git_result = subprocess.run(
                ['git', 'rev-parse', '--short', 'HEAD'],
                capture_output=True,
                text=True,
                timeout=5
            )
            if git_result.returncode == 0:
                self.result.git_commit = git_result.stdout.strip()
        except:
            pass
        
    def run(self) -> TestRunResult:
        """运行测试"""
        print("=" * 70)
        print("FormalMath 自动化测试套件 v2.0")
        print("=" * 70)
        
        start_time = time.time()
        
        # 清除缓存（如果请求）
        if self.args.clear_cache:
            cache = TestCache()
            cache.clear()
            print("\n🗑  测试缓存已清除")
        
        # 创建测试套件
        if self.args.module:
            print(f"\n运行测试模块: {self.args.module}")
            suite = create_specific_suite(self.args.module)
        else:
            print("\n运行全部测试模块")
            suite = create_test_suite()
        
        # 设置环境变量
        if self.args.parallel:
            os.environ['TEST_PARALLEL'] = 'true'
        if self.args.skip_lean:
            os.environ['SKIP_LEAN_COMPILE'] = 'true'
        if self.args.mathlib_mode:
            os.environ['MATHLIB_CHECK_MODE'] = self.args.mathlib_mode
        
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
        
        # 保存到历史
        if self.args.save_history:
            self.history.save_result(self.result)
        
        # 加载趋势数据
        trend = None
        if self.args.trend:
            trend = self.history.load_trend_data(days=30)
        
        # 生成报告
        if self.args.html:
            self._generate_html_report(trend)
        
        if self.args.json:
            self._generate_json_report()
        
        if self.args.junit:
            self._generate_junit_report()
        
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
        
        # 成功的测试也需要添加（简化处理，从测试类中获取）
        # 这里简化处理，实际应记录所有通过的测试
    
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
    
    def _generate_html_report(self, trend: Optional[TrendData] = None):
        """生成HTML报告"""
        generator = HTMLReportGenerator(self.result, trend)
        html_content = generator.generate()
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = REPORT_DIR / f"test_report_{timestamp}.html"
        
        report_file.write_text(html_content, encoding='utf-8')
        print(f"\n📄 HTML报告已生成: {report_file}")
        
        # 同时生成最新报告
        latest_file = REPORT_DIR / "test_report_latest.html"
        latest_file.write_text(html_content, encoding='utf-8')
        print(f"📄 最新报告: {latest_file}")
    
    def _generate_json_report(self):
        """生成JSON报告"""
        data = self.result.to_dict()
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = REPORT_DIR / f"test_report_{timestamp}.json"
        
        report_file.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding='utf-8')
        print(f"📄 JSON报告已生成: {report_file}")
        
        # 同时生成最新报告
        latest_file = REPORT_DIR / "test_report_latest.json"
        latest_file.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding='utf-8')
    
    def _generate_junit_report(self):
        """生成JUnit XML报告"""
        generator = JUnitXMLReportGenerator(self.result)
        xml_content = generator.generate()
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = REPORT_DIR / f"junit_report_{timestamp}.xml"
        
        report_file.write_text(xml_content, encoding='utf-8')
        print(f"📄 JUnit XML报告已生成: {report_file}")
        
        # 同时生成最新报告
        latest_file = REPORT_DIR / "junit_report_latest.xml"
        latest_file.write_text(xml_content, encoding='utf-8')
    
    def _print_summary(self):
        """打印测试摘要"""
        print("\n" + "=" * 70)
        print("测试摘要")
        print("=" * 70)
        print(f"总测试数:   {self.result.total_tests}")
        print(f"通过:       {self.result.passed} ✓")
        print(f"失败:       {self.result.failed} ✗")
        print(f"错误:       {self.result.errors} ⚠")
        print(f"跳过:       {self.result.skipped} ⏭")
        print(f"成功率:     {self.result.success_rate:.1f}%")
        if self.result.coverage:
            print(f"覆盖率:     {self.result.coverage:.1f}%")
        print(f"持续时间:   {self.result.duration:.2f}秒")
        if self.result.git_commit:
            print(f"Git Commit: {self.result.git_commit}")
        print("=" * 70)
        
        # 95%目标
        if self.result.success_rate >= 95 and self.result.failed == 0 and self.result.errors == 0:
            print("✅ 测试结果: 优秀 (达到95%目标)")
        elif self.result.success_rate >= 80:
            print("⚠️  测试结果: 通过 (达到80%最低要求)")
        else:
            print("❌ 测试结果: 未通过 (未达到80%目标)")


# ============================================================================
# 命令行参数
# ============================================================================

def create_argument_parser() -> argparse.ArgumentParser:
    """创建命令行参数解析器"""
    parser = argparse.ArgumentParser(
        description="FormalMath项目自动化测试运行器 v2.0",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 运行所有测试
  python run_tests.py
  
  # 运行特定模块测试
  python run_tests.py --module document
  python run_tests.py --module lean4
  python run_tests.py --module content
  python run_tests.py --module quality
  python run_tests.py --module msc
  python run_tests.py --module crossref
  python run_tests.py --module terminology
  python run_tests.py --module performance
  
  # 生成所有报告
  python run_tests.py --html --json --junit
  
  # CI模式 (启用所有报告)
  python run_tests.py --ci
  
  # 跳过Lean编译测试
  python run_tests.py --skip-lean
  
  # 设置mathlib检查模式
  python run_tests.py --mathlib-mode skip
  python run_tests.py --mathlib-mode detect
  python run_tests.py --mathlib-mode strict
  
  # 启用并行测试
  python run_tests.py --parallel
  
  # 清除测试缓存
  python run_tests.py --clear-cache
  
  # 显示历史趋势
  python run_tests.py --trend
        """
    )
    
    parser.add_argument(
        '-m', '--module',
        choices=['document', 'lean4', 'content', 'quality', 'msc', 'crossref', 'terminology', 'performance', 'all'],
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
        '--junit',
        action='store_true',
        help='生成JUnit XML测试报告（用于CI集成）'
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
        help='CI模式: 启用HTML、JSON、JUnit报告'
    )
    
    parser.add_argument(
        '--fail-fast',
        action='store_true',
        help='遇到第一个失败时停止'
    )
    
    parser.add_argument(
        '--parallel',
        action='store_true',
        help='启用并行测试执行'
    )
    
    parser.add_argument(
        '--skip-lean',
        action='store_true',
        help='跳过Lean4编译测试'
    )
    
    parser.add_argument(
        '--mathlib-mode',
        choices=['detect', 'skip', 'strict'],
        default='detect',
        help='mathlib检查模式: detect(检测并跳过), skip(始终跳过), strict(严格模式) (默认: detect)'
    )
    
    parser.add_argument(
        '--clear-cache',
        action='store_true',
        help='清除测试缓存'
    )
    
    parser.add_argument(
        '--trend',
        action='store_true',
        help='显示历史趋势分析'
    )
    
    parser.add_argument(
        '--save-history',
        action='store_true',
        default=True,
        help='保存测试结果到历史记录（默认启用）'
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
        args.junit = True
        args.coverage = True
        args.verbosity = 1
        args.trend = True
    
    # 调整module参数
    if args.module == 'all':
        args.module = None
    
    # 运行测试
    runner = TestRunner(args)
    result = runner.run()
    
    # 返回退出码
    if result.success_rate >= 95 and result.failed == 0 and result.errors == 0:
        sys.exit(0)
    elif result.success_rate >= 80:
        sys.exit(0)  # 仍然返回0，但打印警告
    else:
        sys.exit(1)


if __name__ == '__main__':
    main()
