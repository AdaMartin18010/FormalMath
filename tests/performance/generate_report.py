"""
性能测试报告生成器
Performance Test Report Generator

生成详细的性能测试报告，包括图表和优化建议
"""

import os
import json
import sys
from datetime import datetime
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from pathlib import Path

import matplotlib
matplotlib.use('Agg')  # 非交互式后端
import matplotlib.pyplot as plt
import numpy as np
from jinja2 import Template


# 报告模板
HTML_TEMPLATE = '''
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath 性能测试报告</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f7fa;
            padding: 20px;
        }
        .container {
            max-width: 1400px;
            margin: 0 auto;
            background: white;
            border-radius: 12px;
            box-shadow: 0 2px 12px rgba(0,0,0,0.1);
            overflow: hidden;
        }
        .header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 40px;
            text-align: center;
        }
        .header h1 {
            font-size: 2.5em;
            margin-bottom: 10px;
        }
        .header .meta {
            opacity: 0.9;
            font-size: 1.1em;
        }
        .summary-cards {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            padding: 30px;
            background: #f8f9fa;
        }
        .card {
            background: white;
            padding: 25px;
            border-radius: 10px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.08);
            border-left: 4px solid #667eea;
        }
        .card h3 {
            color: #666;
            font-size: 0.9em;
            text-transform: uppercase;
            letter-spacing: 1px;
            margin-bottom: 10px;
        }
        .card .value {
            font-size: 2.2em;
            font-weight: bold;
            color: #333;
        }
        .card .unit {
            font-size: 0.9em;
            color: #888;
            margin-left: 5px;
        }
        .status-pass { border-left-color: #28a745; }
        .status-warn { border-left-color: #ffc107; }
        .status-fail { border-left-color: #dc3545; }
        .content {
            padding: 30px;
        }
        .section {
            margin-bottom: 40px;
        }
        .section h2 {
            color: #333;
            border-bottom: 2px solid #667eea;
            padding-bottom: 10px;
            margin-bottom: 20px;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin: 20px 0;
            background: white;
            box-shadow: 0 1px 3px rgba(0,0,0,0.1);
        }
        th, td {
            padding: 12px 15px;
            text-align: left;
            border-bottom: 1px solid #e0e0e0;
        }
        th {
            background: #667eea;
            color: white;
            font-weight: 600;
        }
        tr:hover {
            background: #f5f5f5;
        }
        .badge {
            display: inline-block;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 0.85em;
            font-weight: 600;
        }
        .badge-success { background: #d4edda; color: #155724; }
        .badge-warning { background: #fff3cd; color: #856404; }
        .badge-danger { background: #f8d7da; color: #721c24; }
        .chart-container {
            margin: 30px 0;
            padding: 20px;
            background: #f8f9fa;
            border-radius: 10px;
            text-align: center;
        }
        .chart-container img {
            max-width: 100%;
            height: auto;
            border-radius: 8px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
        }
        .recommendations {
            background: #f8f9fa;
            padding: 25px;
            border-radius: 10px;
        }
        .recommendation-item {
            padding: 15px;
            margin: 10px 0;
            background: white;
            border-radius: 8px;
            border-left: 4px solid #667eea;
        }
        .recommendation-item h4 {
            color: #667eea;
            margin-bottom: 8px;
        }
        .recommendation-item p {
            color: #666;
            font-size: 0.95em;
        }
        .footer {
            text-align: center;
            padding: 30px;
            color: #888;
            border-top: 1px solid #e0e0e0;
            font-size: 0.9em;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>📊 FormalMath 性能测试报告</h1>
            <div class="meta">
                生成时间: {{ timestamp }} | 环境: {{ environment }}
            </div>
        </div>

        <div class="summary-cards">
            <div class="card status-{{ overall_status }}">
                <h3>总体状态</h3>
                <div class="value">{{ overall_status_text }}</div>
            </div>
            <div class="card">
                <h3>平均响应时间</h3>
                <div class="value">{{ avg_response_time }}<span class="unit">ms</span></div>
            </div>
            <div class="card">
                <h3>吞吐量</h3>
                <div class="value">{{ throughput }}<span class="unit">req/s</span></div>
            </div>
            <div class="card">
                <h3>错误率</h3>
                <div class="value">{{ error_rate }}<span class="unit">%</span></div>
            </div>
        </div>

        <div class="content">
            <!-- 负载测试结果 -->
            {% if load_test_results %}
            <div class="section">
                <h2>🚀 负载测试结果</h2>
                <table>
                    <thead>
                        <tr>
                            <th>指标</th>
                            <th>值</th>
                            <th>状态</th>
                        </tr>
                    </thead>
                    <tbody>
                        <tr>
                            <td>并发用户数</td>
                            <td>{{ load_test_results.users }}</td>
                            <td><span class="badge badge-success">正常</span></td>
                        </tr>
                        <tr>
                            <td>总请求数</td>
                            <td>{{ load_test_results.total_requests }}</td>
                            <td>-</td>
                        </tr>
                        <tr>
                            <td>平均响应时间</td>
                            <td>{{ load_test_results.avg_response_time }} ms</td>
                            <td>{{ load_test_results.response_status }}</td>
                        </tr>
                        <tr>
                            <td>95%响应时间</td>
                            <td>{{ load_test_results.p95_response_time }} ms</td>
                            <td>{{ load_test_results.p95_status }}</td>
                        </tr>
                        <tr>
                            <td>吞吐量</td>
                            <td>{{ load_test_results.rps }} req/s</td>
                            <td>-</td>
                        </tr>
                        <tr>
                            <td>错误率</td>
                            <td>{{ load_test_results.error_rate }}%</td>
                            <td>{{ load_test_results.error_status }}</td>
                        </tr>
                    </tbody>
                </table>

                {% if load_test_chart %}
                <div class="chart-container">
                    <h3>响应时间分布</h3>
                    <img src="{{ load_test_chart }}" alt="响应时间分布图">
                </div>
                {% endif %}
            </div>
            {% endif %}

            <!-- API性能测试 -->
            {% if api_results %}
            <div class="section">
                <h2>🔌 API性能测试</h2>
                <table>
                    <thead>
                        <tr>
                            <th>端点</th>
                            <th>平均(ms)</th>
                            <th>P95(ms)</th>
                            <th>吞吐量</th>
                            <th>错误数</th>
                            <th>状态</th>
                        </tr>
                    </thead>
                    <tbody>
                        {% for api in api_results %}
                        <tr>
                            <td>{{ api.name }}</td>
                            <td>{{ api.avg_time }}</td>
                            <td>{{ api.p95_time }}</td>
                            <td>{{ api.rps }} req/s</td>
                            <td>{{ api.errors }}</td>
                            <td>{{ api.status_badge }}</td>
                        </tr>
                        {% endfor %}
                    </tbody>
                </table>

                {% if api_chart %}
                <div class="chart-container">
                    <h3>API响应时间对比</h3>
                    <img src="{{ api_chart }}" alt="API性能对比图">
                </div>
                {% endif %}
            </div>
            {% endif %}

            <!-- 前端性能测试 -->
            {% if frontend_results %}
            <div class="section">
                <h2>🎨 前端性能测试</h2>
                <table>
                    <thead>
                        <tr>
                            <th>页面</th>
                            <th>FCP(ms)</th>
                            <th>LCP(ms)</th>
                            <th>TTI(ms)</th>
                            <th>CLS</th>
                            <th>状态</th>
                        </tr>
                    </thead>
                    <tbody>
                        {% for page in frontend_results %}
                        <tr>
                            <td>{{ page.name }}</td>
                            <td>{{ page.fcp }}</td>
                            <td>{{ page.lcp }}</td>
                            <td>{{ page.tti }}</td>
                            <td>{{ page.cls }}</td>
                            <td>{{ page.status_badge }}</td>
                        </tr>
                        {% endfor %}
                    </tbody>
                </table>
            </div>
            {% endif %}

            <!-- 优化建议 -->
            {% if recommendations %}
            <div class="section">
                <h2>💡 优化建议</h2>
                <div class="recommendations">
                    {% for rec in recommendations %}
                    <div class="recommendation-item">
                        <h4>{{ rec.title }}</h4>
                        <p>{{ rec.description }}</p>
                        <small>优先级: {{ rec.priority }} | 预期收益: {{ rec.impact }}</small>
                    </div>
                    {% endfor %}
                </div>
            </div>
            {% endif %}
        </div>

        <div class="footer">
            <p>FormalMath Performance Test Report | Generated by automated testing system</p>
        </div>
    </div>
</body>
</html>
'''


@dataclass
class TestResult:
    """测试结果数据类"""
    name: str
    status: str  # pass, warn, fail
    metrics: Dict[str, Any]
    details: Optional[str] = None


class ReportGenerator:
    """报告生成器"""

    def __init__(self, output_dir: str = "reports"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.charts_dir = self.output_dir / "charts"
        self.charts_dir.mkdir(exist_ok=True)

    def generate_report(
        self,
        load_test_data: Optional[Dict] = None,
        api_test_data: Optional[List[Dict]] = None,
        frontend_test_data: Optional[List[Dict]] = None,
        stress_test_data: Optional[Dict] = None,
        environment: str = "development"
    ) -> str:
        """生成完整报告"""

        # 生成图表
        load_test_chart = None
        api_chart = None

        if load_test_data:
            load_test_chart = self._generate_response_time_chart(load_test_data)

        if api_test_data:
            api_chart = self._generate_api_comparison_chart(api_test_data)

        # 生成优化建议
        recommendations = self._generate_recommendations(
            load_test_data, api_test_data, frontend_test_data
        )

        # 计算总体状态
        overall_status = self._calculate_overall_status(
            load_test_data, api_test_data, frontend_test_data
        )

        # 准备模板数据
        template_data = {
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "environment": environment,
            "overall_status": overall_status,
            "overall_status_text": self._get_status_text(overall_status),
            "avg_response_time": self._calculate_avg_response_time(api_test_data),
            "throughput": self._calculate_throughput(load_test_data),
            "error_rate": self._calculate_error_rate(load_test_data),
            "load_test_results": self._format_load_test_results(load_test_data),
            "load_test_chart": load_test_chart,
            "api_results": self._format_api_results(api_test_data),
            "api_chart": api_chart,
            "frontend_results": self._format_frontend_results(frontend_test_data),
            "recommendations": recommendations
        }

        # 渲染HTML
        template = Template(HTML_TEMPLATE)
        html_content = template.render(**template_data)

        # 保存报告
        report_path = self.output_dir / f"performance_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(html_content)

        print(f"\n✅ 性能报告已生成: {report_path}")
        return str(report_path)

    def _generate_response_time_chart(self, data: Dict) -> Optional[str]:
        """生成响应时间分布图"""
        try:
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

            # 响应时间分布直方图
            if 'response_times' in data:
                times = data['response_times']
                ax1.hist(times, bins=50, color='#667eea', alpha=0.7, edgecolor='white')
                ax1.axvline(data.get('avg_response_time', 0), color='red', linestyle='--',
                           label=f'平均: {data.get("avg_response_time", 0):.0f}ms')
                ax1.axvline(data.get('p95_response_time', 0), color='orange', linestyle='--',
                           label=f'P95: {data.get("p95_response_time", 0):.0f}ms')
                ax1.set_xlabel('响应时间 (ms)')
                ax1.set_ylabel('请求数')
                ax1.set_title('响应时间分布')
                ax1.legend()
                ax1.grid(True, alpha=0.3)

            # 吞吐量随时间变化
            if 'rps_over_time' in data:
                times = range(len(data['rps_over_time']))
                ax2.plot(times, data['rps_over_time'], color='#28a745', linewidth=2)
                ax2.set_xlabel('时间 (秒)')
                ax2.set_ylabel('吞吐量 (req/s)')
                ax2.set_title('吞吐量变化')
                ax2.grid(True, alpha=0.3)

            plt.tight_layout()
            chart_path = self.charts_dir / f"response_time_{datetime.now().strftime('%H%M%S')}.png"
            plt.savefig(chart_path, dpi=150, bbox_inches='tight')
            plt.close()

            return str(chart_path.relative_to(self.output_dir))
        except Exception as e:
            print(f"生成响应时间图表失败: {e}")
            return None

    def _generate_api_comparison_chart(self, data: List[Dict]) -> Optional[str]:
        """生成API性能对比图"""
        try:
            fig, ax = plt.subplots(figsize=(12, 6))

            names = [d.get('name', 'Unknown') for d in data]
            avg_times = [d.get('avg_time', 0) for d in data]
            p95_times = [d.get('p95_time', 0) for d in data]

            x = np.arange(len(names))
            width = 0.35

            bars1 = ax.bar(x - width/2, avg_times, width, label='平均响应时间',
                          color='#667eea', alpha=0.8)
            bars2 = ax.bar(x + width/2, p95_times, width, label='P95响应时间',
                          color='#764ba2', alpha=0.8)

            # 添加目标线
            ax.axhline(y=200, color='green', linestyle='--', alpha=0.5, label='目标: 200ms')
            ax.axhline(y=500, color='orange', linestyle='--', alpha=0.5, label='警告: 500ms')

            ax.set_xlabel('API端点')
            ax.set_ylabel('响应时间 (ms)')
            ax.set_title('API性能对比')
            ax.set_xticks(x)
            ax.set_xticklabels(names, rotation=45, ha='right')
            ax.legend()
            ax.grid(True, alpha=0.3, axis='y')

            plt.tight_layout()
            chart_path = self.charts_dir / f"api_comparison_{datetime.now().strftime('%H%M%S')}.png"
            plt.savefig(chart_path, dpi=150, bbox_inches='tight')
            plt.close()

            return str(chart_path.relative_to(self.output_dir))
        except Exception as e:
            print(f"生成API对比图表失败: {e}")
            return None

    def _generate_recommendations(
        self,
        load_test_data: Optional[Dict],
        api_test_data: Optional[List[Dict]],
        frontend_test_data: Optional[List[Dict]]
    ) -> List[Dict]:
        """生成优化建议"""
        recommendations = []

        # 基于负载测试的建议
        if load_test_data:
            error_rate = load_test_data.get('error_rate', 0)
            avg_time = load_test_data.get('avg_response_time', 0)

            if error_rate > 5:
                recommendations.append({
                    "title": "降低错误率",
                    "description": f"当前错误率为 {error_rate:.2f}%，建议检查服务器日志，识别并修复导致请求失败的错误。",
                    "priority": "高",
                    "impact": "显著提升用户体验"
                })

            if avg_time > 500:
                recommendations.append({
                    "title": "优化响应时间",
                    "description": f"平均响应时间为 {avg_time:.2f}ms，超过500ms阈值。建议启用缓存、优化数据库查询或增加服务器资源。",
                    "priority": "高",
                    "impact": "提升用户满意度"
                })

        # 基于API测试的建议
        if api_test_data:
            slow_apis = [api for api in api_test_data if api.get('avg_time', 0) > 500]
            if slow_apis:
                api_names = ', '.join([api.get('name', 'Unknown') for api in slow_apis[:3]])
                recommendations.append({
                    "title": "优化慢速API",
                    "description": f"以下API响应较慢: {api_names}。建议实施分页、添加缓存或优化查询逻辑。",
                    "priority": "中",
                    "impact": "提升整体性能"
                })

        # 基于前端测试的建议
        if frontend_test_data:
            high_cls = [p for p in frontend_test_data if p.get('cls', 0) > 0.1]
            if high_cls:
                recommendations.append({
                    "title": "减少布局偏移",
                    "description": "检测到较高的累积布局偏移(CLS)。建议为图片和iframe设置固定尺寸，避免内容加载时的布局抖动。",
                    "priority": "中",
                    "impact": "改善Core Web Vitals"
                })

        # 通用建议
        recommendations.append({
            "title": "启用Gzip压缩",
            "description": "确保所有文本资源(HTML, CSS, JS, JSON)都启用了Gzip或Brotli压缩，可减少传输大小70%以上。",
            "priority": "中",
            "impact": "减少带宽消耗"
        })

        recommendations.append({
            "title": "实施CDN加速",
            "description": "将静态资源部署到CDN，可显著降低用户访问延迟，特别是对于分布在全球的用户。",
            "priority": "低",
            "impact": "提升全球访问速度"
        })

        return recommendations

    def _calculate_overall_status(
        self,
        load_test_data: Optional[Dict],
        api_test_data: Optional[List[Dict]],
        frontend_test_data: Optional[List[Dict]]
    ) -> str:
        """计算总体状态"""
        issues = 0

        if load_test_data:
            if load_test_data.get('error_rate', 0) > 5:
                issues += 2
            if load_test_data.get('avg_response_time', 0) > 1000:
                issues += 1

        if api_test_data:
            slow_apis = sum(1 for api in api_test_data if api.get('avg_time', 0) > 500)
            issues += slow_apis

        if issues == 0:
            return "pass"
        elif issues <= 2:
            return "warn"
        else:
            return "fail"

    def _get_status_text(self, status: str) -> str:
        """获取状态文本"""
        status_map = {
            "pass": "通过 ✓",
            "warn": "警告 ⚠",
            "fail": "失败 ✗"
        }
        return status_map.get(status, "未知")

    def _format_load_test_results(self, data: Optional[Dict]) -> Optional[Dict]:
        """格式化负载测试结果"""
        if not data:
            return None

        avg_time = data.get('avg_response_time', 0)
        p95_time = data.get('p95_response_time', 0)
        error_rate = data.get('error_rate', 0)

        return {
            "users": data.get('users', 0),
            "total_requests": f"{data.get('total_requests', 0):,}",
            "avg_response_time": f"{avg_time:.2f}",
            "response_status": self._get_badge(avg_time < 500, avg_time < 1000),
            "p95_response_time": f"{p95_time:.2f}",
            "p95_status": self._get_badge(p95_time < 1000, p95_time < 2000),
            "rps": f"{data.get('rps', 0):.2f}",
            "error_rate": f"{error_rate:.2f}",
            "error_status": self._get_badge(error_rate < 1, error_rate < 5)
        }

    def _format_api_results(self, data: Optional[List[Dict]]) -> Optional[List[Dict]]:
        """格式化API结果"""
        if not data:
            return None

        formatted = []
        for api in data:
            avg_time = api.get('avg_time', 0)
            formatted.append({
                "name": api.get('name', 'Unknown'),
                "avg_time": f"{avg_time:.2f}",
                "p95_time": f"{api.get('p95_time', 0):.2f}",
                "rps": f"{api.get('rps', 0):.2f}",
                "errors": api.get('errors', 0),
                "status_badge": self._get_badge(avg_time < 300, avg_time < 500)
            })
        return formatted

    def _format_frontend_results(self, data: Optional[List[Dict]]) -> Optional[List[Dict]]:
        """格式化前端结果"""
        if not data:
            return None

        formatted = []
        for page in data:
            lcp = page.get('lcp', 0)
            formatted.append({
                "name": page.get('name', 'Unknown'),
                "fcp": f"{page.get('fcp', 0):.0f}",
                "lcp": f"{lcp:.0f}",
                "tti": f"{page.get('tti', 0):.0f}",
                "cls": f"{page.get('cls', 0):.3f}",
                "status_badge": self._get_badge(lcp < 2500, lcp < 4000)
            })
        return formatted

    def _get_badge(self, pass_condition: bool, warn_condition: bool) -> str:
        """获取徽章HTML"""
        if pass_condition:
            return '<span class="badge badge-success">通过</span>'
        elif warn_condition:
            return '<span class="badge badge-warning">警告</span>'
        else:
            return '<span class="badge badge-danger">失败</span>'

    def _calculate_avg_response_time(self, api_test_data: Optional[List[Dict]]) -> str:
        """计算平均响应时间"""
        if not api_test_data:
            return "N/A"
        times = [api.get('avg_time', 0) for api in api_test_data]
        return f"{sum(times) / len(times):.2f}" if times else "N/A"

    def _calculate_throughput(self, load_test_data: Optional[Dict]) -> str:
        """计算吞吐量"""
        if not load_test_data:
            return "N/A"
        return f"{load_test_data.get('rps', 0):.2f}"

    def _calculate_error_rate(self, load_test_data: Optional[Dict]) -> str:
        """计算错误率"""
        if not load_test_data:
            return "N/A"
        return f"{load_test_data.get('error_rate', 0):.2f}"


def generate_sample_report():
    """生成示例报告（用于测试）"""
    generator = ReportGenerator()

    # 示例数据
    load_test_data = {
        "users": 100,
        "total_requests": 15000,
        "avg_response_time": 245.5,
        "p95_response_time": 520.3,
        "rps": 48.5,
        "error_rate": 0.5,
        "response_times": np.random.lognormal(5.5, 0.5, 15000).tolist(),
        "rps_over_time": [30 + np.random.randint(-10, 10) for _ in range(300)]
    }

    api_test_data = [
        {"name": "健康检查", "avg_time": 25.3, "p95_time": 45.2, "rps": 120.5, "errors": 0},
        {"name": "概念列表", "avg_time": 180.5, "p95_time": 320.1, "rps": 45.2, "errors": 0},
        {"name": "概念详情", "avg_time": 120.3, "p95_time": 210.5, "rps": 65.8, "errors": 0},
        {"name": "搜索", "avg_time": 450.2, "p95_time": 850.3, "rps": 22.1, "errors": 2},
        {"name": "数学家列表", "avg_time": 155.8, "p95_time": 280.6, "rps": 52.3, "errors": 0},
    ]

    frontend_test_data = [
        {"name": "首页", "fcp": 850, "lcp": 1200, "tti": 1800, "cls": 0.02},
        {"name": "概念列表", "fcp": 950, "lcp": 1500, "tti": 2200, "cls": 0.05},
        {"name": "概念详情", "fcp": 750, "lcp": 1100, "tti": 1600, "cls": 0.01},
        {"name": "搜索结果", "fcp": 1200, "lcp": 2200, "tti": 3200, "cls": 0.08},
    ]

    report_path = generator.generate_report(
        load_test_data=load_test_data,
        api_test_data=api_test_data,
        frontend_test_data=frontend_test_data,
        environment="staging"
    )

    return report_path


if __name__ == "__main__":
    print("生成示例性能测试报告...")
    report_path = generate_sample_report()
    print(f"报告已保存: {report_path}")
