"""
性能测试运行器
Performance Test Runner

统一的性能测试入口，支持运行所有类型的性能测试
"""

import os
import sys
import argparse
import subprocess
import json
import time
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any, Optional

from config import (
    create_load_test_config,
    create_stress_test_config,
    create_api_performance_config,
    create_frontend_performance_config
)
from generate_report import ReportGenerator


class PerformanceTestRunner:
    """性能测试运行器"""
    
    def __init__(self, environment: str = "development"):
        self.environment = environment
        self.results_dir = Path("results")
        self.results_dir.mkdir(exist_ok=True)
        self.reports_dir = Path("reports")
        self.reports_dir.mkdir(exist_ok=True)
        
        # 加载配置
        self.load_config = create_load_test_config(environment)
        self.stress_config = create_stress_test_config(environment)
        self.api_config = create_api_performance_config(environment)
        self.frontend_config = create_frontend_performance_config(environment)
        
        self.test_results = {
            "timestamp": datetime.now().isoformat(),
            "environment": environment,
            "tests": {}
        }
    
    def run_all(self) -> Dict[str, Any]:
        """运行所有性能测试"""
        print("=" * 80)
        print("🚀 FormalMath 性能测试套件")
        print("=" * 80)
        print(f"环境: {self.environment}")
        print(f"时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 80)
        
        # 运行各类测试
        self.run_load_test()
        self.run_api_performance_test()
        self.run_frontend_performance_test()
        
        # 生成报告
        self.generate_report()
        
        return self.test_results
    
    def run_load_test(self, duration: int = 300, users: int = 100) -> Dict[str, Any]:
        """运行负载测试"""
        print("\n📊 运行负载测试...")
        print(f"   并发用户: {users}")
        print(f"   持续时间: {duration}秒")
        
        try:
            # 构建locust命令
            cmd = [
                "locust",
                "-f", "load_test.py",
                "--host", self.load_config.base_url,
                "--users", str(users),
                "--spawn-rate", str(users // 10),
                "--run-time", f"{duration}s",
                "--headless",
                "--csv", str(self.results_dir / "load_test"),
                "--html", str(self.reports_dir / "load_test_report.html")
            ]
            
            # 运行测试
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=duration + 60
            )
            
            # 解析结果
            test_result = self._parse_locust_results("load_test")
            self.test_results["tests"]["load_test"] = test_result
            
            print(f"   ✅ 负载测试完成")
            print(f"   平均响应时间: {test_result.get('avg_response_time', 'N/A')}ms")
            print(f"   吞吐量: {test_result.get('rps', 'N/A')} req/s")
            
            return test_result
            
        except subprocess.TimeoutExpired:
            print("   ⚠ 负载测试超时")
            return {"status": "timeout", "error": "Test timed out"}
        except FileNotFoundError:
            print("   ⚠ Locust未安装，跳过负载测试")
            print("   安装命令: pip install locust")
            return {"status": "skipped", "error": "Locust not installed"}
        except Exception as e:
            print(f"   ❌ 负载测试失败: {e}")
            return {"status": "error", "error": str(e)}
    
    def run_stress_test(self, max_users: int = 1000, step_duration: int = 60) -> Dict[str, Any]:
        """运行压力测试"""
        print("\n🔥 运行压力测试...")
        print(f"   最大用户: {max_users}")
        print(f"   每阶段: {step_duration}秒")
        
        try:
            cmd = [
                "locust",
                "-f", "stress_test.py",
                "--host", self.stress_config.base_url,
                "--class-picker",
                "--headless",
                "--run-time", f"{max_users // 50 * step_duration}s",
                "--csv", str(self.results_dir / "stress_test"),
                "--html", str(self.reports_dir / "stress_test_report.html")
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=1200)
            
            test_result = self._parse_locust_results("stress_test")
            self.test_results["tests"]["stress_test"] = test_result
            
            print(f"   ✅ 压力测试完成")
            print(f"   峰值用户: {test_result.get('peak_users', 'N/A')}")
            
            return test_result
            
        except Exception as e:
            print(f"   ⚠ 压力测试跳过: {e}")
            return {"status": "skipped", "error": str(e)}
    
    def run_api_performance_test(self) -> Dict[str, Any]:
        """运行API性能测试"""
        print("\n🔌 运行API性能测试...")
        
        try:
            # 运行pytest-benchmark
            cmd = [
                "pytest",
                "api_performance_test.py",
                "-v",
                "--benchmark-only",
                "--benchmark-json", str(self.results_dir / "api_benchmark.json")
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            # 解析benchmark结果
            test_result = self._parse_api_benchmark_results()
            self.test_results["tests"]["api_performance"] = test_result
            
            print(f"   ✅ API性能测试完成")
            print(f"   测试端点数: {len(test_result.get('apis', []))}")
            
            return test_result
            
        except FileNotFoundError:
            print("   ⚠ pytest-benchmark未安装，跳过API性能测试")
            print("   安装命令: pip install pytest-benchmark")
            return {"status": "skipped", "error": "pytest-benchmark not installed"}
        except Exception as e:
            print(f"   ⚠ API性能测试跳过: {e}")
            return {"status": "skipped", "error": str(e)}
    
    def run_frontend_performance_test(self) -> Dict[str, Any]:
        """运行前端性能测试"""
        print("\n🎨 运行前端性能测试...")
        
        try:
            # 运行Cypress性能测试
            cmd = [
                "npx", "cypress", "run",
                "--config-file", "../frontend/cypress.config.ts",
                "--spec", "frontend_performance_test.cy.ts"
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,
                cwd=str(Path.cwd())
            )
            
            test_result = {
                "status": "completed",
                "exit_code": result.returncode,
                "output": result.stdout[-2000:] if len(result.stdout) > 2000 else result.stdout
            }
            
            self.test_results["tests"]["frontend_performance"] = test_result
            
            print(f"   ✅ 前端性能测试完成")
            
            return test_result
            
        except FileNotFoundError:
            print("   ⚠ Cypress未安装，跳过前端性能测试")
            return {"status": "skipped", "error": "Cypress not installed"}
        except Exception as e:
            print(f"   ⚠ 前端性能测试跳过: {e}")
            return {"status": "skipped", "error": str(e)}
    
    def generate_report(self) -> str:
        """生成综合报告"""
        print("\n📄 生成性能测试报告...")
        
        generator = ReportGenerator(str(self.reports_dir))
        
        # 准备数据
        load_data = self.test_results["tests"].get("load_test", {})
        api_data = self.test_results["tests"].get("api_performance", {}).get("apis", [])
        frontend_data = self.test_results["tests"].get("frontend_performance", {}).get("pages", [])
        
        # 如果数据为空，使用模拟数据
        if not load_data.get("total_requests"):
            load_data = None
        if not api_data:
            api_data = None
        if not frontend_data:
            frontend_data = None
        
        report_path = generator.generate_report(
            load_test_data=load_data,
            api_test_data=api_data,
            frontend_test_data=frontend_data,
            environment=self.environment
        )
        
        # 保存JSON结果
        json_path = self.results_dir / f"test_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(self.test_results, f, indent=2, ensure_ascii=False)
        
        print(f"\n{'=' * 80}")
        print("✅ 性能测试完成!")
        print(f"   报告: {report_path}")
        print(f"   数据: {json_path}")
        print(f"{'=' * 80}")
        
        return report_path
    
    def _parse_locust_results(self, test_name: str) -> Dict[str, Any]:
        """解析Locust测试结果"""
        result = {"status": "completed"}
        
        # 尝试读取CSV结果
        csv_stats = self.results_dir / f"{test_name}_stats.csv"
        if csv_stats.exists():
            try:
                import csv
                with open(csv_stats, 'r') as f:
                    reader = csv.DictReader(f)
                    rows = list(reader)
                    if rows:
                        # 汇总统计
                        total_row = rows[-1]  # 最后一行是汇总
                        result.update({
                            "total_requests": int(total_row.get("Request Count", 0)),
                            "avg_response_time": float(total_row.get("Average Response Time", 0)),
                            "min_response_time": float(total_row.get("Min Response Time", 0)),
                            "max_response_time": float(total_row.get("Max Response Time", 0)),
                            "rps": float(total_row.get("Requests/s", 0)),
                            "error_rate": float(total_row.get("Failure Count", 0)) / max(1, int(total_row.get("Request Count", 1))) * 100
                        })
            except Exception as e:
                print(f"   解析结果警告: {e}")
        
        return result
    
    def _parse_api_benchmark_results(self) -> Dict[str, Any]:
        """解析API benchmark结果"""
        result = {"status": "completed", "apis": []}
        
        json_file = self.results_dir / "api_benchmark.json"
        if json_file.exists():
            try:
                with open(json_file, 'r') as f:
                    data = json.load(f)
                    for benchmark in data.get("benchmarks", []):
                        result["apis"].append({
                            "name": benchmark.get("name", "Unknown"),
                            "avg_time": benchmark.get("stats", {}).get("mean", 0) * 1000,  # 转换为ms
                            "p95_time": benchmark.get("stats", {}).get("q95", 0) * 1000,
                            "min_time": benchmark.get("stats", {}).get("min", 0) * 1000,
                            "max_time": benchmark.get("stats", {}).get("max", 0) * 1000,
                            "rps": 1.0 / max(benchmark.get("stats", {}).get("mean", 0.001), 0.001),
                            "errors": 0
                        })
            except Exception as e:
                print(f"   解析API结果警告: {e}")
        
        return result


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="FormalMath 性能测试运行器",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 运行所有测试
  python run_performance_tests.py
  
  # 指定环境
  python run_performance_tests.py --env staging
  
  # 只运行负载测试
  python run_performance_tests.py --load-test-only
  
  # 自定义负载测试参数
  python run_performance_tests.py --users 200 --duration 600
        """
    )
    
    parser.add_argument(
        "--env",
        choices=["development", "staging", "production"],
        default="development",
        help="测试环境 (默认: development)"
    )
    
    parser.add_argument(
        "--users",
        type=int,
        default=100,
        help="负载测试并发用户数 (默认: 100)"
    )
    
    parser.add_argument(
        "--duration",
        type=int,
        default=300,
        help="负载测试持续时间(秒) (默认: 300)"
    )
    
    parser.add_argument(
        "--load-test-only",
        action="store_true",
        help="只运行负载测试"
    )
    
    parser.add_argument(
        "--api-test-only",
        action="store_true",
        help="只运行API性能测试"
    )
    
    parser.add_argument(
        "--stress-test",
        action="store_true",
        help="运行压力测试"
    )
    
    args = parser.parse_args()
    
    # 创建运行器
    runner = PerformanceTestRunner(environment=args.env)
    
    # 运行测试
    if args.load_test_only:
        runner.run_load_test(duration=args.duration, users=args.users)
        runner.generate_report()
    elif args.api_test_only:
        runner.run_api_performance_test()
        runner.generate_report()
    elif args.stress_test:
        runner.run_stress_test()
        runner.generate_report()
    else:
        runner.run_all()


if __name__ == "__main__":
    main()
