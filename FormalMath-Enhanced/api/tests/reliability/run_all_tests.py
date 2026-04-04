"""
API可靠性测试运行器

运行所有可靠性测试并生成综合报告

使用方法:
    python tests/reliability/run_all_tests.py
    
选项:
    --functional    仅运行功能测试
    --performance   仅运行性能测试
    --security      仅运行安全测试
    --fault         仅运行容错测试
    --all           运行所有测试（默认）
"""
import sys
import os
import argparse
import subprocess
import json
from datetime import datetime
from pathlib import Path

# 添加项目路径
sys.path.insert(0, str(Path(__file__).parent.parent.parent))


class TestRunner:
    """测试运行器"""
    
    def __init__(self):
        self.results = {}
        self.start_time = None
        self.end_time = None
    
    def run_functional_tests(self) -> dict:
        """运行功能测试"""
        print("\n" + "="*80)
        print("运行功能测试...")
        print("="*80)
        
        result = subprocess.run(
            [sys.executable, "-m", "pytest", 
             "tests/reliability/test_api_functional.py", 
             "-v", "--tb=short"],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent.parent)
        )
        
        return {
            "stdout": result.stdout,
            "stderr": result.stderr,
            "returncode": result.returncode,
            "passed": "passed" in result.stdout and result.returncode == 0
        }
    
    def run_performance_tests(self) -> dict:
        """运行性能测试"""
        print("\n" + "="*80)
        print("运行性能测试...")
        print("="*80)
        
        result = subprocess.run(
            [sys.executable, "-m", "pytest", 
             "tests/reliability/test_api_performance.py", 
             "-v", "-m", "performance", "--tb=short"],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent.parent)
        )
        
        return {
            "stdout": result.stdout,
            "stderr": result.stderr,
            "returncode": result.returncode,
            "passed": result.returncode == 0
        }
    
    def run_security_tests(self) -> dict:
        """运行安全测试"""
        print("\n" + "="*80)
        print("运行安全测试...")
        print("="*80)
        
        result = subprocess.run(
            [sys.executable, "-m", "pytest", 
             "tests/reliability/test_api_security.py", 
             "-v", "-m", "security", "--tb=short"],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent.parent)
        )
        
        return {
            "stdout": result.stdout,
            "stderr": result.stderr,
            "returncode": result.returncode,
            "passed": result.returncode == 0
        }
    
    def run_fault_tolerance_tests(self) -> dict:
        """运行容错测试"""
        print("\n" + "="*80)
        print("运行容错测试...")
        print("="*80)
        
        result = subprocess.run(
            [sys.executable, "-m", "pytest", 
             "tests/reliability/test_api_fault_tolerance.py", 
             "-v", "-m", "fault_tolerance", "--tb=short"],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent.parent)
        )
        
        return {
            "stdout": result.stdout,
            "stderr": result.stderr,
            "returncode": result.returncode,
            "passed": result.returncode == 0
        }
    
    def generate_report(self) -> str:
        """生成测试报告"""
        report = []
        report.append("# FormalMath API 可靠性测试报告")
        report.append(f"\n生成时间: {datetime.now().isoformat()}")
        report.append(f"\n测试耗时: {self.end_time - self.start_time:.2f}秒")
        
        # 总体结果
        report.append("\n## 总体结果\n")
        
        all_passed = all(r.get("passed", False) for r in self.results.values())
        if all_passed:
            report.append("✅ **所有测试通过**")
        else:
            report.append("❌ **部分测试失败**")
        
        # 各模块结果
        report.append("\n## 各模块测试结果\n")
        
        for test_type, result in self.results.items():
            status = "✅ 通过" if result.get("passed") else "❌ 失败"
            report.append(f"- **{test_type}**: {status}")
        
        # 详细结果
        report.append("\n## 详细结果\n")
        
        for test_type, result in self.results.items():
            report.append(f"\n### {test_type}\n")
            report.append(f"返回码: {result.get('returncode')}")
            
            if result.get('stdout'):
                report.append("\n**标准输出:**")
                report.append("```")
                # 限制输出长度
                stdout = result['stdout'][-2000:] if len(result['stdout']) > 2000 else result['stdout']
                report.append(stdout)
                report.append("```")
            
            if result.get('stderr'):
                report.append("\n**标准错误:**")
                report.append("```")
                stderr = result['stderr'][-1000:] if len(result['stderr']) > 1000 else result['stderr']
                report.append(stderr)
                report.append("```")
        
        # 建议
        report.append("\n## 改进建议\n")
        
        if not self.results.get("functional", {}).get("passed"):
            report.append("- **功能测试**: 检查API业务逻辑实现")
        
        if not self.results.get("performance", {}).get("passed"):
            report.append("- **性能测试**: 考虑添加缓存、优化数据库查询")
        
        if not self.results.get("security", {}).get("passed"):
            report.append("- **安全测试**: 加强输入验证和防护措施")
        
        if not self.results.get("fault_tolerance", {}).get("passed"):
            report.append("- **容错测试**: 完善异常处理和降级机制")
        
        return "\n".join(report)
    
    def run(self, args):
        """运行测试"""
        self.start_time = datetime.now().timestamp()
        
        if args.functional or args.all:
            self.results["功能测试"] = self.run_functional_tests()
        
        if args.performance or args.all:
            self.results["性能测试"] = self.run_performance_tests()
        
        if args.security or args.all:
            self.results["安全测试"] = self.run_security_tests()
        
        if args.fault or args.all:
            self.results["容错测试"] = self.run_fault_tolerance_tests()
        
        self.end_time = datetime.now().timestamp()
        
        # 生成并输出报告
        report = self.generate_report()
        print("\n" + "="*80)
        print(report)
        print("="*80)
        
        # 保存报告
        report_path = Path(__file__).parent / "test_report.md"
        with open(report_path, "w", encoding="utf-8") as f:
            f.write(report)
        
        print(f"\n报告已保存到: {report_path}")
        
        # 返回整体测试状态
        return all(r.get("passed", False) for r in self.results.values())


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="FormalMath API可靠性测试")
    parser.add_argument("--functional", action="store_true", help="仅运行功能测试")
    parser.add_argument("--performance", action="store_true", help="仅运行性能测试")
    parser.add_argument("--security", action="store_true", help="仅运行安全测试")
    parser.add_argument("--fault", action="store_true", help="仅运行容错测试")
    parser.add_argument("--all", action="store_true", help="运行所有测试（默认）")
    
    args = parser.parse_args()
    
    # 如果没有指定任何测试类型，默认运行所有
    if not any([args.functional, args.performance, args.security, args.fault]):
        args.all = True
    
    runner = TestRunner()
    success = runner.run(args)
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
