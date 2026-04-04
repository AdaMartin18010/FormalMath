"""
API性能测试
API Performance Testing

使用pytest-benchmark进行细粒度的API性能基准测试
"""

import pytest
import asyncio
import time
import statistics
from typing import List, Dict, Any
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed
import requests
import aiohttp

from config import create_api_performance_config


# 测试配置
config = create_api_performance_config()


@dataclass
class ApiBenchmarkResult:
    """API基准测试结果"""
    endpoint: str
    method: str
    iterations: int
    total_time: float
    avg_time: float
    min_time: float
    max_time: float
    median_time: float
    p95_time: float
    p99_time: float
    requests_per_second: float
    error_count: int


class ApiPerformanceTester:
    """API性能测试器"""
    
    def __init__(self, base_url: str):
        self.base_url = base_url
        self.session = requests.Session()
        self.session.headers.update({
            "Accept": "application/json",
            "User-Agent": "FormalMath-PerformanceTest/1.0"
        })
    
    def benchmark_endpoint(
        self,
        endpoint: str,
        method: str = "GET",
        params: Dict = None,
        json_data: Dict = None,
        iterations: int = 100
    ) -> ApiBenchmarkResult:
        """对单个端点进行基准测试"""
        
        times = []
        error_count = 0
        url = f"{self.base_url}{endpoint}"
        
        # 预热
        for _ in range(min(10, iterations // 10)):
            try:
                self.session.request(method, url, params=params, json=json_data, timeout=10)
            except:
                pass
        
        # 正式测试
        start_total = time.perf_counter()
        
        for _ in range(iterations):
            start = time.perf_counter()
            try:
                response = self.session.request(
                    method, url, params=params, json=json_data, timeout=config.timeout
                )
                response.raise_for_status()
                elapsed = (time.perf_counter() - start) * 1000  # 转换为毫秒
                times.append(elapsed)
            except Exception as e:
                error_count += 1
                times.append(float('inf'))
        
        total_time = (time.perf_counter() - start_total) * 1000
        
        # 过滤掉失败的请求
        valid_times = [t for t in times if t != float('inf')]
        
        if not valid_times:
            return ApiBenchmarkResult(
                endpoint=endpoint, method=method, iterations=iterations,
                total_time=total_time, avg_time=0, min_time=0, max_time=0,
                median_time=0, p95_time=0, p99_time=0,
                requests_per_second=0, error_count=error_count
            )
        
        valid_times.sort()
        
        return ApiBenchmarkResult(
            endpoint=endpoint,
            method=method,
            iterations=iterations,
            total_time=total_time,
            avg_time=statistics.mean(valid_times),
            min_time=min(valid_times),
            max_time=max(valid_times),
            median_time=statistics.median(valid_times),
            p95_time=valid_times[int(len(valid_times) * 0.95)],
            p99_time=valid_times[int(len(valid_times) * 0.99)],
            requests_per_second=len(valid_times) / (total_time / 1000),
            error_count=error_count
        )
    
    def benchmark_concurrent(
        self,
        endpoint: str,
        method: str = "GET",
        params: Dict = None,
        concurrency: int = 10,
        iterations: int = 100
    ) -> ApiBenchmarkResult:
        """并发基准测试"""
        
        times = []
        error_count = 0
        url = f"{self.base_url}{endpoint}"
        
        def make_request(_):
            start = time.perf_counter()
            try:
                response = self.session.request(
                    method, url, params=params, timeout=config.timeout
                )
                response.raise_for_status()
                return (time.perf_counter() - start) * 1000
            except:
                return float('inf')
        
        start_total = time.perf_counter()
        
        with ThreadPoolExecutor(max_workers=concurrency) as executor:
            futures = [executor.submit(make_request, i) for i in range(iterations)]
            for future in as_completed(futures):
                result = future.result()
                if result == float('inf'):
                    error_count += 1
                times.append(result)
        
        total_time = (time.perf_counter() - start_total) * 1000
        valid_times = [t for t in times if t != float('inf')]
        valid_times.sort()
        
        if not valid_times:
            return ApiBenchmarkResult(
                endpoint=endpoint, method=method, iterations=iterations,
                total_time=total_time, avg_time=0, min_time=0, max_time=0,
                median_time=0, p95_time=0, p99_time=0,
                requests_per_second=0, error_count=error_count
            )
        
        return ApiBenchmarkResult(
            endpoint=endpoint,
            method=method,
            iterations=iterations,
            total_time=total_time,
            avg_time=statistics.mean(valid_times),
            min_time=min(valid_times),
            max_time=max(valid_times),
            median_time=statistics.median(valid_times),
            p95_time=valid_times[int(len(valid_times) * 0.95)],
            p99_time=valid_times[int(len(valid_times) * 0.99)],
            requests_per_second=len(valid_times) / (total_time / 1000),
            error_count=error_count
        )


# pytest-benchmark测试用例
class TestApiPerformance:
    """API性能测试类"""
    
    @pytest.fixture(scope="class")
    def tester(self):
        return ApiPerformanceTester(config.base_url)
    
    def test_health_endpoint(self, tester, benchmark):
        """测试健康检查端点"""
        result = benchmark(tester.benchmark_endpoint, "/api/health", iterations=100)
        assert result.avg_time < config.target_response_time, \
            f"平均响应时间 {result.avg_time:.2f}ms 超过目标 {config.target_response_time}ms"
    
    def test_concepts_list(self, tester, benchmark):
        """测试概念列表API"""
        result = benchmark(
            tester.benchmark_endpoint, 
            "/api/concepts",
            params={"page": 1, "limit": 20},
            iterations=50
        )
        assert result.avg_time < 500, f"平均响应时间 {result.avg_time:.2f}ms 超过500ms"
    
    def test_concept_detail(self, tester, benchmark):
        """测试概念详情API"""
        result = benchmark(
            tester.benchmark_endpoint,
            "/api/concepts/set_theory",
            iterations=50
        )
        assert result.avg_time < 300, f"平均响应时间 {result.avg_time:.2f}ms 超过300ms"
    
    def test_search_api(self, tester, benchmark):
        """测试搜索API"""
        result = benchmark(
            tester.benchmark_endpoint,
            "/api/search",
            params={"q": "群论", "limit": 10},
            iterations=30
        )
        assert result.avg_time < 1000, f"平均响应时间 {result.avg_time:.2f}ms 超过1000ms"
    
    def test_mathematicians_list(self, tester, benchmark):
        """测试数学家列表API"""
        result = benchmark(
            tester.benchmark_endpoint,
            "/api/mathematicians",
            params={"page": 1, "limit": 20},
            iterations=50
        )
        assert result.avg_time < 400, f"平均响应时间 {result.avg_time:.2f}ms 超过400ms"


class TestApiConcurrency:
    """API并发性能测试"""
    
    @pytest.fixture(scope="class")
    def tester(self):
        return ApiPerformanceTester(config.base_url)
    
    def test_concurrent_health_check(self, tester):
        """测试健康检查并发性能"""
        result = tester.benchmark_concurrent(
            "/api/health",
            concurrency=20,
            iterations=200
        )
        print(f"\n并发健康检查结果:")
        print(f"  平均响应时间: {result.avg_time:.2f}ms")
        print(f"  吞吐量: {result.requests_per_second:.2f} req/s")
        print(f"  错误数: {result.error_count}")
        
        assert result.requests_per_second > 50, \
            f"吞吐量 {result.requests_per_second:.2f} req/s 低于50 req/s"
        assert result.error_count < 5, f"错误数 {result.error_count} 太多"
    
    def test_concurrent_concepts(self, tester):
        """测试概念列表并发性能"""
        result = tester.benchmark_concurrent(
            "/api/concepts",
            params={"page": 1, "limit": 20},
            concurrency=10,
            iterations=100
        )
        print(f"\n并发概念列表结果:")
        print(f"  P95响应时间: {result.p95_time:.2f}ms")
        print(f"  吞吐量: {result.requests_per_second:.2f} req/s")
        
        assert result.p95_time < 1000, f"P95响应时间 {result.p95_time:.2f}ms 超过1000ms"


def run_all_benchmarks():
    """运行所有基准测试并生成报告"""
    tester = ApiPerformanceTester(config.base_url)
    
    endpoints = [
        ("/api/health", "GET", None, "健康检查"),
        ("/api/concepts", "GET", {"page": 1, "limit": 20}, "概念列表"),
        ("/api/concepts/set_theory", "GET", None, "概念详情"),
        ("/api/mathematicians", "GET", {"page": 1, "limit": 20}, "数学家列表"),
        ("/api/search", "GET", {"q": "群论", "limit": 10}, "搜索"),
        ("/api/courses", "GET", {"university": "mit"}, "课程列表"),
    ]
    
    results = []
    print("\n" + "=" * 80)
    print("API性能基准测试")
    print("=" * 80)
    
    for endpoint, method, params, name in endpoints:
        print(f"\n🔄 测试: {name} ({endpoint})")
        result = tester.benchmark_endpoint(endpoint, method, params, iterations=100)
        results.append((name, result))
        
        print(f"  平均响应时间: {result.avg_time:.2f}ms")
        print(f"  P95响应时间: {result.p95_time:.2f}ms")
        print(f"  吞吐量: {result.requests_per_second:.2f} req/s")
        print(f"  错误率: {result.error_count / result.iterations * 100:.2f}%")
    
    # 打印汇总
    print("\n" + "=" * 80)
    print("测试汇总")
    print("=" * 80)
    print(f"{'端点':<20} {'平均(ms)':<12} {'P95(ms)':<12} {'吞吐量(req/s)':<15} {'状态':<10}")
    print("-" * 80)
    
    for name, result in results:
        status = "✓ PASS" if result.avg_time < 500 and result.error_count == 0 else "✗ FAIL"
        print(f"{name:<20} {result.avg_time:<12.2f} {result.p95_time:<12.2f} "
              f"{result.requests_per_second:<15.2f} {status:<10}")
    
    return results


if __name__ == "__main__":
    print("""
    API性能测试运行方式:
    
    # 1. 使用pytest运行
    pytest api_performance_test.py -v --benchmark-only
    
    # 2. 生成JSON报告
    pytest api_performance_test.py --benchmark-json=reports/api_benchmark.json
    
    # 3. 保存对比基准
    pytest api_performance_test.py --benchmark-save=baseline
    
    # 4. 与基准对比
    pytest api_performance_test.py --benchmark-compare
    
    # 5. 直接运行所有基准测试
    python api_performance_test.py
    """)
    
    # 如果直接运行脚本
    import sys
    if len(sys.argv) == 1:
        run_all_benchmarks()
