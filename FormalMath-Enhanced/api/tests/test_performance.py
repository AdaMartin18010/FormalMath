"""
性能测试脚本

使用方法:
    python tests/test_performance.py
    
或使用pytest:
    pytest tests/test_performance.py -v
"""
import asyncio
import time
import statistics
import httpx
import pytest
from concurrent.futures import ThreadPoolExecutor
from typing import List, Dict, Any

# 测试配置
BASE_URL = "http://localhost:8000"
CONCURRENT_USERS = [10, 50, 100]  # 并发用户数
TEST_DURATION = 30  # 每个测试持续时间（秒）


class PerformanceTester:
    """性能测试器"""
    
    def __init__(self, base_url: str = BASE_URL):
        self.base_url = base_url
        self.results = []
    
    async def test_endpoint(
        self,
        client: httpx.AsyncClient,
        endpoint: str,
        method: str = "GET",
        data: Dict = None
    ) -> Dict[str, Any]:
        """测试单个端点"""
        start_time = time.time()
        
        try:
            if method == "GET":
                response = await client.get(f"{self.base_url}{endpoint}")
            elif method == "POST":
                response = await client.post(
                    f"{self.base_url}{endpoint}",
                    json=data
                )
            else:
                raise ValueError(f"不支持的HTTP方法: {method}")
            
            elapsed = time.time() - start_time
            
            return {
                "success": response.status_code < 400,
                "status_code": response.status_code,
                "response_time": elapsed,
                "content_length": len(response.content),
            }
            
        except Exception as e:
            return {
                "success": False,
                "error": str(e),
                "response_time": time.time() - start_time,
            }
    
    async def concurrent_test(
        self,
        endpoint: str,
        concurrent_users: int,
        duration: int,
        method: str = "GET",
        data: Dict = None
    ) -> Dict[str, Any]:
        """并发压力测试"""
        print(f"\n测试端点: {endpoint}")
        print(f"并发用户数: {concurrent_users}")
        print(f"测试时长: {duration}秒")
        
        results = []
        start_time = time.time()
        request_count = 0
        
        async with httpx.AsyncClient(timeout=30.0) as client:
            while time.time() - start_time < duration:
                tasks = []
                for _ in range(concurrent_users):
                    task = self.test_endpoint(client, endpoint, method, data)
                    tasks.append(task)
                
                batch_results = await asyncio.gather(*tasks, return_exceptions=True)
                
                for result in batch_results:
                    if isinstance(result, Exception):
                        results.append({
                            "success": False,
                            "error": str(result),
                            "response_time": 0
                        })
                    else:
                        results.append(result)
                
                request_count += len(batch_results)
        
        # 计算统计数据
        successful = [r for r in results if r.get("success")]
        failed = [r for r in results if not r.get("success")]
        
        response_times = [r["response_time"] for r in successful if "response_time" in r]
        
        stats = {
            "endpoint": endpoint,
            "concurrent_users": concurrent_users,
            "total_requests": len(results),
            "successful_requests": len(successful),
            "failed_requests": len(failed),
            "success_rate": len(successful) / len(results) * 100 if results else 0,
            "requests_per_second": len(results) / duration,
        }
        
        if response_times:
            stats.update({
                "avg_response_time": statistics.mean(response_times),
                "min_response_time": min(response_times),
                "max_response_time": max(response_times),
                "median_response_time": statistics.median(response_times),
                "p95_response_time": sorted(response_times)[int(len(response_times) * 0.95)],
                "p99_response_time": sorted(response_times)[int(len(response_times) * 0.99)],
            })
        
        return stats
    
    async def run_all_tests(self):
        """运行所有性能测试"""
        print("=" * 60)
        print("FormalMath API 性能测试")
        print("=" * 60)
        
        test_cases = [
            # (端点, 方法, 数据)
            ("/health", "GET", None),
            ("/api/v1/concepts?page=1&page_size=20", "GET", None),
            ("/api/v1/graph/stats", "GET", None),
        ]
        
        all_results = []
        
        for endpoint, method, data in test_cases:
            for concurrent in CONCURRENT_USERS:
                result = await self.concurrent_test(
                    endpoint=endpoint,
                    concurrent_users=concurrent,
                    duration=TEST_DURATION,
                    method=method,
                    data=data
                )
                all_results.append(result)
                self.print_result(result)
        
        # 打印汇总
        self.print_summary(all_results)
        
        return all_results
    
    def print_result(self, result: Dict[str, Any]):
        """打印单个测试结果"""
        print("\n" + "-" * 60)
        print(f"端点: {result['endpoint']}")
        print(f"并发用户: {result['concurrent_users']}")
        print(f"总请求数: {result['total_requests']}")
        print(f"成功率: {result['success_rate']:.2f}%")
        print(f"RPS: {result['requests_per_second']:.2f}")
        
        if 'avg_response_time' in result:
            print(f"平均响应时间: {result['avg_response_time']*1000:.2f}ms")
            print(f"P95响应时间: {result['p95_response_time']*1000:.2f}ms")
            print(f"P99响应时间: {result['p99_response_time']*1000:.2f}ms")
    
    def print_summary(self, results: List[Dict[str, Any]]):
        """打印测试汇总"""
        print("\n" + "=" * 60)
        print("测试汇总")
        print("=" * 60)
        
        for result in results:
            status = "✓" if result['success_rate'] > 95 else "✗"
            print(f"{status} {result['endpoint']} (并发{result['concurrent_users']}): "
                  f"{result['success_rate']:.1f}% 成功率, "
                  f"{result['requests_per_second']:.1f} RPS")


def test_cache_performance():
    """测试缓存性能对比"""
    print("\n" + "=" * 60)
    print("缓存性能测试")
    print("=" * 60)
    
    # 这里可以添加缓存命中率的测试
    print("缓存测试需要连接到Redis服务器")
    print("建议使用redis-benchmark工具测试Redis性能")


def test_database_pool():
    """测试数据库连接池性能"""
    print("\n" + "=" * 60)
    print("数据库连接池测试")
    print("=" * 60)
    
    print("连接池测试建议:")
    print("1. 使用 /health/pool 端点查看连接池状态")
    print("2. 监控活跃连接数")
    print("3. 测试连接池耗尽时的行为")


# Pytest测试函数
@pytest.mark.asyncio
async def test_health_endpoint_performance():
    """测试健康检查端点性能"""
    tester = PerformanceTester()
    result = await tester.concurrent_test(
        endpoint="/health",
        concurrent_users=10,
        duration=5
    )
    
    assert result['success_rate'] > 95, "成功率应大于95%"
    assert result['avg_response_time'] < 0.1, "平均响应时间应小于100ms"


@pytest.mark.asyncio
async def test_concepts_endpoint_performance():
    """测试概念列表端点性能"""
    tester = PerformanceTester()
    result = await tester.concurrent_test(
        endpoint="/api/v1/concepts?page=1&page_size=20",
        concurrent_users=10,
        duration=5
    )
    
    assert result['success_rate'] > 90, "成功率应大于90%"


if __name__ == "__main__":
    # 运行性能测试
    tester = PerformanceTester()
    asyncio.run(tester.run_all_tests())
    
    # 其他测试
    test_cache_performance()
    test_database_pool()
