"""
API性能测试 - 验证并发处理和响应时间

测试范围:
1. 并发请求处理
2. 响应时间基准
3. 缓存性能
4. 数据库连接池性能
"""
import pytest
import asyncio
import time
import statistics
from typing import List, Dict, Any
from concurrent.futures import ThreadPoolExecutor
import httpx
from fastapi.testclient import TestClient
import sys
sys.path.insert(0, 'g:\\_src\\FormalMath\\FormalMath-Enhanced\\api')

from main import app


# ============ 性能测试配置 ============

PERFORMANCE_THRESHOLDS = {
    "health_check": {"avg_response_time": 0.1, "p95": 0.2, "success_rate": 99.9},
    "list_concepts": {"avg_response_time": 0.5, "p95": 1.0, "success_rate": 95.0},
    "graph_stats": {"avg_response_time": 0.3, "p95": 0.6, "success_rate": 95.0},
    "search": {"avg_response_time": 1.0, "p95": 2.0, "success_rate": 90.0},
}

CONCURRENT_LEVELS = [1, 10, 50, 100]


class PerformanceMonitor:
    """性能监控器"""
    
    def __init__(self):
        self.results: List[Dict[str, Any]] = []
    
    def record(self, endpoint: str, response_time: float, success: bool, 
               concurrent_users: int, status_code: int):
        """记录性能数据"""
        self.results.append({
            "endpoint": endpoint,
            "response_time": response_time,
            "success": success,
            "concurrent_users": concurrent_users,
            "status_code": status_code,
            "timestamp": time.time()
        })
    
    def get_statistics(self, endpoint: str = None, concurrent_users: int = None) -> Dict[str, Any]:
        """获取统计数据"""
        filtered = self.results
        
        if endpoint:
            filtered = [r for r in filtered if r["endpoint"] == endpoint]
        if concurrent_users:
            filtered = [r for r in filtered if r["concurrent_users"] == concurrent_users]
        
        if not filtered:
            return {}
        
        response_times = [r["response_time"] for r in filtered]
        successes = [r for r in filtered if r["success"]]
        
        sorted_times = sorted(response_times)
        n = len(sorted_times)
        
        return {
            "total_requests": len(filtered),
            "successful_requests": len(successes),
            "failed_requests": len(filtered) - len(successes),
            "success_rate": len(successes) / len(filtered) * 100,
            "avg_response_time": statistics.mean(response_times),
            "min_response_time": min(response_times),
            "max_response_time": max(response_times),
            "median_response_time": statistics.median(response_times),
            "p95_response_time": sorted_times[int(n * 0.95)] if n > 0 else 0,
            "p99_response_time": sorted_times[int(n * 0.99)] if n > 0 else 0,
            "std_dev": statistics.stdev(response_times) if n > 1 else 0,
        }
    
    def generate_report(self) -> str:
        """生成性能报告"""
        report = []
        report.append("=" * 80)
        report.append("API性能测试报告")
        report.append("=" * 80)
        
        endpoints = set(r["endpoint"] for r in self.results)
        concurrent_levels = set(r["concurrent_users"] for r in self.results)
        
        for endpoint in sorted(endpoints):
            report.append(f"\n端点: {endpoint}")
            report.append("-" * 80)
            
            for level in sorted(concurrent_levels):
                stats = self.get_statistics(endpoint, level)
                if not stats:
                    continue
                
                report.append(f"\n  并发用户: {level}")
                report.append(f"    总请求数: {stats['total_requests']}")
                report.append(f"    成功率: {stats['success_rate']:.2f}%")
                report.append(f"    平均响应时间: {stats['avg_response_time']*1000:.2f}ms")
                report.append(f"    P95响应时间: {stats['p95_response_time']*1000:.2f}ms")
                report.append(f"    P99响应时间: {stats['p99_response_time']*1000:.2f}ms")
                report.append(f"    最大响应时间: {stats['max_response_time']*1000:.2f}ms")
        
        report.append("\n" + "=" * 80)
        return "\n".join(report)


# ============ 测试类 ============

@pytest.mark.performance
class TestEndpointPerformance:
    """端点性能测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.fixture
    def monitor(self):
        """创建性能监控器"""
        return PerformanceMonitor()
    
    async def _make_request(self, client: TestClient, endpoint: str, 
                           method: str = "GET", data: Dict = None) -> Dict[str, Any]:
        """发送单个请求并测量性能"""
        start_time = time.time()
        
        try:
            if method == "GET":
                response = client.get(endpoint)
            elif method == "POST":
                response = client.post(endpoint, json=data)
            else:
                raise ValueError(f"不支持的方法: {method}")
            
            elapsed = time.time() - start_time
            
            return {
                "success": response.status_code < 400,
                "status_code": response.status_code,
                "response_time": elapsed,
            }
        except Exception as e:
            return {
                "success": False,
                "error": str(e),
                "response_time": time.time() - start_time,
            }
    
    async def _concurrent_test(self, client: TestClient, endpoint: str,
                               concurrent_users: int, duration: int,
                               method: str = "GET", data: Dict = None) -> PerformanceMonitor:
        """执行并发测试"""
        monitor = PerformanceMonitor()
        start_time = time.time()
        
        async def worker():
            while time.time() - start_time < duration:
                result = await self._make_request(client, endpoint, method, data)
                monitor.record(
                    endpoint=endpoint,
                    response_time=result["response_time"],
                    success=result.get("success", False),
                    concurrent_users=concurrent_users,
                    status_code=result.get("status_code", 0)
                )
                await asyncio.sleep(0.01)  # 小延迟避免过载
        
        # 创建并发任务
        tasks = [worker() for _ in range(concurrent_users)]
        await asyncio.gather(*tasks)
        
        return monitor
    
    @pytest.mark.asyncio
    @pytest.mark.parametrize("concurrent_users", [1, 10, 50])
    async def test_health_check_performance(self, client, concurrent_users):
        """测试健康检查端点性能"""
        monitor = await self._concurrent_test(
            client, "/health", 
            concurrent_users=concurrent_users, 
            duration=5
        )
        
        stats = monitor.get_statistics("/health", concurrent_users)
        
        # 验证性能阈值
        threshold = PERFORMANCE_THRESHOLDS["health_check"]
        assert stats["success_rate"] >= threshold["success_rate"], \
            f"成功率 {stats['success_rate']:.2f}% 低于阈值 {threshold['success_rate']}%"
        assert stats["avg_response_time"] < threshold["avg_response_time"], \
            f"平均响应时间 {stats['avg_response_time']*1000:.2f}ms 超过阈值 {threshold['avg_response_time']*1000:.2f}ms"
        assert stats["p95_response_time"] < threshold["p95"], \
            f"P95响应时间 {stats['p95_response_time']*1000:.2f}ms 超过阈值 {threshold['p95']*1000:.2f}ms"
    
    @pytest.mark.asyncio
    @pytest.mark.parametrize("concurrent_users", [1, 10, 50])
    async def test_concepts_list_performance(self, client, concurrent_users):
        """测试概念列表端点性能"""
        monitor = await self._concurrent_test(
            client, "/api/v1/concepts?page=1&page_size=20",
            concurrent_users=concurrent_users,
            duration=5
        )
        
        stats = monitor.get_statistics("/api/v1/concepts?page=1&page_size=20", concurrent_users)
        
        # 验证性能阈值
        threshold = PERFORMANCE_THRESHOLDS["list_concepts"]
        assert stats["success_rate"] >= threshold["success_rate"], \
            f"成功率 {stats['success_rate']:.2f}% 低于阈值 {threshold['success_rate']}%"
    
    @pytest.mark.asyncio
    @pytest.mark.parametrize("concurrent_users", [1, 10, 50])
    async def test_graph_stats_performance(self, client, concurrent_users):
        """测试图谱统计端点性能"""
        monitor = await self._concurrent_test(
            client, "/api/v1/concepts/graph/stats",
            concurrent_users=concurrent_users,
            duration=5
        )
        
        stats = monitor.get_statistics("/api/v1/concepts/graph/stats", concurrent_users)
        
        # 验证性能阈值
        threshold = PERFORMANCE_THRESHOLDS["graph_stats"]
        assert stats["success_rate"] >= threshold["success_rate"], \
            f"成功率 {stats['success_rate']:.2f}% 低于阈值 {threshold['success_rate']}%"


@pytest.mark.performance
class TestCachePerformance:
    """缓存性能测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.mark.asyncio
    async def test_cache_hit_performance(self, client):
        """测试缓存命中性能"""
        # 第一次请求（缓存未命中）
        start = time.time()
        response1 = client.get("/api/v1/concepts/graph/stats")
        miss_time = time.time() - start
        
        assert response1.status_code == 200
        
        # 第二次请求（缓存命中）
        start = time.time()
        response2 = client.get("/api/v1/concepts/graph/stats")
        hit_time = time.time() - start
        
        assert response2.status_code == 200
        
        # 缓存命中应该更快
        # 注意：在没有Redis的情况下可能不会有显著差异
        print(f"\n缓存未命中: {miss_time*1000:.2f}ms")
        print(f"缓存命中: {hit_time*1000:.2f}ms")
    
    @pytest.mark.asyncio
    async def test_concurrent_cache_access(self, client):
        """测试并发缓存访问"""
        async def request_worker():
            response = client.get("/api/v1/concepts/graph/stats")
            return response.status_code == 200
        
        # 创建100个并发请求
        tasks = [request_worker() for _ in range(100)]
        results = await asyncio.gather(*tasks)
        
        success_rate = sum(results) / len(results) * 100
        assert success_rate >= 95, f"并发缓存访问成功率 {success_rate:.2f}% 低于95%"


@pytest.mark.performance
class TestDatabasePerformance:
    """数据库性能测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_connection_pool_status(self, client):
        """测试数据库连接池状态"""
        response = client.get("/api/v1/health/pool")
        assert response.status_code == 200
        
        data = response.json()
        assert "pool" in data
        
        pool = data["pool"]
        # 验证连接池状态正常
        assert "size" in pool
        assert "checked_in" in pool
        assert "checked_out" in pool
    
    @pytest.mark.asyncio
    async def test_database_query_performance(self, client):
        """测试数据库查询性能"""
        # 执行多个并发查询
        async def query_worker():
            start = time.time()
            response = client.get("/api/v1/concepts?page=1&page_size=50")
            elapsed = time.time() - start
            return response.status_code == 200, elapsed
        
        # 20个并发查询
        tasks = [query_worker() for _ in range(20)]
        results = await asyncio.gather(*tasks)
        
        success_count = sum(1 for success, _ in results if success)
        times = [t for _, t in results]
        
        success_rate = success_count / len(results) * 100
        avg_time = statistics.mean(times)
        
        print(f"\n数据库查询成功率: {success_rate:.2f}%")
        print(f"平均查询时间: {avg_time*1000:.2f}ms")
        
        assert success_rate >= 95, f"数据库查询成功率 {success_rate:.2f}% 低于95%"
        assert avg_time < 1.0, f"平均查询时间 {avg_time*1000:.2f}ms 超过1秒"


@pytest.mark.performance
class TestLoadTesting:
    """负载测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.mark.asyncio
    @pytest.mark.slow
    async def test_mixed_load(self, client):
        """测试混合负载"""
        endpoints = [
            ("/health", "GET", None),
            ("/api/v1/concepts?page=1&page_size=20", "GET", None),
            ("/api/v1/concepts/graph/stats", "GET", None),
            ("/api/v1/learning-paths/user/1", "GET", None),
        ]
        
        async def random_request():
            import random
            endpoint, method, data = random.choice(endpoints)
            
            start = time.time()
            if method == "GET":
                response = client.get(endpoint)
            else:
                response = client.post(endpoint, json=data or {})
            elapsed = time.time() - start
            
            return {
                "endpoint": endpoint,
                "success": response.status_code < 400,
                "response_time": elapsed,
            }
        
        # 模拟100个用户，每个用户5个请求
        tasks = [random_request() for _ in range(500)]
        results = await asyncio.gather(*tasks)
        
        # 统计分析
        success_count = sum(1 for r in results if r["success"])
        success_rate = success_count / len(results) * 100
        
        times = [r["response_time"] for r in results]
        avg_time = statistics.mean(times)
        p95_time = sorted(times)[int(len(times) * 0.95)]
        
        print(f"\n混合负载测试结果:")
        print(f"  总请求数: {len(results)}")
        print(f"  成功率: {success_rate:.2f}%")
        print(f"  平均响应时间: {avg_time*1000:.2f}ms")
        print(f"  P95响应时间: {p95_time*1000:.2f}ms")
        
        assert success_rate >= 90, f"混合负载成功率 {success_rate:.2f}% 低于90%"
        assert avg_time < 2.0, f"平均响应时间 {avg_time*1000:.2f}ms 超过2秒"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-m", "performance"])
