"""
FormalMath - 负载测试脚本
目标：验证系统支持1000并发用户
使用Locust进行压力测试
"""

from locust import HttpUser, task, between, events
from locust.runners import MasterRunner
import random
import json
import time

# 测试配置
TARGET_RPS = 1000  # 目标每秒请求数
MAX_RESPONSE_TIME = 200  # 最大响应时间(ms)
ERROR_RATE_THRESHOLD = 0.01  # 错误率阈值 1%


class FormalMathUser(HttpUser):
    """模拟FormalMath用户行为"""
    
    wait_time = between(1, 3)  # 用户请求间隔1-3秒
    
    def on_start(self):
        """用户启动时执行 - 模拟登录"""
        self.client.get("/health")
        
    @task(10)
    def browse_homepage(self):
        """浏览首页 - 最高权重"""
        with self.client.get("/", catch_response=True) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Homepage failed: {response.status_code}")
    
    @task(5)
    def api_health_check(self):
        """API健康检查"""
        with self.client.get("/api/v1/health", catch_response=True) as response:
            if response.status_code == 200:
                data = response.json()
                if data.get("status") == "healthy":
                    response.success()
                else:
                    response.failure("API not healthy")
            else:
                response.failure(f"Health check failed: {response.status_code}")
    
    @task(4)
    def browse_math_concepts(self):
        """浏览数学概念"""
        concept_ids = [
            "group-theory", "ring-theory", "field-theory",
            "real-analysis", "complex-analysis",
            "topology", "algebraic-geometry"
        ]
        concept_id = random.choice(concept_ids)
        
        with self.client.get(
            f"/api/v1/concepts/{concept_id}",
            catch_response=True
        ) as response:
            if response.status_code == 200:
                response.success()
            elif response.status_code == 404:
                response.success()  # 404是正常响应
            else:
                response.failure(f"Concept fetch failed: {response.status_code}")
    
    @task(3)
    def search_content(self):
        """搜索内容"""
        search_terms = [
            "group", "ring", "field",
            "continuous", "differentiable",
            "homomorphism", "isomorphism",
            "lean4", "theorem proving"
        ]
        term = random.choice(search_terms)
        
        with self.client.get(
            f"/api/v1/search?q={term}",
            catch_response=True
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Search failed: {response.status_code}")
    
    @task(2)
    def get_lean_theorems(self):
        """获取Lean定理"""
        with self.client.get(
            "/api/v1/lean/theorems",
            params={"limit": 20, "offset": 0},
            catch_response=True
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Theorems fetch failed: {response.status_code}")
    
    @task(2)
    def post_calculation(self):
        """提交计算请求（重任务）"""
        calc_data = {
            "expression": "integral(x**2, (x, 0, 1))",
            "timeout": 30
        }
        
        with self.client.post(
            "/api/v1/calculate",
            json=calc_data,
            catch_response=True
        ) as response:
            if response.status_code in [200, 202]:
                response.success()
            else:
                response.failure(f"Calculation failed: {response.status_code}")
    
    @task(1)
    def get_user_progress(self):
        """获取用户进度（需要认证）"""
        # 模拟已认证用户
        headers = {"Authorization": "Bearer test-token"}
        
        with self.client.get(
            "/api/v1/user/progress",
            headers=headers,
            catch_response=True
        ) as response:
            if response.status_code in [200, 401]:  # 401也是正常响应
                response.success()
            else:
                response.failure(f"Progress fetch failed: {response.status_code}")
    
    @task(1)
    def concurrent_api_calls(self):
        """模拟并发API调用"""
        # 同时发起多个请求
        endpoints = [
            "/api/v1/concepts",
            "/api/v1/lean/theorems",
            "/api/v1/search?q=topology"
        ]
        
        for endpoint in endpoints:
            self.client.get(endpoint)


class StressTestUser(HttpUser):
    """压力测试用户 - 更高频率请求"""
    
    wait_time = between(0.1, 0.5)  # 100-500ms间隔
    
    @task
    def stress_test_api(self):
        """API压力测试"""
        self.client.get("/api/v1/health")


# 测试事件处理
@events.request.add_listener
def on_request(request_type, name, response_time, response_length, 
               response, context, exception, **kwargs):
    """记录每个请求的统计信息"""
    pass


@events.test_start.add_listener
def on_test_start(environment, **kwargs):
    """测试开始时执行"""
    print("=" * 60)
    print("FormalMath 负载测试开始")
    print(f"目标: 支持 {TARGET_RPS} 并发用户")
    print(f"响应时间目标: < {MAX_RESPONSE_TIME}ms (P95)")
    print(f"错误率目标: < {ERROR_RATE_THRESHOLD * 100}%")
    print("=" * 60)


@events.test_stop.add_listener
def on_test_stop(environment, **kwargs):
    """测试结束时执行"""
    print("\n" + "=" * 60)
    print("FormalMath 负载测试结束")
    
    if isinstance(environment.runner, MasterRunner):
        stats = environment.runner.stats
        
        # 计算统计信息
        total_requests = stats.total.num_requests
        total_failures = stats.total.num_failures
        avg_response_time = stats.total.avg_response_time
        p95_response_time = stats.total.get_response_time_percentile(0.95)
        error_rate = total_failures / total_requests if total_requests > 0 else 0
        
        print(f"\n测试结果统计:")
        print(f"  总请求数: {total_requests}")
        print(f"  失败请求: {total_failures}")
        print(f"  平均响应时间: {avg_response_time:.2f}ms")
        print(f"  P95响应时间: {p95_response_time:.2f}ms")
        print(f"  错误率: {error_rate * 100:.2f}%")
        
        # 测试通过标准
        passed = True
        print("\n测试通过标准检查:")
        
        if p95_response_time > MAX_RESPONSE_TIME:
            print(f"  ❌ P95响应时间 {p95_response_time:.2f}ms 超过目标 {MAX_RESPONSE_TIME}ms")
            passed = False
        else:
            print(f"  ✅ P95响应时间 {p95_response_time:.2f}ms 满足目标")
        
        if error_rate > ERROR_RATE_THRESHOLD:
            print(f"  ❌ 错误率 {error_rate * 100:.2f}% 超过目标 {ERROR_RATE_THRESHOLD * 100}%")
            passed = False
        else:
            print(f"  ✅ 错误率 {error_rate * 100:.2f}% 满足目标")
        
        if passed:
            print("\n✅ 负载测试通过!")
        else:
            print("\n❌ 负载测试未通过，需要优化")
    
    print("=" * 60)


# 自定义命令行参数
@events.init_command_line_parser.add_listener
def on_init_command_line_parser(parser):
    parser.add_argument(
        "--target-host",
        type=str,
        default="http://localhost",
        help="目标主机地址"
    )
    parser.add_argument(
        "--rps",
        type=int,
        default=1000,
        help="目标RPS"
    )


# 如果直接运行此脚本
if __name__ == "__main__":
    import sys
    from locust.main import main
    sys.argv = ["locust", "-f", __file__, "--host=http://localhost"]
    main()
