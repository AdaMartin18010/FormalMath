"""
压力测试脚本 - 使用Locust
Stress Testing Script

测试系统在高负载下的稳定性和极限性能。
通过逐步增加负载，找出系统的瓶颈和崩溃点。
"""

import random
import time
from typing import Dict, List
from dataclasses import dataclass, asdict
from locust import HttpUser, task, between, events
from locust.runners import MasterRunner


@dataclass
class StressMetrics:
    """压力测试指标"""
    current_users: int = 0
    peak_users: int = 0
    total_requests: int = 0
    total_failures: int = 0
    max_response_time: float = 0.0
    error_rate_threshold: float = 0.05
    
    def to_dict(self) -> Dict:
        return asdict(self)


# 全局指标
stress_metrics = StressMetrics()


class StressTestUser(HttpUser):
    """
    压力测试用户
    执行高强度的API调用，测试系统极限
    """
    
    wait_time = between(0.1, 0.5)  # 更短的思考时间
    
    # 测试数据池
    concept_pool = [f"concept_{i}" for i in range(1, 101)]
    search_terms = ["数学", "代数", "几何", "分析", "拓扑", "数论"] * 10
    
    def on_start(self):
        """用户启动"""
        global stress_metrics
        stress_metrics.current_users += 1
        stress_metrics.peak_users = max(stress_metrics.peak_users, stress_metrics.current_users)
    
    def on_stop(self):
        """用户停止"""
        global stress_metrics
        stress_metrics.current_users -= 1
    
    @task(50)
    def stress_api_health(self):
        """压力测试 - 健康检查端点"""
        with self.client.get(
            "/api/health",
            catch_response=True,
            name="STRESS /api/health"
        ) as response:
            self._record_metrics(response)
    
    @task(30)
    def stress_concept_list(self):
        """压力测试 - 概念列表"""
        with self.client.get(
            "/api/concepts",
            params={"page": random.randint(1, 20), "limit": 50},
            catch_response=True,
            name="STRESS /api/concepts"
        ) as response:
            self._record_metrics(response)
    
    @task(20)
    def stress_concept_detail(self):
        """压力测试 - 概念详情"""
        concept_id = random.choice(self.concept_pool)
        with self.client.get(
            f"/api/concepts/{concept_id}",
            catch_response=True,
            name="STRESS /api/concepts/{id}"
        ) as response:
            self._record_metrics(response)
    
    @task(15)
    def stress_search(self):
        """压力测试 - 搜索API"""
        term = random.choice(self.search_terms)
        with self.client.get(
            "/api/search",
            params={"q": term, "limit": 20},
            catch_response=True,
            name="STRESS /api/search"
        ) as response:
            self._record_metrics(response)
    
    @task(10)
    def stress_heavy_query(self):
        """压力测试 - 复杂查询"""
        with self.client.get(
            "/api/concepts",
            params={
                "page": 1,
                "limit": 100,
                "include_related": "true",
                "include_prerequisites": "true"
            },
            catch_response=True,
            name="STRESS /api/concepts (heavy)"
        ) as response:
            self._record_metrics(response)
    
    @task(5)
    def stress_batch_request(self):
        """压力测试 - 批量请求"""
        # 模拟连续请求
        for i in range(5):
            with self.client.get(
                f"/api/concepts/{random.choice(self.concept_pool)}",
                catch_response=True,
                name="STRESS /api/concepts/{id} (batch)"
            ) as response:
                self._record_metrics(response)
    
    def _record_metrics(self, response):
        """记录性能指标"""
        global stress_metrics
        stress_metrics.total_requests += 1
        
        if response.status_code >= 400:
            stress_metrics.total_failures += 1
            response.failure(f"HTTP {response.status_code}")
        else:
            stress_metrics.max_response_time = max(
                stress_metrics.max_response_time,
                response.elapsed.total_seconds() * 1000
            )
            response.success()


class RampUpLoadShape:
    """
    阶梯式负载增长形状
    每60秒增加50个用户，直到达到1000用户或错误率超过5%
    """
    
    stages = [
        (60, 50),      # 1分钟: 50用户
        (120, 100),    # 2分钟: 100用户
        (180, 200),    # 3分钟: 200用户
        (240, 300),    # 4分钟: 300用户
        (300, 500),    # 5分钟: 500用户
        (360, 700),    # 6分钟: 700用户
        (420, 1000),   # 7分钟: 1000用户
        (480, 1000),   # 8分钟: 保持1000用户
        (540, 0),      # 9分钟: 降为0
    ]
    
    def __init__(self):
        self.start_time = None
    
    def tick(self, run_time: float) -> tuple:
        """返回当前阶段的目标用户数"""
        if self.start_time is None:
            self.start_time = time.time()
        
        elapsed = time.time() - self.start_time
        
        for duration, users in self.stages:
            if elapsed < duration:
                return users, users / 10  # spawn_rate = users / 10
        
        return None  # 测试结束


class StepLoadShape:
    """阶梯式负载"""
    
    step_time = 60  # 每步持续时间
    step_load = 100  # 每步增加用户数
    spawn_rate = 20  # 每秒生成用户数
    time_limit = 600  # 总时间限制
    
    def tick(self, run_time: float) -> tuple:
        current_step = run_time // self.step_time + 1
        user_count = current_step * self.step_load
        
        if run_time > self.time_limit:
            return None
        
        return user_count, self.spawn_rate


# Locust事件处理
@events.test_start.add_listener
def on_test_start(environment, **kwargs):
    """测试开始"""
    print("=" * 70)
    print("FormalMath 压力测试开始")
    print("=" * 70)
    print("测试策略: 阶梯式负载增长")
    print("目标: 找出系统极限和瓶颈")
    print("=" * 70)


@events.test_stop.add_listener
def on_test_stop(environment, **kwargs):
    """测试结束"""
    global stress_metrics
    
    print("=" * 70)
    print("FormalMath 压力测试结束")
    print("=" * 70)
    
    stats = environment.runner.stats
    print(f"\n📊 测试结果摘要:")
    print(f"  峰值并发用户: {stress_metrics.peak_users}")
    print(f"  总请求数: {stress_metrics.total_requests:,}")
    print(f"  总失败数: {stress_metrics.total_failures:,}")
    
    if stress_metrics.total_requests > 0:
        error_rate = stress_metrics.total_failures / stress_metrics.total_requests * 100
        print(f"  错误率: {error_rate:.2f}%")
        print(f"  最大响应时间: {stress_metrics.max_response_time:.2f}ms")
        
        # 判断系统稳定性
        if error_rate < 1:
            stability = "优秀 ✓"
        elif error_rate < 5:
            stability = "良好"
        else:
            stability = "需要优化 ⚠"
        print(f"  系统稳定性: {stability}")
    
    print("=" * 70)
    
    # 保存详细报告
    _save_stress_report(environment)


def _save_stress_report(environment):
    """保存压力测试报告"""
    import json
    from datetime import datetime
    
    stats = environment.runner.stats
    
    report = {
        "test_type": "stress_test",
        "timestamp": datetime.now().isoformat(),
        "host": environment.host,
        "summary": {
            "total_requests": stats.total.num_requests,
            "total_failures": stats.total.num_failures,
            "avg_response_time": stats.total.avg_response_time,
            "min_response_time": stats.total.min_response_time,
            "max_response_time": stats.total.max_response_time,
            "peak_concurrent_users": stress_metrics.peak_users
        },
        "percentiles": {
            "50%": stats.total.get_response_time_percentile(0.5),
            "75%": stats.total.get_response_time_percentile(0.75),
            "90%": stats.total.get_response_time_percentile(0.90),
            "95%": stats.total.get_response_time_percentile(0.95),
            "99%": stats.total.get_response_time_percentile(0.99)
        }
    }
    
    filename = f"reports/stress_test_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    try:
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        print(f"\n📄 详细报告已保存: {filename}")
    except Exception as e:
        print(f"\n⚠ 保存报告失败: {e}")


# 命令行说明
if __name__ == "__main__":
    print("""
    压力测试运行命令:
    
    # Web界面模式
    locust -f stress_test.py --host=http://localhost:8000
    
    # 命令行模式 - 逐步增加到1000用户
    locust -f stress_test.py \
        --host=http://localhost:8000 \
        --class-picker \
        --headless \
        --run-time 10m \
        --html=reports/stress_test_report.html \
        --csv=reports/stress_test
    
    # 指定负载形状
    locust -f stress_test.py --host=http://localhost:8000 StepLoadShape
    """)
