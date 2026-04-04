"""
负载测试脚本 - 使用Locust
Load Testing Script

模拟正常用户访问模式，测试系统在预期负载下的表现。
"""

import random
import json
from typing import Optional
from locust import HttpUser, task, between, events
from locust.runners import MasterRunner


class FormalMathUser(HttpUser):
    """
    FormalMath 模拟用户
    模拟真实用户浏览数学概念、搜索、查看数学家等行为
    """
    
    # 思考时间: 1-5秒
    wait_time = between(1, 5)
    
    # 测试数据
    concept_ids = [
        "set_theory", "group_theory", "real_analysis", 
        "topology", "algebraic_geometry", "number_theory",
        "differential_geometry", "complex_analysis", "category_theory",
        "homological_algebra", "representation_theory", "functional_analysis"
    ]
    
    mathematician_slugs = [
        "galois", "riemann", "grothendieck", "poincare", 
        "hilbert", "noether", "euler", "gauss", "newton", "leibniz"
    ]
    
    search_queries = [
        "群论", "拓扑", "代数几何", "微积分", "线性代数",
        "数论", "概率论", "微分方程", "泛函分析", "同调代数"
    ]
    
    def on_start(self):
        """用户启动时执行"""
        # 模拟用户登录/初始化
        self.client.get("/api/health")
    
    def on_stop(self):
        """用户停止时执行"""
        pass
    
    @task(40)
    def browse_concepts(self):
        """浏览概念列表 - 最高频操作"""
        # 获取概念列表
        with self.client.get(
            "/api/concepts",
            params={"page": random.randint(1, 10), "limit": 20},
            catch_response=True,
            name="GET /api/concepts (list)"
        ) as response:
            if response.status_code == 200:
                data = response.json()
                if isinstance(data, dict) and "items" in data:
                    response.success()
                else:
                    response.failure("Invalid response format")
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(30)
    def view_concept_detail(self):
        """查看概念详情"""
        concept_id = random.choice(self.concept_ids)
        with self.client.get(
            f"/api/concepts/{concept_id}",
            catch_response=True,
            name="GET /api/concepts/{id}"
        ) as response:
            if response.status_code == 200:
                response.success()
            elif response.status_code == 404:
                response.success()  # 404是正常情况
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(20)
    def search_content(self):
        """搜索内容"""
        query = random.choice(self.search_queries)
        with self.client.get(
            "/api/search",
            params={"q": query, "type": random.choice(["all", "concepts", "mathematicians"])},
            catch_response=True,
            name="GET /api/search"
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(15)
    def view_mathematician(self):
        """查看数学家详情"""
        slug = random.choice(self.mathematician_slugs)
        with self.client.get(
            f"/api/mathematicians/{slug}",
            catch_response=True,
            name="GET /api/mathematicians/{slug}"
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(10)
    def view_courses(self):
        """查看课程列表"""
        universities = ["mit", "harvard", "stanford", "princeton", "eth"]
        with self.client.get(
            "/api/courses",
            params={
                "university": random.choice(universities),
                "page": random.randint(1, 5)
            },
            catch_response=True,
            name="GET /api/courses"
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(5)
    def view_related_concepts(self):
        """查看相关概念"""
        concept_id = random.choice(self.concept_ids)
        with self.client.get(
            f"/api/concepts/{concept_id}/related",
            catch_response=True,
            name="GET /api/concepts/{id}/related"
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Status code: {response.status_code}")
    
    @task(3)
    def get_learning_path(self):
        """获取学习路径"""
        concept_id = random.choice(self.concept_ids)
        with self.client.get(
            f"/api/concepts/{concept_id}/learning-path",
            catch_response=True,
            name="GET /api/concepts/{id}/learning-path"
        ) as response:
            if response.status_code == 200:
                response.success()
            else:
                response.failure(f"Status code: {response.status_code}")


class HeavyUser(FormalMathUser):
    """重度用户 - 更频繁的请求"""
    weight = 1
    wait_time = between(0.5, 2)


class LightUser(FormalMathUser):
    """轻度用户 - 较少的请求"""
    weight = 3
    wait_time = between(3, 10)


# Locust事件处理
@events.test_start.add_listener
def on_test_start(environment, **kwargs):
    """测试开始时执行"""
    print("=" * 60)
    print("FormalMath 负载测试开始")
    print("=" * 60)
    print(f"目标URL: {environment.host}")
    print(f"并发用户数: {environment.runner.target_user_count}")
    print("=" * 60)


@events.test_stop.add_listener
def on_test_stop(environment, **kwargs):
    """测试结束时执行"""
    print("=" * 60)
    print("FormalMath 负载测试结束")
    print("=" * 60)
    
    # 输出统计摘要
    stats = environment.runner.stats
    print(f"总请求数: {stats.total.num_requests}")
    print(f"失败数: {stats.total.num_failures}")
    if stats.total.num_requests > 0:
        print(f"平均响应时间: {stats.total.avg_response_time:.2f}ms")
        print(f"95%响应时间: {stats.total.get_response_time_percentile(0.95):.2f}ms")
        print(f"错误率: {(stats.total.num_failures / stats.total.num_requests * 100):.2f}%")
    print("=" * 60)


# 命令行运行说明
if __name__ == "__main__":
    print("""
    负载测试运行命令:
    
    # Web界面模式
    locust -f load_test.py --host=http://localhost:8000
    
    # 命令行模式 - 100用户，每秒生成10个，运行5分钟
    locust -f load_test.py \
        --host=http://localhost:8000 \
        --users 100 \
        --spawn-rate 10 \
        --run-time 5m \
        --headless \
        --html=reports/load_test_report.html \
        --csv=reports/load_test
    
    # 分布式模式 (主节点)
    locust -f load_test.py --master
    
    # 分布式模式 (工作节点)
    locust -f load_test.py --worker --master-host=localhost
    """)
