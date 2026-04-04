"""
性能测试配置文件
Performance Test Configuration
"""

import os
from dataclasses import dataclass
from typing import Dict, List, Optional


@dataclass
class TestConfig:
    """测试配置基类"""
    name: str
    description: str
    base_url: str
    timeout: int = 30
    
    # API端点
    api_endpoints: Dict[str, str] = None
    
    # 前端页面
    frontend_pages: List[str] = None
    
    # 测试数据路径
    test_data_path: str = "./test_data"
    
    # 报告输出路径
    report_output_path: str = "./reports"
    
    def __post_init__(self):
        if self.api_endpoints is None:
            self.api_endpoints = {
                "concepts": "/api/concepts",
                "mathematicians": "/api/mathematicians",
                "search": "/api/search",
                "courses": "/api/courses",
                "health": "/api/health"
            }
        if self.frontend_pages is None:
            self.frontend_pages = [
                "/",
                "/concepts",
                "/mathematicians",
                "/courses",
                "/search"
            ]


@dataclass  
class LoadTestConfig(TestConfig):
    """负载测试配置"""
    # 用户数量
    users: int = 100
    # 每秒生成用户数
    spawn_rate: int = 10
    # 测试持续时间(秒)
    duration: int = 300
    # 思考时间(秒)
    think_time_min: float = 1.0
    think_time_max: float = 5.0


@dataclass
class StressTestConfig(TestConfig):
    """压力测试配置"""
    # 起始用户数
    initial_users: int = 50
    # 最大用户数
    max_users: int = 1000
    # 用户增量步长
    step_users: int = 50
    # 每阶段持续时间(秒)
    step_duration: int = 60
    # 达到错误率阈值时停止
    error_threshold: float = 0.05


@dataclass
class ApiPerformanceConfig(TestConfig):
    """API性能测试配置"""
    # 每个端点测试次数
    iterations: int = 100
    # 并发数
    concurrency: int = 10
    # 预热次数
    warmup: int = 10
    # 目标响应时间(ms)
    target_response_time: int = 200
    # 目标吞吐量(req/s)
    target_throughput: int = 100
    # 超时时间(秒)
    timeout: int = 10


@dataclass
class FrontendPerformanceConfig(TestConfig):
    """前端性能测试配置"""
    # Lighthouse配置
    lighthouse_runs: int = 3
    # 性能预算
    performance_budget: Dict[str, int] = None
    # 设备类型
    device_type: str = "desktop"  # desktop, mobile
    # 网络节流
    network_throttling: str = "Slow 3G"  # Slow 3G, Fast 3G, 4G, none
    
    def __post_init__(self):
        super().__post_init__()
        if self.performance_budget is None:
            self.performance_budget = {
                "first_contentful_paint": 1800,
                "largest_contentful_paint": 2500,
                "time_to_interactive": 3500,
                "cumulative_layout_shift": 0.1,
                "total_blocking_time": 200,
                "speed_index": 3400
            }


# 环境配置
ENVIRONMENTS = {
    "development": {
        "base_url": "http://localhost:3000",
        "api_url": "http://localhost:8000"
    },
    "staging": {
        "base_url": "https://staging.formalmath.org",
        "api_url": "https://api-staging.formalmath.org"
    },
    "production": {
        "base_url": "https://formalmath.org",
        "api_url": "https://api.formalmath.org"
    }
}


def get_config(env: str = "development") -> Dict:
    """获取环境配置"""
    return ENVIRONMENTS.get(env, ENVIRONMENTS["development"])


def create_load_test_config(env: str = "development") -> LoadTestConfig:
    """创建负载测试配置"""
    config = get_config(env)
    return LoadTestConfig(
        name="FormalMath Load Test",
        description="模拟正常用户负载",
        base_url=config["base_url"]
    )


def create_stress_test_config(env: str = "development") -> StressTestConfig:
    """创建压力测试配置"""
    config = get_config(env)
    return StressTestConfig(
        name="FormalMath Stress Test",
        description="测试系统极限性能",
        base_url=config["base_url"]
    )


def create_api_performance_config(env: str = "development") -> ApiPerformanceConfig:
    """创建API性能测试配置"""
    config = get_config(env)
    return ApiPerformanceConfig(
        name="FormalMath API Performance Test",
        description="API端点性能基准测试",
        base_url=config["api_url"]
    )


def create_frontend_performance_config(env: str = "development") -> FrontendPerformanceConfig:
    """创建前端性能测试配置"""
    config = get_config(env)
    return FrontendPerformanceConfig(
        name="FormalMath Frontend Performance Test",
        description="前端页面性能基准测试",
        base_url=config["base_url"]
    )
