"""
Pytest配置文件 - 可靠性测试

提供共享的fixtures和配置
"""
import pytest
import asyncio
from typing import Generator
from unittest.mock import Mock


# ============ 标记配置 ============

def pytest_configure(config):
    """配置pytest标记"""
    config.addinivalue_line("markers", "functional: 功能测试")
    config.addinivalue_line("markers", "performance: 性能测试")
    config.addinivalue_line("markers", "security: 安全测试")
    config.addinivalue_line("markers", "fault_tolerance: 容错测试")
    config.addinivalue_line("markers", "slow: 慢速测试")


# ============ Fixtures ============

@pytest.fixture(scope="session")
def event_loop():
    """创建事件循环"""
    loop = asyncio.get_event_loop_policy().new_event_loop()
    yield loop
    loop.close()


@pytest.fixture
def mock_redis():
    """模拟Redis客户端"""
    mock = Mock()
    mock.get.return_value = None
    mock.set.return_value = True
    mock.delete.return_value = True
    mock.exists.return_value = False
    mock.ping.return_value = True
    return mock


@pytest.fixture
def mock_celery():
    """模拟Celery应用"""
    mock = Mock()
    mock.delay.return_value = Mock(id="test_task_id", status="SUCCESS")
    mock.apply_async.return_value = Mock(id="test_task_id")
    return mock


@pytest.fixture
def sample_concept_data():
    """示例概念数据"""
    return {
        "id": "test_concept",
        "name": "测试概念",
        "branch": "algebra",
        "difficulty": "basic",
        "description": "这是一个测试概念",
        "prerequisites": ["prereq1", "prereq2"]
    }


@pytest.fixture
def sample_learning_path_data():
    """示例学习路径数据"""
    return {
        "user_id": 1,
        "target_concepts": ["algebra_basics", "linear_algebra"],
        "algorithm": "astar",
        "constraints": {"max_duration": 120},
        "async_mode": True
    }


@pytest.fixture
def sample_search_query():
    """示例搜索查询"""
    return {
        "query": "线性代数基础",
        "search_type": "hybrid",
        "k": 10,
        "rerank": True
    }


@pytest.fixture
def sample_recommendation_request():
    """示例推荐请求"""
    return {
        "user_id": 1,
        "n_recommendations": 10,
        "recommendation_type": "hybrid",
        "context": {"session_duration": 30}
    }


# ============ 钩子函数 ============

def pytest_collection_modifyitems(config, items):
    """修改测试项"""
    # 自动添加标记
    for item in items:
        # 根据文件名添加标记
        if "functional" in item.nodeid:
            item.add_marker(pytest.mark.functional)
        elif "performance" in item.nodeid:
            item.add_marker(pytest.mark.performance)
        elif "security" in item.nodeid:
            item.add_marker(pytest.mark.security)
        elif "fault_tolerance" in item.nodeid:
            item.add_marker(pytest.mark.fault_tolerance)


def pytest_runtest_setup(item):
    """测试设置"""
    # 检查是否需要跳过
    if "slow" in item.keywords and not item.config.getoption("--run-slow"):
        pytest.skip("需要 --run-slow 选项来运行慢速测试")


# ============ 自定义选项 ============

def pytest_addoption(parser):
    """添加命令行选项"""
    parser.addoption(
        "--run-slow",
        action="store_true",
        default=False,
        help="运行慢速测试"
    )
    parser.addoption(
        "--run-performance",
        action="store_true",
        default=False,
        help="运行性能测试"
    )
