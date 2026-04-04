"""
Pytest配置和fixture
"""
import pytest
import sys
import os
from pathlib import Path
from unittest.mock import Mock, MagicMock

# 添加项目根目录到Python路径
PROJECT_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(PROJECT_ROOT / 'tools'))

# Fixture定义

@pytest.fixture
def sample_concept_data():
    """示例概念数据"""
    return {
        "concept_id": "test_group_001",
        "name": "群论",
        "category": "代数学",
        "description": "研究群的代数结构",
        "difficulty": "intermediate",
        "prerequisites": ["set_theory", "binary_operations"],
        "related_concepts": ["ring_theory", "field_theory"],
        "msc_codes": ["20-XX", "20A05"],
        "formalizations": {
            "mathlib4": "Mathlib.Algebra.Group.Basic"
        }
    }

@pytest.fixture
def sample_concepts_list():
    """示例概念列表"""
    return [
        {
            "concept_id": "concept_001",
            "name": "群论",
            "category": "代数学",
            "difficulty": "intermediate"
        },
        {
            "concept_id": "concept_002",
            "name": "拓扑学",
            "category": "几何学",
            "difficulty": "advanced"
        },
        {
            "concept_id": "concept_003",
            "name": "数论",
            "category": "数论",
            "difficulty": "beginner"
        }
    ]

@pytest.fixture
def sample_graph_data():
    """示例图谱数据"""
    return {
        "nodes": [
            {"id": "1", "name": "群论", "category": "代数"},
            {"id": "2", "name": "环论", "category": "代数"},
            {"id": "3", "name": "拓扑学", "category": "几何"}
        ],
        "edges": [
            {"source": "1", "target": "2", "type": "prerequisite"},
            {"source": "3", "target": "1", "type": "related"}
        ]
    }

@pytest.fixture
def sample_yaml_content():
    """示例YAML内容"""
    return """
concepts:
  - concept_id: test_001
    name: 测试概念
    category: 测试
    description: 用于测试的概念
    
  - concept_id: test_002
    name: 另一个测试概念
    category: 测试
    description: 另一个用于测试的概念
    
metadata:
  version: "1.0"
  last_updated: "2024-01-01"
"""

@pytest.fixture
def mock_file_system():
    """模拟文件系统"""
    mock_fs = Mock()
    mock_fs.read_file = Mock(return_value="")
    mock_fs.write_file = Mock(return_value=True)
    mock_fs.exists = Mock(return_value=True)
    mock_fs.mkdir = Mock(return_value=True)
    return mock_fs

@pytest.fixture
def mock_http_client():
    """模拟HTTP客户端"""
    mock_client = Mock()
    mock_client.get = Mock(return_value=Mock(
        status_code=200,
        json=Mock(return_value={"success": True}),
        text="<html>Test</html>"
    ))
    mock_client.post = Mock(return_value=Mock(
        status_code=201,
        json=Mock(return_value={"id": "123"})
    ))
    return mock_client

@pytest.fixture(scope="session")
def test_output_dir():
    """测试输出目录"""
    output_dir = PROJECT_ROOT / 'tests' / 'output'
    output_dir.mkdir(exist_ok=True)
    return output_dir

@pytest.fixture(autouse=True)
def reset_mocks():
    """每个测试后重置mock"""
    yield
    # 清理工作

# 钩子函数

def pytest_configure(config):
    """配置pytest"""
    config.addinivalue_line("markers", "slow: marks tests as slow")
    config.addinivalue_line("markers", "integration: marks tests as integration tests")

def pytest_collection_modifyitems(config, items):
    """修改测试项"""
    # 自动添加标记
    for item in items:
        if "integration" in item.nodeid:
            item.add_marker(pytest.mark.integration)
        if "unit" in item.nodeid:
            item.add_marker(pytest.mark.unit)

def pytest_runtest_setup(item):
    """测试设置"""
    # 检查是否需要跳过
    if "slow" in item.keywords and not item.config.getoption("--run-slow"):
        pytest.skip("need --run-slow option to run")

# 自定义命令行选项
def pytest_addoption(parser):
    """添加命令行选项"""
    parser.addoption(
        "--run-slow", action="store_true", default=False, help="run slow tests"
    )
    parser.addoption(
        "--run-integration", action="store_true", default=False, help="run integration tests"
    )
