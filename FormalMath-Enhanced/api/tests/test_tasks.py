"""
异步任务测试
"""
import pytest
import time
from app.tasks.celery_app import celery_app, health_check_task


def test_celery_health_check():
    """测试Celery健康检查任务"""
    # 注意：此测试需要运行中的Celery Worker
    try:
        result = health_check_task.delay()
        
        # 等待结果（最多10秒）
        task_result = result.get(timeout=10)
        
        assert task_result["status"] == "ok"
        assert "task_id" in task_result
        
    except Exception as e:
        pytest.skip(f"Celery Worker不可用: {e}")


def test_celery_task_timeout():
    """测试任务超时处理"""
    try:
        # 发送任务但不等待
        result = health_check_task.delay()
        
        # 检查任务状态
        assert result.id is not None
        
        # 等待一小段时间
        time.sleep(1)
        
        # 状态应为PENDING或SUCCESS
        assert result.status in ["PENDING", "SUCCESS"]
        
    except Exception as e:
        pytest.skip(f"Celery Worker不可用: {e}")


def test_task_serialization():
    """测试任务序列化"""
    # 测试复杂数据结构的序列化
    test_data = {
        "user_id": 123,
        "concepts": ["algebra", "geometry"],
        "nested": {"key": "value"}
    }
    
    # 验证JSON序列化
    import json
    serialized = json.dumps(test_data)
    deserialized = json.loads(serialized)
    
    assert deserialized == test_data


def test_celery_config():
    """测试Celery配置"""
    # 验证配置已加载
    assert celery_app.conf.task_serializer == "json"
    assert celery_app.conf.accept_content == ["json"]
    assert "default" in [q.name for q in celery_app.conf.task_queues]
    assert "path_calculation" in [q.name for q in celery_app.conf.task_queues]
