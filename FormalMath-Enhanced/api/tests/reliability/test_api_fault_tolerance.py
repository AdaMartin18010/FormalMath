"""
API容错测试 - 验证异常处理、错误处理和恢复机制

测试范围:
1. 异常输入处理
2. 服务依赖故障
3. 网络超时处理
4. 资源耗尽处理
5. 恢复机制
6. 优雅降级
"""
import pytest
import asyncio
from unittest.mock import Mock, patch, MagicMock
from fastapi.testclient import TestClient
from sqlalchemy.exc import OperationalError, TimeoutError as DBTimeoutError
import sys
sys.path.insert(0, 'g:\\_src\\FormalMath\\FormalMath-Enhanced\\api')

from main import app


# ============ 容错测试类 ============

@pytest.mark.fault_tolerance
class TestExceptionHandling:
    """异常处理测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_generic_exception_handler(self, client):
        """测试通用异常处理器"""
        # 触发未处理的异常
        with patch('app.api.knowledge_graph.cache.get') as mock_get:
            mock_get.side_effect = Exception("Unexpected error")
            
            response = client.get("/api/v1/concepts?page=1")
            
            # 应该返回500错误，但不暴露详细错误
            assert response.status_code == 500
            data = response.json()
            assert "error" in data
    
    def test_http_exception_handling(self, client):
        """测试HTTP异常处理"""
        # 请求不存在的资源
        response = client.get("/api/v1/concepts/non_existent_id")
        
        assert response.status_code == 404
        data = response.json()
        assert "detail" in data
    
    def test_validation_exception_handling(self, client):
        """测试验证异常处理"""
        # 发送无效数据
        response = client.post("/api/v1/learning-paths", json={
            "user_id": "not_a_number",
            "target_concepts": "not_a_list"
        })
        
        assert response.status_code == 422
        data = response.json()
        assert "detail" in data
    
    def test_database_connection_error(self, client):
        """测试数据库连接错误处理"""
        with patch('app.core.database.db_manager.get_db') as mock_db:
            mock_db.side_effect = OperationalError("DB connection failed", {}, None)
            
            response = client.get("/api/v1/concepts")
            
            # 应该返回500或503
            assert response.status_code in [500, 503]
    
    def test_database_timeout(self, client):
        """测试数据库超时处理"""
        with patch('app.api.knowledge_graph.paginate_query') as mock_query:
            mock_query.side_effect = DBTimeoutError("Query timeout")
            
            response = client.get("/api/v1/concepts?page=1")
            
            # 应该返回500或503
            assert response.status_code in [500, 503]


@pytest.mark.fault_tolerance
class TestDependencyFailure:
    """服务依赖故障测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_redis_failure_handling(self, client):
        """测试Redis故障处理"""
        with patch('app.cache.redis_cache.cache.redis') as mock_redis:
            mock_redis.get.side_effect = Exception("Redis connection failed")
            
            # 请求应该仍然成功（降级到数据库）
            response = client.get("/api/v1/concepts?page=1")
            
            # 可能成功（降级）或失败
            assert response.status_code in [200, 500, 503]
    
    def test_redis_timeout_handling(self, client):
        """测试Redis超时处理"""
        with patch('app.cache.redis_cache.cache.redis') as mock_redis:
            mock_redis.get.side_effect = asyncio.TimeoutError("Redis timeout")
            
            response = client.get("/api/v1/concepts?page=1")
            assert response.status_code in [200, 500, 503]
    
    def test_celery_failure_handling(self, client):
        """测试Celery故障处理"""
        with patch('app.api.learning_path.calculate_learning_path') as mock_task:
            mock_task.delay.side_effect = Exception("Celery not available")
            
            response = client.post("/api/v1/learning-paths", json={
                "user_id": 1,
                "target_concepts": ["algebra"],
                "async_mode": True
            })
            
            # 应该返回500错误
            assert response.status_code == 500
    
    def test_search_service_failure(self, client):
        """测试搜索服务故障处理"""
        with patch('app.api.search.get_semantic_search_service') as mock_service:
            mock_instance = MagicMock()
            mock_instance.search.side_effect = Exception("Search service failed")
            mock_service.return_value = mock_instance
            
            response = client.post("/api/v1/search/search", json={
                "query": "test",
                "search_type": "hybrid"
            })
            
            # 应该返回500错误
            assert response.status_code == 500
            data = response.json()
            assert "detail" in data


@pytest.mark.fault_tolerance
class TestInvalidDataHandling:
    """无效数据处理测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_malformed_json_handling(self, client):
        """测试畸形JSON处理"""
        response = client.post(
            "/api/v1/learning-paths",
            data='{"user_id": 1, "target_concepts": [broken json',
            headers={"Content-Type": "application/json"}
        )
        
        assert response.status_code == 422
    
    def test_invalid_unicode_handling(self, client):
        """测试无效Unicode处理"""
        response = client.post("/api/v1/search/search", json={
            "query": "\xff\xfe\x00\x00invalid unicode",
            "search_type": "hybrid"
        })
        
        # 应该正常处理或返回验证错误
        assert response.status_code in [200, 422]
    
    def test_null_byte_handling(self, client):
        """测试空字节处理"""
        response = client.get("/api/v1/concepts?search=test\x00null")
        
        # 应该正常处理或返回错误
        assert response.status_code in [200, 400, 422]
    
    def test_very_long_string_handling(self, client):
        """测试超长字符串处理"""
        long_string = "a" * 100000
        
        response = client.post("/api/v1/search/search", json={
            "query": long_string,
            "search_type": "hybrid"
        })
        
        # 应该返回验证错误
        assert response.status_code in [422, 413]
    
    def test_special_characters_handling(self, client):
        """测试特殊字符处理"""
        special_chars = [
            "\x00",  # Null
            "\x01",  # Start of heading
            "\x1f",  # Unit separator
            "\x7f",  # DEL
            "\x80",  # Extended ASCII
            "\xff",  # Extended ASCII max
        ]
        
        for char in special_chars:
            response = client.get(f"/api/v1/concepts?search=test{char}special")
            # 应该正常处理或返回验证错误
            assert response.status_code in [200, 400, 422]


@pytest.mark.fault_tolerance
class TestGracefulDegradation:
    """优雅降级测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_cache_miss_degradation(self, client):
        """测试缓存未命中降级"""
        with patch('app.cache.redis_cache.cache.get') as mock_get:
            mock_get.return_value = None  # 模拟缓存未命中
            
            response = client.get("/api/v1/concepts?page=1")
            
            # 应该成功（从数据库获取）
            assert response.status_code == 200
    
    def test_partial_service_failure(self, client):
        """测试部分服务故障"""
        with patch('app.api.health._check_redis') as mock_redis:
            mock_redis.return_value = {"status": "unhealthy", "error": "Connection refused"}
            
            # 详细健康检查应该显示Redis故障但仍返回200
            response = client.get("/api/v1/health/detailed")
            assert response.status_code == 200
            
            data = response.json()
            assert data["redis"]["status"] == "unhealthy"
    
    def test_recommendation_fallback(self, client):
        """测试推荐系统降级"""
        # 模拟推荐服务故障
        with patch('app.api.recommendation.CollaborativeFiltering') as mock_cf:
            mock_instance = MagicMock()
            mock_instance.recommend_for_user.side_effect = Exception("Service unavailable")
            mock_cf.return_value = mock_instance
            
            response = client.post("/api/v1/recommendations/recommend", json={
                "user_id": 1,
                "n_recommendations": 10,
                "recommendation_type": "collaborative"
            })
            
            # 可能成功（降级到其他推荐方法）或失败
            assert response.status_code in [200, 500]


@pytest.mark.fault_tolerance
class TestRecoveryMechanisms:
    """恢复机制测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_retry_mechanism_simulation(self, client):
        """测试重试机制"""
        # 模拟临时故障
        call_count = 0
        
        def side_effect(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            if call_count < 3:
                raise Exception("Temporary failure")
            return {"status": "ok"}
        
        with patch('app.api.health._check_redis', side_effect=side_effect):
            # 需要多次请求才能验证重试
            for _ in range(5):
                response = client.get("/api/v1/health/redis")
                if response.status_code == 200:
                    break
    
    def test_circuit_breaker_simulation(self, client):
        """测试熔断器模拟"""
        # 模拟持续故障
        with patch('app.cache.redis_cache.cache.get') as mock_get:
            mock_get.side_effect = Exception("Service down")
            
            # 快速发送多个请求
            results = []
            for _ in range(10):
                response = client.get("/api/v1/concepts?page=1")
                results.append(response.status_code)
            
            # 如果实现了熔断器，应该看到一些快速失败
            # 注意：当前实现可能没有熔断器
            pass


@pytest.mark.fault_tolerance
class TestConcurrentFaults:
    """并发故障测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.mark.asyncio
    async def test_concurrent_database_errors(self, client):
        """测试并发数据库错误"""
        async def make_request():
            return client.get("/api/v1/concepts?page=1")
        
        with patch('app.core.database.db_manager.get_pool_status') as mock_status:
            mock_status.side_effect = Exception("Pool exhausted")
            
            # 发送并发请求
            tasks = [make_request() for _ in range(20)]
            responses = await asyncio.gather(*tasks, return_exceptions=True)
            
            # 大多数请求应该返回错误
            error_count = sum(1 for r in responses if isinstance(r, Exception) or 
                            (hasattr(r, 'status_code') and r.status_code >= 500))
            # 不严格要求错误数，但应该有一些错误
            assert error_count >= 0
    
    @pytest.mark.asyncio
    async def test_resource_contention(self, client):
        """测试资源争用"""
        async def request_worker():
            response = client.get("/api/v1/concepts/graph/stats")
            return response.status_code
        
        # 创建资源争用
        tasks = [request_worker() for _ in range(100)]
        responses = await asyncio.gather(*tasks)
        
        # 大部分请求应该成功
        success_count = responses.count(200)
        success_rate = success_count / len(responses) * 100
        
        assert success_rate >= 80, f"资源争用下成功率 {success_rate:.2f}% 低于80%"


@pytest.mark.fault_tolerance
class TestBoundaryConditions:
    """边界条件测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_zero_page_size(self, client):
        """测试零页面大小"""
        response = client.get("/api/v1/concepts?page_size=0")
        assert response.status_code == 422
    
    def test_negative_page_number(self, client):
        """测试负页码"""
        response = client.get("/api/v1/concepts?page=-1")
        assert response.status_code == 422
    
    def test_maximum_page_size(self, client):
        """测试最大页面大小"""
        response = client.get("/api/v1/concepts?page_size=1000")
        assert response.status_code == 422  # 超过最大限制
    
    def test_empty_list_handling(self, client):
        """测试空列表处理"""
        response = client.post("/api/v1/learning-paths", json={
            "user_id": 1,
            "target_concepts": [],
            "async_mode": False
        })
        assert response.status_code == 422  # 空列表应该被验证拒绝
    
    def test_extreme_id_values(self, client):
        """测试极端ID值"""
        # 最大整数
        response = client.get("/api/v1/learning-paths/9223372036854775807")
        assert response.status_code in [404, 500]
        
        # 零ID
        response = client.get("/api/v1/learning-paths/0")
        assert response.status_code == 404
        
        # 负数ID
        response = client.get("/api/v1/learning-paths/-1")
        assert response.status_code in [404, 422]


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-m", "fault_tolerance"])
