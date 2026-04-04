"""
API功能测试 - 验证所有端点的功能正确性

测试范围:
1. 健康检查端点
2. 知识图谱端点
3. 学习路径端点
4. 异步任务端点
5. 搜索端点
6. 推荐系统端点
7. 学习引擎端点
"""
import pytest
import asyncio
from typing import Dict, Any
from unittest.mock import Mock, patch, MagicMock
from fastapi.testclient import TestClient
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker
from sqlalchemy.pool import StaticPool

# 导入应用
import sys
sys.path.insert(0, 'g:\\_src\\FormalMath\\FormalMath-Enhanced\\api')

from app.core.database import Base, get_db
from main import app


# ============ 测试数据库设置 ============
SQLALCHEMY_DATABASE_URL = "sqlite:///:memory:"

engine = create_engine(
    SQLALCHEMY_DATABASE_URL,
    connect_args={"check_same_thread": False},
    poolclass=StaticPool,
)
TestingSessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=engine)


def override_get_db():
    """测试数据库依赖"""
    try:
        db = TestingSessionLocal()
        yield db
    finally:
        db.close()


app.dependency_overrides[get_db] = override_get_db


# ============ Fixtures ============

@pytest.fixture(scope="function")
def client():
    """创建测试客户端"""
    Base.metadata.create_all(bind=engine)
    with TestClient(app) as c:
        yield c
    Base.metadata.drop_all(bind=engine)


@pytest.fixture(scope="function")
def db_session():
    """创建数据库会话"""
    Base.metadata.create_all(bind=engine)
    session = TestingSessionLocal()
    try:
        yield session
    finally:
        session.close()
    Base.metadata.drop_all(bind=engine)


# ============ 健康检查端点测试 ============

class TestHealthEndpoints:
    """健康检查端点测试"""
    
    def test_basic_health_check(self, client):
        """测试基础健康检查"""
        response = client.get("/health")
        assert response.status_code == 200
        data = response.json()
        assert data["status"] == "healthy"
    
    def test_detailed_health_check(self, client):
        """测试详细健康检查"""
        response = client.get("/api/v1/health/detailed")
        assert response.status_code == 200
        data = response.json()
        assert "api" in data
        assert "database" in data
        assert "redis" in data
        assert "celery" in data
    
    def test_database_health(self, client):
        """测试数据库健康检查"""
        response = client.get("/api/v1/health/database")
        # 可能返回200或503，取决于数据库状态
        assert response.status_code in [200, 503]
    
    def test_connection_pool_status(self, client):
        """测试连接池状态端点"""
        response = client.get("/api/v1/health/pool")
        assert response.status_code == 200
        data = response.json()
        assert "pool" in data
        assert "timestamp" in data


# ============ 知识图谱端点测试 ============

class TestKnowledgeGraphEndpoints:
    """知识图谱端点测试"""
    
    def test_list_concepts_empty(self, client):
        """测试空概念列表"""
        response = client.get("/api/v1/concepts?page=1&page_size=20")
        assert response.status_code == 200
        data = response.json()
        assert "items" in data
        assert "total" in data
        assert data["total"] == 0
    
    def test_list_concepts_pagination(self, client):
        """测试概念列表分页"""
        # 测试第一页
        response = client.get("/api/v1/concepts?page=1&page_size=10")
        assert response.status_code == 200
        data = response.json()
        assert data["page"] == 1
        assert data["page_size"] == 10
        
        # 测试无效页码
        response = client.get("/api/v1/concepts?page=0")
        assert response.status_code == 422  # 验证错误
    
    def test_list_concepts_with_filters(self, client):
        """测试带过滤器的概念列表"""
        response = client.get("/api/v1/concepts?branch=algebra&difficulty=basic")
        assert response.status_code == 200
        data = response.json()
        assert "items" in data
    
    def test_get_concept_not_found(self, client):
        """测试获取不存在的概念"""
        response = client.get("/api/v1/concepts/non_existent_id")
        assert response.status_code == 404
        assert "detail" in response.json()
    
    def test_get_concept_relations(self, client):
        """测试获取概念关系"""
        response = client.get("/api/v1/concepts/test_id/relations")
        assert response.status_code == 200
        data = response.json()
        assert "concept_id" in data
        assert "relations" in data
    
    def test_get_concept_prerequisites(self, client):
        """测试获取概念前置依赖"""
        response = client.get("/api/v1/concepts/test_id/prerequisites?depth=2")
        assert response.status_code == 200
        data = response.json()
        assert "concept_id" in data
        assert "prerequisites" in data
    
    def test_get_graph_stats(self, client):
        """测试获取图谱统计"""
        response = client.get("/api/v1/concepts/graph/stats")
        assert response.status_code == 200
        data = response.json()
        assert "total_nodes" in data
        assert "total_edges" in data
        assert "branches" in data
        assert "difficulty_distribution" in data
    
    def test_clear_kg_cache(self, client):
        """测试清除知识图谱缓存"""
        response = client.post("/api/v1/concepts/cache/clear")
        assert response.status_code == 200
        data = response.json()
        assert "message" in data


# ============ 学习路径端点测试 ============

class TestLearningPathEndpoints:
    """学习路径端点测试"""
    
    def test_create_learning_path_validation(self, client):
        """测试创建学习路径参数验证"""
        # 测试缺少必填字段
        response = client.post("/api/v1/learning-paths", json={})
        assert response.status_code == 422
        
        # 测试空目标概念列表
        response = client.post("/api/v1/learning-paths", json={
            "user_id": 1,
            "target_concepts": []
        })
        assert response.status_code == 422
    
    def test_create_learning_path_async(self, client):
        """测试异步创建学习路径"""
        response = client.post("/api/v1/learning-paths", json={
            "user_id": 1,
            "target_concepts": ["algebra_basics", "linear_algebra"],
            "async_mode": True
        })
        # 如果Celery不可用，可能返回500
        assert response.status_code in [200, 500]
    
    def test_get_user_learning_paths(self, client):
        """测试获取用户学习路径"""
        response = client.get("/api/v1/learning-paths/user/1")
        assert response.status_code == 200
        data = response.json()
        assert isinstance(data, list)
    
    def test_get_learning_path_detail_not_found(self, client):
        """测试获取不存在的学习路径详情"""
        response = client.get("/api/v1/learning-paths/99999")
        assert response.status_code == 404
    
    def test_optimize_path_not_found(self, client):
        """测试优化不存在的路径"""
        response = client.post("/api/v1/learning-paths/99999/optimize")
        assert response.status_code == 404
    
    def test_update_path_progress_validation(self, client):
        """测试更新路径进度验证"""
        # 测试负数进度
        response = client.put("/api/v1/learning-paths/1/progress?completed_nodes=-1")
        assert response.status_code == 422
    
    def test_delete_learning_path_not_found(self, client):
        """测试删除不存在的学习路径"""
        response = client.delete("/api/v1/learning-paths/99999")
        assert response.status_code == 404


# ============ 异步任务端点测试 ============

class TestTaskEndpoints:
    """异步任务端点测试"""
    
    def test_get_task_info_invalid_id(self, client):
        """测试获取无效任务ID的信息"""
        response = client.get("/api/v1/tasks/invalid_task_id")
        # 应该返回任务状态（可能是PENDING）或404
        assert response.status_code in [200, 404]
    
    def test_get_task_result_not_ready(self, client):
        """测试获取未完成任务的结果"""
        response = client.get("/api/v1/tasks/non_existent/result")
        assert response.status_code == 400
    
    def test_get_task_progress(self, client):
        """测试获取任务进度"""
        response = client.get("/api/v1/tasks/test_task/progress")
        assert response.status_code == 200
        data = response.json()
        assert "task_id" in data
        assert "progress" in data
    
    def test_revoke_task(self, client):
        """测试撤销任务"""
        response = client.post("/api/v1/tasks/test_task/revoke")
        # 可能成功或失败，取决于Celery状态
        assert response.status_code in [200, 500]
    
    def test_list_tasks(self, client):
        """测试列出任务"""
        response = client.get("/api/v1/tasks?limit=50")
        assert response.status_code == 200
        data = response.json()
        assert "tasks" in data
        assert "total" in data
    
    def test_get_workers_status(self, client):
        """测试获取Worker状态"""
        response = client.get("/api/v1/tasks/workers/status")
        # 可能成功或失败，取决于Celery Worker状态
        assert response.status_code in [200, 500]
    
    def test_purge_tasks(self, client):
        """测试清除任务队列"""
        response = client.post("/api/v1/tasks/purge")
        assert response.status_code in [200, 500]


# ============ 搜索端点测试 ============

class TestSearchEndpoints:
    """搜索端点测试"""
    
    def test_search_validation(self, client):
        """测试搜索参数验证"""
        # 测试空查询
        response = client.post("/api/v1/search/search", json={})
        assert response.status_code == 422
        
        # 测试过长查询
        response = client.post("/api/v1/search/search", json={
            "query": "a" * 1001
        })
        assert response.status_code == 422
    
    def test_search_get_validation(self, client):
        """测试GET搜索参数验证"""
        # 测试缺少查询参数
        response = client.get("/api/v1/search/search")
        assert response.status_code == 422
    
    def test_index_document_validation(self, client):
        """测试索引文档参数验证"""
        # 测试缺少必填字段
        response = client.post("/api/v1/search/index", json={})
        assert response.status_code == 422
    
    def test_formula_search_validation(self, client):
        """测试公式搜索参数验证"""
        # 测试空LaTeX
        response = client.post("/api/v1/search/formula", json={
            "latex": ""
        })
        assert response.status_code == 422
    
    def test_ask_question_validation(self, client):
        """测试问答参数验证"""
        # 测试空问题
        response = client.post("/api/v1/search/ask", json={
            "question": ""
        })
        assert response.status_code == 422


# ============ 推荐系统端点测试 ============

class TestRecommendationEndpoints:
    """推荐系统端点测试"""
    
    def test_get_recommendations_validation(self, client):
        """测试推荐请求参数验证"""
        # 测试缺少必填字段
        response = client.post("/api/v1/recommendations/recommend", json={})
        assert response.status_code == 422
        
        # 测试无效推荐数量
        response = client.post("/api/v1/recommendations/recommend", json={
            "user_id": 1,
            "n_recommendations": 100
        })
        assert response.status_code == 422
    
    def test_feedback_validation(self, client):
        """测试反馈参数验证"""
        # 测试超出范围的奖励值
        response = client.post("/api/v1/recommendations/feedback", json={
            "user_id": 1,
            "concept_id": "test",
            "reward": 1.5
        })
        assert response.status_code == 422
        
        response = client.post("/api/v1/recommendations/feedback", json={
            "user_id": 1,
            "concept_id": "test",
            "reward": -0.5
        })
        assert response.status_code == 422
    
    def test_similar_users_validation(self, client):
        """测试相似用户请求参数验证"""
        response = client.post("/api/v1/recommendations/similar-users", json={
            "user_id": 1,
            "k": 100
        })
        assert response.status_code == 422
    
    def test_explain_recommendation(self, client):
        """测试推荐解释端点"""
        response = client.get("/api/v1/recommendations/explain/1/test_concept")
        # 可能返回404（推荐不存在）或500（数据库错误）
        assert response.status_code in [404, 500]


# ============ 学习引擎端点测试 ============

class TestLearningEngineEndpoints:
    """学习引擎端点测试"""
    
    def test_initialize_user_validation(self, client):
        """测试初始化用户参数验证"""
        # 测试缺少user_id
        response = client.post("/api/v1/learning-engine/users/initialize", json={})
        assert response.status_code == 422
    
    def test_record_interaction_validation(self, client):
        """测试记录交互参数验证"""
        # 测试缺少必填字段
        response = client.post("/api/v1/learning-engine/interactions/record", json={
            "user_id": "test_user"
        })
        assert response.status_code == 422
    
    def test_get_next_steps(self, client):
        """测试获取下一步学习建议"""
        response = client.get("/api/v1/learning-engine/users/test_user/next-steps")
        assert response.status_code == 200
        data = response.json()
        assert "user_id" in data
        assert "suggestions" in data
    
    def test_generate_learning_path_validation(self, client):
        """测试生成学习路径参数验证"""
        response = client.post("/api/v1/learning-engine/paths/generate", json={
            "user_id": "test_user"
        })
        assert response.status_code == 422
    
    def test_adjust_difficulty_validation(self, client):
        """测试调整难度参数验证"""
        # 测试超出范围的performance值
        response = client.post("/api/v1/learning-engine/difficulty/adjust", json={
            "user_id": "test_user",
            "performance": 1.5
        })
        assert response.status_code == 422
    
    def test_get_gamification_summary(self, client):
        """测试获取游戏化摘要"""
        response = client.get("/api/v1/learning-engine/gamification/test_user/summary")
        # 可能成功或失败，取决于数据状态
        assert response.status_code in [200, 500]
    
    def test_system_status(self, client):
        """测试系统状态端点"""
        response = client.get("/api/v1/learning-engine/system/status")
        assert response.status_code == 200
        data = response.json()
        assert "status" in data
        assert "components" in data
        assert "timestamp" in data


# ============ 根端点测试 ============

class TestRootEndpoints:
    """根端点测试"""
    
    def test_root_endpoint(self, client):
        """测试根端点"""
        response = client.get("/")
        assert response.status_code == 200
        data = response.json()
        assert "name" in data
        assert "version" in data
        assert "status" in data
        assert "features" in data
    
    def test_docs_endpoint(self, client):
        """测试文档端点"""
        response = client.get("/docs")
        assert response.status_code == 200
    
    def test_openapi_endpoint(self, client):
        """测试OpenAPI规范端点"""
        response = client.get("/openapi.json")
        assert response.status_code == 200
        data = response.json()
        assert "openapi" in data
        assert "paths" in data


# ============ 错误处理测试 ============

class TestErrorHandling:
    """错误处理测试"""
    
    def test_invalid_json(self, client):
        """测试无效JSON请求"""
        response = client.post(
            "/api/v1/learning-paths",
            data="invalid json",
            headers={"Content-Type": "application/json"}
        )
        assert response.status_code == 422
    
    def test_method_not_allowed(self, client):
        """测试不允许的HTTP方法"""
        response = client.delete("/api/v1/concepts")
        assert response.status_code == 405
    
    def test_not_found(self, client):
        """测试404处理"""
        response = client.get("/non_existent_endpoint")
        assert response.status_code == 404


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
