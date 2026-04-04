"""
API安全性测试 - 验证输入验证、权限控制和防护措施

测试范围:
1. 输入验证和净化
2. SQL注入防护
3. XSS防护
4. 请求大小限制
5. 速率限制（如果实现）
6. 认证和授权
7. 敏感数据保护
"""
import pytest
import json
from fastapi.testclient import TestClient
import sys
sys.path.insert(0, 'g:\\_src\\FormalMath\\FormalMath-Enhanced\\api')

from main import app


# ============ 安全测试数据 ============

SQL_INJECTION_PAYLOADS = [
    "' OR '1'='1",
    "'; DROP TABLE users; --",
    "' UNION SELECT * FROM users --",
    "1; DROP TABLE users--",
    "' OR 1=1--",
    "'; DELETE FROM users WHERE '1'='1",
]

XSS_PAYLOADS = [
    "<script>alert('xss')</script>",
    "<img src=x onerror=alert('xss')>",
    "<body onload=alert('xss')>",
    "javascript:alert('xss')",
    "<svg onload=alert('xss')>",
]

PATH_TRAVERSAL_PAYLOADS = [
    "../../../etc/passwd",
    "..\\..\\..\\windows\\system32\\config\\sam",
    "....//....//etc/passwd",
    "%2e%2e%2f%2e%2e%2f%2e%2e%2fetc%2fpasswd",
]

COMMAND_INJECTION_PAYLOADS = [
    "; cat /etc/passwd",
    "| whoami",
    "`ls -la`",
    "$(id)",
]

OVERSIZED_PAYLOADS = {
    "large_string": "x" * 1000000,  # 1MB字符串
    "deep_nesting": {"a": {"b": {"c": {"d": {"e": "f"}}}}},
    "many_keys": {f"key_{i}": f"value_{i}" for i in range(10000)},
}


# ============ 安全测试类 ============

@pytest.mark.security
class TestInputValidation:
    """输入验证测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.mark.parametrize("payload", SQL_INJECTION_PAYLOADS)
    def test_sql_injection_concepts_search(self, client, payload):
        """测试概念搜索SQL注入防护"""
        response = client.get(f"/api/v1/concepts?search={payload}")
        # 应该返回正常响应或验证错误，不应崩溃
        assert response.status_code in [200, 400, 422]
        
        # 响应不应包含SQL错误信息
        if response.status_code != 200:
            response_text = response.text.lower()
            assert "sql" not in response_text or "sqlite" not in response_text, \
                "响应可能泄露SQL错误信息"
    
    @pytest.mark.parametrize("payload", SQL_INJECTION_PAYLOADS)
    def test_sql_injection_concept_id(self, client, payload):
        """测试概念ID SQL注入防护"""
        response = client.get(f"/api/v1/concepts/{payload}")
        # 应该返回404或验证错误
        assert response.status_code in [404, 400, 422]
    
    @pytest.mark.parametrize("payload", XSS_PAYLOADS)
    def test_xss_search_query(self, client, payload):
        """测试搜索查询XSS防护"""
        response = client.post("/api/v1/search/search", json={
            "query": payload,
            "search_type": "hybrid"
        })
        
        # 检查响应是否被正确转义
        if response.status_code == 200:
            response_text = response.text
            # 响应中不应包含未转义的脚本标签
            assert "<script>" not in response_text or "\\u003cscript\\u003e" in response_text, \
                "XSS payload未被转义"
    
    @pytest.mark.parametrize("payload", XSS_PAYLOADS)
    def test_xss_index_document(self, client, payload):
        """测试文档索引XSS防护"""
        response = client.post("/api/v1/search/index", json={
            "doc_id": "test_doc",
            "content": payload,
            "metadata": {"title": payload}
        })
        
        # 请求可能被接受但内容应被净化
        assert response.status_code in [200, 422, 500]
    
    def test_invalid_json_format(self, client):
        """测试无效JSON格式处理"""
        response = client.post(
            "/api/v1/learning-paths",
            data="not valid json {",
            headers={"Content-Type": "application/json"}
        )
        assert response.status_code == 422
    
    def test_missing_content_type(self, client):
        """测试缺少Content-Type头"""
        response = client.post(
            "/api/v1/learning-paths",
            data='{"user_id": 1, "target_concepts": ["test"]}'
        )
        # FastAPI可能会假设它是JSON或返回错误
        assert response.status_code in [200, 422, 415]
    
    def test_invalid_query_parameters(self, client):
        """测试无效查询参数"""
        # 负数页码
        response = client.get("/api/v1/concepts?page=-1")
        assert response.status_code == 422
        
        # 超大页码
        response = client.get("/api/v1/concepts?page=999999999999999999999")
        assert response.status_code in [200, 422]
        
        # 非数字页码
        response = client.get("/api/v1/concepts?page=abc")
        assert response.status_code == 422
    
    def test_oversized_request_body(self, client):
        """测试超大请求体"""
        large_data = {
            "user_id": 1,
            "target_concepts": [OVERSIZED_PAYLOADS["large_string"]]
        }
        
        response = client.post("/api/v1/learning-paths", json=large_data)
        # 应该返回413或处理错误
        assert response.status_code in [413, 422, 500]
    
    def test_deeply_nested_json(self, client):
        """测试深度嵌套JSON"""
        # 创建深度嵌套的结构
        data = {"user_id": 1, "target_concepts": ["test"]}
        for _ in range(100):
            data = {"nested": data}
        
        response = client.post("/api/v1/learning-paths", json=data)
        # 应该正常处理或返回验证错误
        assert response.status_code in [200, 422, 500]


@pytest.mark.security
class TestAuthenticationSecurity:
    """认证安全测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_missing_authentication(self, client):
        """测试缺少认证"""
        # 测试需要认证的端点（如果存在）
        # 当前API可能没有认证机制
        pass
    
    def test_invalid_token_format(self, client):
        """测试无效令牌格式"""
        response = client.get(
            "/api/v1/learning-paths/user/1",
            headers={"Authorization": "InvalidTokenFormat"}
        )
        # 如果没有认证，返回200；如果有认证，应返回401
        assert response.status_code in [200, 401, 403]
    
    def test_expired_token(self, client):
        """测试过期令牌"""
        expired_token = "Bearer eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJleHAiOjEwfQ.invalid"
        response = client.get(
            "/api/v1/learning-paths/user/1",
            headers={"Authorization": expired_token}
        )
        assert response.status_code in [200, 401]


@pytest.mark.security
class TestInjectionAttacks:
    """注入攻击测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    @pytest.mark.parametrize("payload", PATH_TRAVERSAL_PAYLOADS)
    def test_path_traversal_cache_clear(self, client, payload):
        """测试路径遍历攻击防护 - 缓存清除"""
        response = client.post(f"/api/v1/concepts/cache/clear?branch={payload}")
        # 应该正常处理或返回错误，不应访问文件系统
        assert response.status_code in [200, 400, 422]
    
    def test_no_sql_injection(self, client):
        """测试NoSQL注入防护"""
        # 测试MongoDB风格的注入（如果适用）
        malicious_query = {
            "query": "test",
            "filter_metadata": {
                "$where": "this.password == 'admin'"
            }
        }
        
        response = client.post("/api/v1/search/search", json=malicious_query)
        # 应该正常处理或返回验证错误
        assert response.status_code in [200, 422]
    
    def test_ldap_injection(self, client):
        """测试LDAP注入防护"""
        # 如果API使用LDAP认证
        ldap_payload = "*)(uid=*))(&(uid=*"
        response = client.get(f"/api/v1/concepts?search={ldap_payload}")
        assert response.status_code in [200, 400, 422]


@pytest.mark.security
class TestDataExposure:
    """数据泄露测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_error_message_leakage(self, client):
        """测试错误消息泄露"""
        # 触发一个错误
        response = client.get("/api/v1/concepts/../../../etc/passwd")
        
        # 错误消息不应包含敏感信息
        if response.status_code >= 500:
            response_text = response.text.lower()
            sensitive_patterns = [
                "password", "secret", "key", "token",
                "stack trace", "traceback", "file ",
                "/home/", "/var/", "c:\\", "server:",
            ]
            for pattern in sensitive_patterns:
                assert pattern not in response_text, \
                    f"错误响应可能包含敏感信息: {pattern}"
    
    def test_debug_mode_disabled(self, client):
        """测试调试模式是否禁用"""
        response = client.get("/")
        
        if response.status_code == 200:
            data = response.json()
            # 根端点不应在响应中包含debug信息
            # 检查响应头
            assert "x-debug" not in response.headers
    
    def test_headers_security(self, client):
        """测试安全响应头"""
        response = client.get("/")
        
        # 检查基本安全头
        # 注意：FastAPI默认可能不包含所有这些头
        headers = response.headers
        
        # 不应包含可能泄露信息的头
        assert "x-powered-by" not in headers
        assert "server" not in headers or headers["server"] == "uvicorn"
    
    def test_stack_trace_not_exposed(self, client):
        """测试堆栈跟踪不暴露"""
        # 发送无效请求触发错误
        response = client.post(
            "/api/v1/learning-paths",
            data="invalid",
            headers={"Content-Type": "application/json"}
        )
        
        if response.status_code == 422:
            response_text = response.text.lower()
            # 不应包含堆栈跟踪
            assert "traceback" not in response_text
            assert "file \"" not in response_text
            assert "line " not in response_text


@pytest.mark.security
class TestResourceExhaustion:
    """资源耗尽测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_repeated_requests(self, client):
        """测试重复请求处理"""
        # 快速发送多个相同请求
        responses = []
        for _ in range(100):
            response = client.get("/health")
            responses.append(response.status_code)
        
        # 所有请求都应成功
        success_rate = responses.count(200) / len(responses) * 100
        assert success_rate >= 95, f"重复请求成功率 {success_rate:.2f}% 低于95%"
    
    def test_slowloris_protection(self, client):
        """测试Slowloris攻击防护"""
        # 注意：这需要实际的HTTP服务器测试
        # 这里只是简单的连接测试
        import socket
        
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(5)
            sock.connect(("127.0.0.1", 8000))
            # 发送部分请求
            sock.send(b"GET / HTTP/1.1\r\n")
            # 等待，看服务器是否超时
            sock.settimeout(10)
            try:
                data = sock.recv(1024)
                # 如果收到数据，服务器可能在等待
            except socket.timeout:
                pass  # 预期行为：超时关闭
            sock.close()
        except (socket.error, ConnectionRefusedError):
            # 服务器可能未运行
            pass


@pytest.mark.security
class TestCORSConfiguration:
    """CORS配置测试"""
    
    @pytest.fixture
    def client(self):
        """创建测试客户端"""
        with TestClient(app) as c:
            yield c
    
    def test_cors_preflight(self, client):
        """测试CORS预检请求"""
        response = client.options(
            "/api/v1/concepts",
            headers={
                "Origin": "http://example.com",
                "Access-Control-Request-Method": "GET",
                "Access-Control-Request-Headers": "Content-Type",
            }
        )
        
        # 检查CORS头
        assert "access-control-allow-origin" in response.headers
    
    def test_cors_simple_request(self, client):
        """测试CORS简单请求"""
        response = client.get(
            "/api/v1/concepts",
            headers={"Origin": "http://example.com"}
        )
        
        assert "access-control-allow-origin" in response.headers


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-m", "security"])
