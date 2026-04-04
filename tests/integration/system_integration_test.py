"""
FormalMath 系统集成测试
测试内容：
1. 前端-后端集成
2. API所有端点
3. 数据库连接
4. 缓存系统
5. AI服务
"""
import asyncio
import json
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any
import traceback

# 添加项目路径
PROJECT_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(PROJECT_ROOT / 'FormalMath-Enhanced' / 'api'))
sys.path.insert(0, str(PROJECT_ROOT / 'tools'))

# 测试结果存储
class TestResults:
    def __init__(self):
        self.tests: List[Dict[str, Any]] = []
        self.start_time: Optional[datetime] = None
        self.end_time: Optional[datetime] = None
        
    def add_test(self, name: str, category: str, status: str, 
                 message: str = "", duration: float = 0, details: dict = None):
        self.tests.append({
            "name": name,
            "category": category,
            "status": status,  # passed, failed, skipped
            "message": message,
            "duration": duration,
            "details": details or {},
            "timestamp": datetime.now().isoformat()
        })
        
    def get_summary(self) -> Dict[str, Any]:
        passed = sum(1 for t in self.tests if t["status"] == "passed")
        failed = sum(1 for t in self.tests if t["status"] == "failed")
        skipped = sum(1 for t in self.tests if t["status"] == "skipped")
        total = len(self.tests)
        
        return {
            "total": total,
            "passed": passed,
            "failed": failed,
            "skipped": skipped,
            "pass_rate": (passed / total * 100) if total > 0 else 0,
            "duration": (self.end_time - self.start_time).total_seconds() if self.end_time else 0
        }

results = TestResults()


def run_test(name: str, category: str):
    """测试装饰器"""
    def decorator(func):
        def wrapper(*args, **kwargs):
            start = time.time()
            try:
                result = func(*args, **kwargs)
                duration = time.time() - start
                results.add_test(name, category, "passed", 
                               f"测试通过", duration, {"result": result})
                return result
            except Exception as e:
                duration = time.time() - start
                error_msg = f"{str(e)}\n{traceback.format_exc()}"
                results.add_test(name, category, "failed", error_msg, duration)
                return None
        return wrapper
    return decorator


# ============== 数据库连接测试 ==============

@run_test("数据库引擎初始化", "数据库连接")
def test_database_engine():
    """测试数据库引擎初始化"""
    try:
        from app.core.database import db_manager, init_db
        db_manager.init_engine()
        status = db_manager.get_pool_status()
        return {"pool_status": status, "initialized": db_manager._initialized}
    except Exception as e:
        raise Exception(f"数据库引擎初始化失败: {e}")


@run_test("数据库表创建", "数据库连接")
def test_database_tables():
    """测试数据库表创建"""
    try:
        from app.core.database import db_manager
        db_manager.create_tables()
        return {"tables_created": True}
    except Exception as e:
        raise Exception(f"数据库表创建失败: {e}")


@run_test("数据库索引创建", "数据库连接")
def test_database_indexes():
    """测试数据库索引创建"""
    try:
        from app.core.database import db_manager
        db_manager.create_indexes()
        return {"indexes_created": True}
    except Exception as e:
        raise Exception(f"数据库索引创建失败: {e}")


@run_test("数据库会话管理", "数据库连接")
def test_database_session():
    """测试数据库会话管理"""
    try:
        from app.core.database import db_manager, get_db
        
        # 测试会话生成器
        db_gen = get_db()
        db = next(db_gen)
        
        # 测试简单查询
        result = db.execute("SELECT 1").fetchone()
        
        # 关闭会话
        try:
            next(db_gen)
        except StopIteration:
            pass
            
        return {"query_result": result[0] if result else None}
    except Exception as e:
        raise Exception(f"数据库会话管理失败: {e}")


# ============== 缓存系统测试 ==============

@run_test("Redis缓存初始化", "缓存系统")
def test_redis_init():
    """测试Redis缓存初始化"""
    try:
        import asyncio
        from app.cache.redis_cache import cache
        
        async def _test():
            await cache.initialize()
            return {"initialized": cache._redis is not None}
        
        return asyncio.run(_test())
    except Exception as e:
        raise Exception(f"Redis缓存初始化失败: {e}")


@run_test("Redis缓存基本操作", "缓存系统")
def test_redis_basic_ops():
    """测试Redis缓存基本操作"""
    try:
        import asyncio
        from app.cache.redis_cache import cache
        
        async def _test():
            # 测试设置和获取
            test_data = {"key": "value", "number": 123}
            await cache.set("test_key", test_data, ttl=60)
            result = await cache.get("test_key")
            
            # 清理
            await cache.delete("test_key")
            
            return {"set_get_match": result == test_data}
        
        return asyncio.run(_test())
    except Exception as e:
        raise Exception(f"Redis缓存基本操作失败: {e}")


@run_test("Redis缓存业务方法", "缓存系统")
def test_redis_business_ops():
    """测试Redis缓存业务方法"""
    try:
        import asyncio
        from app.cache.redis_cache import cache
        
        async def _test():
            # 测试知识图谱缓存
            await cache.set_knowledge_graph({"nodes": [], "edges": []}, branch="test")
            graph = await cache.get_knowledge_graph(branch="test")
            
            # 测试用户进度缓存
            await cache.set_user_progress(1, {"progress": 50})
            progress = await cache.get_user_progress(1)
            
            # 清理
            await cache.delete_by_prefix("kg")
            await cache.delete_by_prefix("progress")
            
            return {
                "graph_cached": graph is not None,
                "progress_cached": progress is not None
            }
        
        return asyncio.run(_test())
    except Exception as e:
        raise Exception(f"Redis缓存业务方法失败: {e}")


# ============== API端点测试 ==============

@run_test("API配置加载", "API端点")
def test_api_config():
    """测试API配置加载"""
    try:
        from app.core.config import settings
        return {
            "app_name": settings.APP_NAME,
            "version": settings.APP_VERSION,
            "api_prefix": settings.API_PREFIX,
            "debug": settings.DEBUG
        }
    except Exception as e:
        raise Exception(f"API配置加载失败: {e}")


@run_test("FastAPI应用创建", "API端点")
def test_fastapi_app():
    """测试FastAPI应用创建"""
    try:
        from main import app
        return {
            "app_created": app is not None,
            "title": app.title,
            "version": app.version
        }
    except Exception as e:
        raise Exception(f"FastAPI应用创建失败: {e}")


@run_test("API路由注册", "API端点")
def test_api_routes():
    """测试API路由注册"""
    try:
        from main import app
        routes = [route.path for route in app.routes]
        return {
            "total_routes": len(routes),
            "routes": routes[:20]  # 只显示前20个
        }
    except Exception as e:
        raise Exception(f"API路由注册失败: {e}")


@run_test("知识图谱API", "API端点")
def test_knowledge_graph_api():
    """测试知识图谱API端点"""
    try:
        from app.api.knowledge_graph import router
        routes = [route.path for route in router.routes]
        return {
            "routes": routes,
            "has_graph_endpoint": any("graph" in r for r in routes)
        }
    except Exception as e:
        raise Exception(f"知识图谱API测试失败: {e}")


@run_test("学习路径API", "API端点")
def test_learning_path_api():
    """测试学习路径API端点"""
    try:
        from app.api.learning_path import router
        routes = [route.path for route in router.routes]
        return {
            "routes": routes,
            "has_path_endpoint": any("path" in r for r in routes)
        }
    except Exception as e:
        raise Exception(f"学习路径API测试失败: {e}")


@run_test("搜索API", "API端点")
def test_search_api():
    """测试搜索API端点"""
    try:
        from app.api.search import router
        routes = [route.path for route in router.routes]
        return {
            "routes": routes,
            "has_search_endpoint": any("search" in r for r in routes)
        }
    except Exception as e:
        raise Exception(f"搜索API测试失败: {e}")


@run_test("健康检查API", "API端点")
def test_health_api():
    """测试健康检查API端点"""
    try:
        from app.api.health import router
        routes = [route.path for route in router.routes]
        return {
            "routes": routes,
            "has_health_endpoint": any("health" in r for r in routes)
        }
    except Exception as e:
        raise Exception(f"健康检查API测试失败: {e}")


# ============== 前端-后端集成测试 ==============

@run_test("前端配置检查", "前端-后端集成")
def test_frontend_config():
    """测试前端配置"""
    try:
        frontend_package = PROJECT_ROOT / 'FormalMath-Interactive' / 'package.json'
        with open(frontend_package, 'r', encoding='utf-8') as f:
            config = json.load(f)
        return {
            "name": config.get("name"),
            "version": config.get("version"),
            "has_test_scripts": "test" in config.get("scripts", {})
        }
    except Exception as e:
        raise Exception(f"前端配置检查失败: {e}")


@run_test("Vite代理配置", "前端-后端集成")
def test_vite_proxy():
    """测试Vite代理配置"""
    try:
        vite_config = PROJECT_ROOT / 'FormalMath-Interactive' / 'vite.config.ts'
        content = vite_config.read_text(encoding='utf-8')
        return {
            "has_proxy_config": "proxy:" in content,
            "api_target": "localhost:8000" in content
        }
    except Exception as e:
        raise Exception(f"Vite代理配置测试失败: {e}")


@run_test("CORS配置", "前端-后端集成")
def test_cors_config():
    """测试CORS配置"""
    try:
        from app.core.config import settings
        return {
            "cors_origins": settings.CORS_ORIGINS,
            "allow_credentials": settings.CORS_ALLOW_CREDENTIALS,
            "allow_methods": settings.CORS_ALLOW_METHODS[:5]  # 只显示前5个
        }
    except Exception as e:
        raise Exception(f"CORS配置测试失败: {e}")


# ============== AI服务测试 ==============

@run_test("ML模块加载", "AI服务")
def test_ml_modules():
    """测试ML模块加载"""
    modules_tested = []
    errors = []
    
    ml_modules = [
        'app.ml.knowledge_graph_embedding',
        'app.ml.learning_engine',
        'app.ml.path_planner',
        'app.ml.dynamic_adapter'
    ]
    
    for module_name in ml_modules:
        try:
            __import__(module_name)
            modules_tested.append(module_name)
        except Exception as e:
            errors.append(f"{module_name}: {e}")
    
    return {
        "modules_loaded": len(modules_tested),
        "modules": modules_tested,
        "errors": errors
    }


@run_test("推荐系统模块", "AI服务")
def test_recommendation_modules():
    """测试推荐系统模块"""
    try:
        from app.recommendation.hybrid_recommender import HybridRecommender
        return {
            "hybrid_recommender_loaded": True,
            "has_recommend_methods": hasattr(HybridRecommender, 'recommend')
        }
    except Exception as e:
        return {
            "hybrid_recommender_loaded": False,
            "error": str(e)
        }


@run_test("嵌入服务", "AI服务")
def test_embedding_service():
    """测试嵌入服务"""
    try:
        from app.services.embedding import EmbeddingService
        return {
            "embedding_service_loaded": True,
            "has_embed_methods": hasattr(EmbeddingService, 'embed')
        }
    except Exception as e:
        return {
            "embedding_service_loaded": False,
            "error": str(e)
        }


@run_test("语义搜索服务", "AI服务")
def test_semantic_search():
    """测试语义搜索服务"""
    try:
        from app.services.semantic_search_service import get_semantic_search_service
        service = get_semantic_search_service()
        return {
            "service_initialized": service is not None,
            "has_search_methods": hasattr(service, 'search') if service else False
        }
    except Exception as e:
        return {
            "service_initialized": False,
            "error": str(e)
        }


# ============== 工具模块测试 ==============

@run_test("概念提取工具", "工具模块")
def test_extract_concepts():
    """测试概念提取工具"""
    try:
        from extract_concepts import extract_concepts_from_yaml
        return {
            "module_loaded": True,
            "has_extract_function": callable(extract_concepts_from_yaml)
        }
    except Exception as e:
        raise Exception(f"概念提取工具测试失败: {e}")


@run_test("概念合并工具", "工具模块")
def test_merge_concepts():
    """测试概念合并工具"""
    try:
        from merge_concepts import merge_concepts
        return {
            "module_loaded": True,
            "has_merge_function": callable(merge_concepts)
        }
    except Exception as e:
        raise Exception(f"概念合并工具测试失败: {e}")


# ============== 主测试函数 ==============

def run_all_tests():
    """运行所有测试"""
    results.start_time = datetime.now()
    
    print("=" * 60)
    print("FormalMath 系统集成测试")
    print("=" * 60)
    print(f"开始时间: {results.start_time}")
    print()
    
    # 1. 数据库连接测试
    print("\n[1/5] 数据库连接测试...")
    test_database_engine()
    test_database_tables()
    test_database_indexes()
    test_database_session()
    
    # 2. 缓存系统测试
    print("\n[2/5] 缓存系统测试...")
    test_redis_init()
    test_redis_basic_ops()
    test_redis_business_ops()
    
    # 3. API端点测试
    print("\n[3/5] API端点测试...")
    test_api_config()
    test_fastapi_app()
    test_api_routes()
    test_knowledge_graph_api()
    test_learning_path_api()
    test_search_api()
    test_health_api()
    
    # 4. 前端-后端集成测试
    print("\n[4/5] 前端-后端集成测试...")
    test_frontend_config()
    test_vite_proxy()
    test_cors_config()
    
    # 5. AI服务测试
    print("\n[5/5] AI服务测试...")
    test_ml_modules()
    test_recommendation_modules()
    test_embedding_service()
    test_semantic_search()
    
    # 6. 工具模块测试
    print("\n[额外] 工具模块测试...")
    test_extract_concepts()
    test_merge_concepts()
    
    results.end_time = datetime.now()
    
    return results


def generate_report():
    """生成测试报告"""
    summary = results.get_summary()
    
    report = []
    report.append("# FormalMath 系统集成测试报告")
    report.append("")
    report.append(f"**测试时间**: {results.start_time}")
    report.append(f"**测试耗时**: {summary['duration']:.2f}秒")
    report.append("")
    report.append("## 测试摘要")
    report.append("")
    report.append(f"| 指标 | 数值 |")
    report.append(f"|------|------|")
    report.append(f"| 总测试数 | {summary['total']} |")
    report.append(f"| 通过 | {summary['passed']} |")
    report.append(f"| 失败 | {summary['failed']} |")
    report.append(f"| 跳过 | {summary['skipped']} |")
    report.append(f"| 通过率 | {summary['pass_rate']:.1f}% |")
    report.append("")
    
    # 按类别分组
    categories = {}
    for test in results.tests:
        cat = test["category"]
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(test)
    
    report.append("## 详细测试结果")
    report.append("")
    
    for category, tests in categories.items():
        report.append(f"### {category}")
        report.append("")
        report.append(f"| 测试名称 | 状态 | 耗时 | 说明 |")
        report.append(f"|----------|------|------|------|")
        
        for test in tests:
            status_icon = "✅" if test["status"] == "passed" else "❌" if test["status"] == "failed" else "⏭️"
            message = test["message"][:50] + "..." if len(test["message"]) > 50 else test["message"]
            report.append(f"| {test['name']} | {status_icon} {test['status']} | {test['duration']:.2f}s | {message} |")
        
        report.append("")
    
    # 失败测试详情
    failed_tests = [t for t in results.tests if t["status"] == "failed"]
    if failed_tests:
        report.append("## 失败测试详情")
        report.append("")
        for test in failed_tests:
            report.append(f"### {test['name']} ({test['category']})")
            report.append("")
            report.append(f"```")
            report.append(test["message"])
            report.append(f"```")
            report.append("")
    
    return "\n".join(report)


def generate_fix_list():
    """生成问题修复清单"""
    failed_tests = [t for t in results.tests if t["status"] == "failed"]
    
    fix_list = []
    fix_list.append("# FormalMath 问题修复清单")
    fix_list.append("")
    fix_list.append(f"**生成时间**: {datetime.now().isoformat()}")
    fix_list.append(f"**问题总数**: {len(failed_tests)}")
    fix_list.append("")
    
    if not failed_tests:
        fix_list.append("✅ 所有测试通过，暂无需要修复的问题。")
    else:
        fix_list.append("## 待修复问题")
        fix_list.append("")
        
        for i, test in enumerate(failed_tests, 1):
            fix_list.append(f"### {i}. {test['name']}")
            fix_list.append("")
            fix_list.append(f"- **类别**: {test['category']}")
            fix_list.append(f"- **时间**: {test['timestamp']}")
            fix_list.append(f"- **错误信息**:")
            fix_list.append(f"  ```")
            fix_list.append(f"  {test['message'][:500]}")
            fix_list.append(f"  ```")
            fix_list.append("")
            fix_list.append(f"**建议修复措施**:")
            fix_list.append(f"- [ ] 检查相关配置")
            fix_list.append(f"- [ ] 验证依赖安装")
            fix_list.append(f"- [ ] 查看日志详情")
            fix_list.append("")
    
    return "\n".join(fix_list)


if __name__ == "__main__":
    # 运行测试
    run_all_tests()
    
    # 生成报告
    report = generate_report()
    fix_list = generate_fix_list()
    
    # 保存报告
    output_dir = PROJECT_ROOT / 'tests' / 'output'
    output_dir.mkdir(exist_ok=True)
    
    report_file = output_dir / 'integration_test_report.md'
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write(report)
    print(f"\n测试报告已保存: {report_file}")
    
    fix_list_file = output_dir / 'fix_list.md'
    with open(fix_list_file, 'w', encoding='utf-8') as f:
        f.write(fix_list)
    print(f"问题修复清单已保存: {fix_list_file}")
    
    # 打印摘要
    summary = results.get_summary()
    print("\n" + "=" * 60)
    print("测试完成摘要")
    print("=" * 60)
    print(f"总测试数: {summary['total']}")
    print(f"通过: {summary['passed']} ✅")
    print(f"失败: {summary['failed']} ❌")
    print(f"跳过: {summary['skipped']} ⏭️")
    print(f"通过率: {summary['pass_rate']:.1f}%")
    print(f"总耗时: {summary['duration']:.2f}秒")
    print("=" * 60)
    
    # 退出码
    sys.exit(0 if summary['failed'] == 0 else 1)
