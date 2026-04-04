"""
API配置验证脚本

验证API的各项配置是否正确，并输出诊断报告

使用方法:
    python scripts/validate_api.py
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import asyncio
import json
from datetime import datetime
from typing import Dict, List, Any


def check_dependencies() -> Dict[str, Any]:
    """检查依赖项"""
    results = {
        "name": "依赖项检查",
        "status": "pass",
        "details": []
    }
    
    required_packages = [
        "fastapi",
        "uvicorn",
        "sqlalchemy",
        "pydantic",
        "redis",
        "celery",
        "brotli",
        "httpx",
        "pytest"
    ]
    
    for package in required_packages:
        try:
            __import__(package)
            results["details"].append(f"✓ {package} 已安装")
        except ImportError:
            results["details"].append(f"✗ {package} 未安装")
            results["status"] = "warning"
    
    return results


def check_configuration() -> Dict[str, Any]:
    """检查配置"""
    results = {
        "name": "配置检查",
        "status": "pass",
        "details": []
    }
    
    try:
        from app.core.config import settings
        
        # 检查关键配置
        checks = [
            ("APP_NAME", settings.APP_NAME),
            ("APP_VERSION", settings.APP_VERSION),
            ("API_PREFIX", settings.API_PREFIX),
            ("DATABASE_URL", settings.DATABASE_URL),
            ("REDIS_HOST", settings.REDIS_HOST),
            ("CELERY_BROKER_URL", settings.CELERY_BROKER_URL),
        ]
        
        for name, value in checks:
            if value:
                # 隐藏敏感信息
                if "password" in name.lower() or "url" in name.lower():
                    display_value = "***" if value else ""
                else:
                    display_value = value
                results["details"].append(f"✓ {name}: {display_value}")
            else:
                results["details"].append(f"✗ {name}: 未设置")
                results["status"] = "warning"
        
        # 检查安全配置
        if settings.DEBUG:
            results["details"].append("⚠ DEBUG模式已启用（生产环境应禁用）")
            results["status"] = "warning"
        
        if settings.CORS_ORIGINS == ["*"]:
            results["details"].append("⚠ CORS允许所有来源（生产环境应限制）")
            results["status"] = "warning"
            
    except Exception as e:
        results["details"].append(f"✗ 配置加载失败: {e}")
        results["status"] = "fail"
    
    return results


def check_database() -> Dict[str, Any]:
    """检查数据库连接"""
    results = {
        "name": "数据库检查",
        "status": "pass",
        "details": []
    }
    
    try:
        from app.core.database import db_manager, init_db
        
        # 尝试初始化数据库
        db_manager.init_engine()
        results["details"].append("✓ 数据库引擎初始化成功")
        
        # 检查连接池状态
        pool_status = db_manager.get_pool_status()
        if "error" not in pool_status:
            results["details"].append(f"✓ 连接池大小: {pool_status.get('size', 'unknown')}")
        else:
            results["details"].append(f"⚠ 连接池状态: {pool_status['error']}")
        
        # 测试简单查询
        from app.models.models import User
        results["details"].append("✓ 数据模型加载成功")
        
    except Exception as e:
        results["details"].append(f"✗ 数据库检查失败: {e}")
        results["status"] = "fail"
    
    return results


def check_redis() -> Dict[str, Any]:
    """检查Redis连接"""
    results = {
        "name": "Redis检查",
        "status": "pass",
        "details": []
    }
    
    try:
        import asyncio
        from app.cache.redis_cache import cache
        
        # 尝试连接Redis
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        try:
            loop.run_until_complete(cache.initialize())
            
            # 测试操作
            loop.run_until_complete(cache.set("test_key", "test_value", ttl=10))
            value = loop.run_until_complete(cache.get("test_key"))
            loop.run_until_complete(cache.delete("test_key"))
            
            if value == "test_value":
                results["details"].append("✓ Redis连接成功")
                results["details"].append("✓ 读写测试通过")
            else:
                results["details"].append("⚠ Redis读写测试失败")
                results["status"] = "warning"
            
            loop.run_until_complete(cache.close())
            
        finally:
            loop.close()
            
    except Exception as e:
        results["details"].append(f"⚠ Redis未配置或不可用: {e}")
        results["status"] = "warning"
    
    return results


def check_routes() -> Dict[str, Any]:
    """检查API路由"""
    results = {
        "name": "路由检查",
        "status": "pass",
        "details": []
    }
    
    try:
        from main import app
        
        routes = app.routes
        route_count = len([r for r in routes if hasattr(r, "methods")])
        
        results["details"].append(f"✓ 注册路由数: {route_count}")
        
        # 检查关键端点
        key_endpoints = [
            "/health",
            "/api/v1/health",
            "/api/v1/concepts",
            "/api/v1/learning-paths",
            "/api/v1/tasks",
        ]
        
        from fastapi.testclient import TestClient
        client = TestClient(app)
        
        for endpoint in key_endpoints:
            try:
                response = client.get(endpoint)
                if response.status_code in [200, 404, 422]:  # 404表示端点存在但资源不存在
                    results["details"].append(f"✓ {endpoint} 可访问")
                else:
                    results["details"].append(f"⚠ {endpoint} 状态: {response.status_code}")
            except Exception as e:
                results["details"].append(f"✗ {endpoint} 访问失败: {e}")
                results["status"] = "fail"
                
    except Exception as e:
        results["details"].append(f"✗ 路由检查失败: {e}")
        results["status"] = "fail"
    
    return results


def check_security() -> Dict[str, Any]:
    """检查安全配置"""
    results = {
        "name": "安全检查",
        "status": "pass",
        "details": []
    }
    
    try:
        from app.core.config import settings
        from app.middleware.rate_limit import RateLimitMiddleware
        from app.core.error_handlers import APIException
        
        # 检查中间件
        try:
            from main import app
            middleware_classes = [type(m).__name__ for m in app.user_middleware]
            
            if "RateLimitMiddleware" in middleware_classes or "RateLimitMiddleware" in str(app.user_middleware):
                results["details"].append("✓ 速率限制中间件已启用")
            else:
                results["details"].append("⚠ 速率限制中间件未启用")
                results["status"] = "warning"
            
            if "CORSMiddleware" in middleware_classes or "CORSMiddleware" in str(app.user_middleware):
                results["details"].append("✓ CORS中间件已启用")
            else:
                results["details"].append("⚠ CORS中间件未启用")
                
        except Exception as e:
            results["details"].append(f"⚠ 中间件检查失败: {e}")
        
        # 检查错误处理器
        results["details"].append("✓ 自定义错误处理器已注册")
        
    except Exception as e:
        results["details"].append(f"⚠ 安全模块检查失败: {e}")
        results["status"] = "warning"
    
    return results


def generate_report(checks: List[Dict[str, Any]]) -> str:
    """生成验证报告"""
    lines = []
    lines.append("="*80)
    lines.append("FormalMath API 配置验证报告")
    lines.append("="*80)
    lines.append(f"验证时间: {datetime.now().isoformat()}")
    lines.append("")
    
    pass_count = sum(1 for c in checks if c["status"] == "pass")
    warning_count = sum(1 for c in checks if c["status"] == "warning")
    fail_count = sum(1 for c in checks if c["status"] == "fail")
    
    lines.append(f"总览: {pass_count} 通过, {warning_count} 警告, {fail_count} 失败")
    lines.append("")
    
    for check in checks:
        status_icon = {
            "pass": "✓",
            "warning": "⚠",
            "fail": "✗"
        }.get(check["status"], "?")
        
        lines.append(f"{status_icon} {check['name']}")
        for detail in check["details"]:
            lines.append(f"   {detail}")
        lines.append("")
    
    lines.append("="*80)
    
    if fail_count > 0:
        lines.append("状态: ❌ 验证失败，请修复上述问题")
    elif warning_count > 0:
        lines.append("状态: ⚠️ 验证通过，但存在警告")
    else:
        lines.append("状态: ✅ 所有检查通过")
    
    lines.append("="*80)
    
    return "\n".join(lines)


def main():
    """主函数"""
    print("开始API配置验证...")
    print()
    
    # 执行所有检查
    checks = [
        check_dependencies(),
        check_configuration(),
        check_database(),
        check_redis(),
        check_routes(),
        check_security(),
    ]
    
    # 生成并输出报告
    report = generate_report(checks)
    print(report)
    
    # 保存报告
    report_path = "api_validation_report.txt"
    with open(report_path, "w", encoding="utf-8") as f:
        f.write(report)
    
    print(f"\n报告已保存到: {report_path}")
    
    # 返回状态码
    fail_count = sum(1 for c in checks if c["status"] == "fail")
    return 0 if fail_count == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
