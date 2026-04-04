#!/usr/bin/env python3
"""
FormalMath API - 数据库初始化脚本
用于生产环境首次部署时初始化数据库
"""
import asyncio
import logging
import sys
from pathlib import Path

# 添加项目路径
sys.path.insert(0, str(Path(__file__).parent.parent))

from app.core.config_production import settings_production as settings
from app.core.database_production import db_manager, init_db

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


async def check_database_connection():
    """检查数据库连接"""
    try:
        db_manager.init_engines()
        health = await db_manager.health_check()
        if health["status"] == "healthy":
            logger.info("✅ 数据库连接正常")
            return True
        else:
            logger.error(f"❌ 数据库连接异常: {health}")
            return False
    except Exception as e:
        logger.error(f"❌ 数据库连接失败: {e}")
        return False


async def init_database():
    """初始化数据库"""
    logger.info("开始初始化数据库...")
    
    # 检查连接
    if not await check_database_connection():
        sys.exit(1)
    
    try:
        # 创建表
        logger.info("创建数据库表...")
        await db_manager.create_tables()
        
        # 创建索引
        logger.info("创建性能索引...")
        await db_manager.create_indexes()
        
        logger.info("✅ 数据库初始化完成")
        
        # 显示连接池状态
        pool_status = await db_manager.get_pool_status()
        logger.info(f"连接池状态: {pool_status}")
        
    except Exception as e:
        logger.error(f"❌ 数据库初始化失败: {e}")
        sys.exit(1)
    finally:
        await db_manager.close()


async def verify_database():
    """验证数据库配置"""
    logger.info("验证数据库配置...")
    
    checks = []
    
    # 检查数据库类型
    if settings.DATABASE_URL.startswith("postgresql"):
        checks.append(("数据库类型", "✅ PostgreSQL"))
    else:
        checks.append(("数据库类型", "❌ 非PostgreSQL，生产环境必须使用PostgreSQL"))
    
    # 检查连接池配置
    if settings.DATABASE_POOL_SIZE >= 10:
        checks.append(("连接池大小", f"✅ {settings.DATABASE_POOL_SIZE}"))
    else:
        checks.append(("连接池大小", f"⚠️ {settings.DATABASE_POOL_SIZE} (建议 >= 10)"))
    
    # 检查密钥
    if settings.SECRET_KEY and len(settings.SECRET_KEY) >= 32:
        checks.append(("密钥强度", "✅ 符合要求"))
    else:
        checks.append(("密钥强度", "❌ 密钥太弱或未设置"))
    
    # 检查Redis
    if settings.REDIS_MODE in ["standalone", "sentinel", "cluster"]:
        checks.append(("Redis模式", f"✅ {settings.REDIS_MODE}"))
    else:
        checks.append(("Redis模式", "❌ 无效模式"))
    
    # 打印检查结果
    print("\n" + "=" * 50)
    print("数据库配置检查")
    print("=" * 50)
    for name, result in checks:
        print(f"{name:20} {result}")
    print("=" * 50 + "\n")
    
    return all("✅" in result for _, result in checks)


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description="FormalMath API 数据库初始化工具")
    parser.add_argument("command", choices=["init", "verify", "check"], 
                       help="命令: init=初始化, verify=验证配置, check=检查连接")
    parser.add_argument("--force", action="store_true", 
                       help="强制重新初始化（删除现有数据）")
    
    args = parser.parse_args()
    
    if args.command == "init":
        if args.force:
            confirm = input("⚠️ 警告: 这将删除所有现有数据！确认吗？(yes/no): ")
            if confirm.lower() != "yes":
                logger.info("操作已取消")
                return
        asyncio.run(init_database())
    
    elif args.command == "verify":
        asyncio.run(verify_database())
    
    elif args.command == "check":
        db_manager.init_engines()
        health = asyncio.run(db_manager.health_check())
        print("\n数据库健康状态:")
        print("-" * 30)
        for key, value in health.items():
            print(f"{key:20} {value}")


if __name__ == "__main__":
    main()
