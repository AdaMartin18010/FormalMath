"""
FormalMath API - 生产环境数据库连接池和优化配置
支持PostgreSQL读写分离、连接池优化、查询优化
"""
import logging
from contextlib import asynccontextmanager
from typing import AsyncGenerator, Optional, List
from sqlalchemy import create_engine, event, text
from sqlalchemy.engine import Engine
from sqlalchemy.ext.asyncio import (
    create_async_engine, 
    AsyncSession, 
    async_sessionmaker,
    AsyncEngine
)
from sqlalchemy.orm import declarative_base
from sqlalchemy.pool import QueuePool, NullPool
from .config_production import settings_production as settings

logger = logging.getLogger(__name__)

# 声明基类
Base = declarative_base()


class DatabaseManager:
    """生产环境数据库管理器 - 支持读写分离和连接池优化"""
    
    def __init__(self):
        self.write_engine: Optional[AsyncEngine] = None
        self.read_engines: List[AsyncEngine] = []
        self.read_engine_index: int = 0
        self.SessionLocal: Optional[async_sessionmaker] = None
        self._initialized = False
    
    def init_engines(self):
        """初始化数据库引擎和连接池"""
        if self._initialized:
            return
        
        # 初始化写引擎（主库）
        self.write_engine = self._create_engine(
            settings.DATABASE_URL,
            pool_size=settings.DATABASE_POOL_SIZE,
            max_overflow=settings.DATABASE_MAX_OVERFLOW,
            is_primary=True
        )
        
        # 初始化读引擎（从库）- 用于读写分离
        for idx, replica_url in enumerate(settings.DATABASE_READ_REPLICA_URLS):
            read_engine = self._create_engine(
                replica_url,
                pool_size=max(5, settings.DATABASE_POOL_SIZE // 2),
                max_overflow=max(10, settings.DATABASE_MAX_OVERFLOW // 2),
                is_primary=False,
                replica_index=idx
            )
            self.read_engines.append(read_engine)
        
        # 创建会话工厂
        self.SessionLocal = async_sessionmaker(
            bind=self.write_engine,
            autocommit=False,
            autoflush=False,
            expire_on_commit=False,
            class_=AsyncSession
        )
        
        # 添加事件监听器
        self._setup_event_listeners()
        
        self._initialized = True
        logger.info(
            f"生产环境数据库连接池初始化完成: "
            f"主库pool_size={settings.DATABASE_POOL_SIZE}, "
            f"从库数量={len(self.read_engines)}"
        )
    
    def _create_engine(
        self, 
        url: str, 
        pool_size: int, 
        max_overflow: int,
        is_primary: bool = True,
        replica_index: int = 0
    ) -> AsyncEngine:
        """创建异步数据库引擎"""
        
        # 转换为异步URL
        async_url = url
        if url.startswith("postgresql://"):
            async_url = url.replace("postgresql://", "postgresql+asyncpg://", 1)
        
        engine = create_async_engine(
            async_url,
            poolclass=QueuePool,
            pool_size=pool_size,
            max_overflow=max_overflow,
            pool_timeout=settings.DATABASE_POOL_TIMEOUT,
            pool_recycle=settings.DATABASE_POOL_RECYCLE,
            pool_pre_ping=settings.DATABASE_POOL_PRE_PING,
            echo=settings.DATABASE_ECHO,
            connect_args={
                "timeout": settings.DATABASE_CONNECT_TIMEOUT,
                "command_timeout": settings.DATABASE_STATEMENT_TIMEOUT / 1000,
                "server_settings": {
                    "application_name": f"formalmath_api_{'primary' if is_primary else f'replica_{replica_index}'}",
                    "jit": "on",
                    "statement_timeout": str(settings.DATABASE_STATEMENT_TIMEOUT),
                    "idle_in_transaction_session_timeout": str(settings.DATABASE_IDLE_IN_TRANSACTION_TIMEOUT)
                }
            }
        )
        
        return engine
    
    def _setup_event_listeners(self):
        """设置SQLAlchemy事件监听器"""
        
        @event.listens_for(self.write_engine.sync_engine, "connect")
        def on_connect(dbapi_conn, connection_record):
            """连接建立时的回调"""
            logger.debug("新的数据库连接已建立")
        
        @event.listens_for(self.write_engine.sync_engine, "checkout")
        def on_checkout(dbapi_conn, connection_record, connection_proxy):
            """连接检出时的回调"""
            logger.debug("数据库连接已检出")
        
        @event.listens_for(self.write_engine.sync_engine, "checkin")
        def on_checkin(dbapi_conn, connection_record):
            """连接归还时的回调"""
            logger.debug("数据库连接已归还")
    
    def get_read_engine(self) -> AsyncEngine:
        """获取读引擎（轮询选择）"""
        if not self.read_engines:
            return self.write_engine
        
        # 简单的轮询负载均衡
        engine = self.read_engines[self.read_engine_index]
        self.read_engine_index = (self.read_engine_index + 1) % len(self.read_engines)
        return engine
    
    async def create_tables(self):
        """创建所有表"""
        async with self.write_engine.begin() as conn:
            await conn.run_sync(Base.metadata.create_all)
        logger.info("数据库表创建完成")
    
    async def create_indexes(self):
        """创建性能优化索引"""
        from ..models import models  # noqa: F401
        
        async with self.write_engine.begin() as conn:
            # 创建复合索引
            indexes = [
                # 用户学习路径索引
                """
                CREATE INDEX IF NOT EXISTS idx_learning_path_user_status 
                ON learning_paths(user_id, status) 
                WHERE status IS NOT NULL
                """,
                
                # 知识图谱节点索引
                """
                CREATE INDEX IF NOT EXISTS idx_kg_node_branch_difficulty 
                ON knowledge_graph_nodes(branch, difficulty)
                """,
                
                # 学习进度唯一索引
                """
                CREATE UNIQUE INDEX IF NOT EXISTS idx_user_progress_user_concept 
                ON user_progress(user_id, concept_id)
                """,
                
                # 认知诊断时间索引
                """
                CREATE INDEX IF NOT EXISTS idx_diagnosis_user_created 
                ON cognitive_diagnoses(user_id, created_at DESC)
                """,
                
                # 全文搜索索引
                """
                CREATE INDEX IF NOT EXISTS idx_concepts_name_trgm 
                ON concepts USING gin (name gin_trgm_ops)
                """,
                
                # 覆盖索引
                """
                CREATE INDEX IF NOT EXISTS idx_concept_relations_covering 
                ON knowledge_graph_relations(source_id, target_id, relation_type)
                INCLUDE (weight, created_at)
                """,
                
                # 部分索引
                """
                CREATE INDEX IF NOT EXISTS idx_users_active 
                ON users(email) 
                WHERE is_active = true
                """,
            ]
            
            for sql in indexes:
                try:
                    await conn.execute(text(sql))
                except Exception as e:
                    logger.warning(f"创建索引失败 (可能已存在): {e}")
        
        logger.info("数据库索引创建完成")
    
    async def get_db(self) -> AsyncGenerator[AsyncSession, None]:
        """获取数据库会话（依赖注入使用）- 写操作"""
        if not self._initialized:
            self.init_engines()
        
        async with self.SessionLocal() as session:
            try:
                yield session
            finally:
                await session.close()
    
    async def get_read_db(self) -> AsyncGenerator[AsyncSession, None]:
        """获取数据库会话（只读操作）- 读操作"""
        if not self._initialized:
            self.init_engines()
        
        read_engine = self.get_read_engine()
        async_session = async_sessionmaker(
            bind=read_engine,
            autocommit=False,
            autoflush=False,
            expire_on_commit=False,
            class_=AsyncSession
        )
        
        async with async_session() as session:
            try:
                yield session
            finally:
                await session.close()
    
    @asynccontextmanager
    async def session_scope(self, readonly: bool = False):
        """提供事务范围的会话上下文管理器"""
        if not self._initialized:
            self.init_engines()
        
        engine = self.get_read_engine() if readonly else self.write_engine
        async_session = async_sessionmaker(
            bind=engine,
            autocommit=False,
            autoflush=False,
            expire_on_commit=False,
            class_=AsyncSession
        )
        
        async with async_session() as session:
            try:
                yield session
                await session.commit()
            except Exception as e:
                await session.rollback()
                raise e
            finally:
                await session.close()
    
    async def execute_optimized_query(self, query: str, params: Optional[dict] = None):
        """执行优化的原始SQL查询"""
        async with self.write_engine.connect() as conn:
            result = await conn.execute(text(query), params or {})
            return result.fetchall()
    
    async def get_pool_status(self) -> dict:
        """获取连接池状态"""
        if not self.write_engine:
            return {"error": "引擎未初始化"}
        
        # 获取主库连接池状态
        pool = self.write_engine.pool
        status = {
            "primary": {
                "size": pool.size(),
                "checked_in": pool.checkedin(),
                "checked_out": pool.checkedout(),
                "overflow": pool.overflow(),
            },
            "replicas": []
        }
        
        # 获取从库连接池状态
        for idx, engine in enumerate(self.read_engines):
            replica_pool = engine.pool
            status["replicas"].append({
                "index": idx,
                "size": replica_pool.size(),
                "checked_in": replica_pool.checkedin(),
                "checked_out": replica_pool.checkedout(),
            })
        
        return status
    
    async def health_check(self) -> dict:
        """数据库健康检查"""
        health = {
            "status": "healthy",
            "primary": False,
            "replicas": []
        }
        
        # 检查主库
        try:
            async with self.write_engine.connect() as conn:
                result = await conn.execute(text("SELECT 1"))
                await result.scalar()
                health["primary"] = True
        except Exception as e:
            health["primary"] = False
            health["status"] = "unhealthy"
            logger.error(f"主库健康检查失败: {e}")
        
        # 检查从库
        for idx, engine in enumerate(self.read_engines):
            try:
                async with engine.connect() as conn:
                    result = await conn.execute(text("SELECT 1"))
                    await result.scalar()
                    health["replicas"].append({"index": idx, "status": "healthy"})
            except Exception as e:
                health["replicas"].append({"index": idx, "status": "unhealthy", "error": str(e)})
                logger.error(f"从库 {idx} 健康检查失败: {e}")
        
        return health
    
    async def close(self):
        """关闭所有数据库连接"""
        if self.write_engine:
            await self.write_engine.dispose()
        
        for engine in self.read_engines:
            await engine.dispose()
        
        logger.info("数据库连接已关闭")


# 全局数据库管理器实例
db_manager = DatabaseManager()


async def get_db() -> AsyncGenerator[AsyncSession, None]:
    """FastAPI依赖注入使用的数据库会话生成器（写操作）"""
    async for session in db_manager.get_db():
        yield session


async def get_read_db() -> AsyncGenerator[AsyncSession, None]:
    """FastAPI依赖注入使用的数据库会话生成器（只读操作）"""
    async for session in db_manager.get_read_db():
        yield session


async def init_db():
    """初始化数据库"""
    db_manager.init_engines()
    await db_manager.create_tables()
    await db_manager.create_indexes()
