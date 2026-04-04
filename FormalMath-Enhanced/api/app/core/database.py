"""
数据库连接池和优化配置
"""
import logging
from typing import Generator, Optional
from contextlib import contextmanager
from sqlalchemy import create_engine, event, Index, text
from sqlalchemy.orm import sessionmaker, Session, declarative_base
from sqlalchemy.pool import QueuePool
from .config import settings

logger = logging.getLogger(__name__)

# 声明基类
Base = declarative_base()


class DatabaseManager:
    """数据库管理器 - 连接池和查询优化"""
    
    def __init__(self):
        self.engine = None
        self.SessionLocal = None
        self._initialized = False
    
    def init_engine(self):
        """初始化数据库引擎和连接池"""
        if self._initialized:
            return
        
        # 创建引擎，配置连接池
        self.engine = create_engine(
            settings.DATABASE_URL,
            poolclass=QueuePool,
            pool_size=settings.DATABASE_POOL_SIZE,
            max_overflow=settings.DATABASE_MAX_OVERFLOW,
            pool_timeout=settings.DATABASE_POOL_TIMEOUT,
            pool_recycle=settings.DATABASE_POOL_RECYCLE,
            pool_pre_ping=True,  # 自动检测断开的连接
            echo=settings.DEBUG,
        )
        
        # 创建会话工厂
        self.SessionLocal = sessionmaker(
            autocommit=False,
            autoflush=False,
            bind=self.engine
        )
        
        # 添加事件监听器
        self._setup_event_listeners()
        
        self._initialized = True
        logger.info(f"数据库连接池初始化完成: pool_size={settings.DATABASE_POOL_SIZE}")
    
    def _setup_event_listeners(self):
        """设置SQLAlchemy事件监听器"""
        
        @event.listens_for(self.engine, "connect")
        def on_connect(dbapi_conn, connection_record):
            """连接建立时的回调"""
            logger.debug("新数据库连接已建立")
        
        @event.listens_for(self.engine, "checkout")
        def on_checkout(dbapi_conn, connection_record, connection_proxy):
            """连接检出时的回调"""
            logger.debug("数据库连接已检出")
    
    def create_tables(self):
        """创建所有表"""
        Base.metadata.create_all(bind=self.engine)
        logger.info("数据库表创建完成")
    
    def create_indexes(self):
        """创建性能优化索引"""
        from ..models import models
        
        # 用户学习路径索引
        Index(
            'idx_learning_path_user_status',
            models.LearningPath.user_id,
            models.LearningPath.status
        ).create(self.engine, checkfirst=True)
        
        # 知识图谱节点索引
        Index(
            'idx_kg_node_branch_difficulty',
            models.KnowledgeGraphNode.branch,
            models.KnowledgeGraphNode.difficulty
        ).create(self.engine, checkfirst=True)
        
        # 学习进度索引
        Index(
            'idx_user_progress_user_concept',
            models.UserProgress.user_id,
            models.UserProgress.concept_id,
            unique=True
        ).create(self.engine, checkfirst=True)
        
        # 认知诊断索引
        Index(
            'idx_diagnosis_user_created',
            models.CognitiveDiagnosis.user_id,
            models.CognitiveDiagnosis.created_at.desc()
        ).create(self.engine, checkfirst=True)
        
        # 复合查询优化索引
        with self.engine.connect() as conn:
            # 为常用查询创建覆盖索引
            conn.execute(text("""
                CREATE INDEX IF NOT EXISTS idx_concept_relations_covering 
                ON knowledge_graph_relations(source_id, target_id, relation_type)
            """))
            
            conn.execute(text("""
                CREATE INDEX IF NOT EXISTS idx_user_activities_covering
                ON user_activities(user_id, activity_type, created_at DESC)
            """))
            
            conn.commit()
        
        logger.info("数据库索引创建完成")
    
    def get_db(self) -> Generator[Session, None, None]:
        """获取数据库会话（依赖注入使用）"""
        if not self._initialized:
            self.init_engine()
        
        db = self.SessionLocal()
        try:
            yield db
        finally:
            db.close()
    
    @contextmanager
    def session_scope(self) -> Generator[Session, None, None]:
        """提供事务范围的会话上下文管理器"""
        if not self._initialized:
            self.init_engine()
        
        session = self.SessionLocal()
        try:
            yield session
            session.commit()
        except Exception as e:
            session.rollback()
            raise e
        finally:
            session.close()
    
    def execute_optimized_query(self, query: str, params: Optional[dict] = None):
        """执行优化的原始SQL查询"""
        with self.engine.connect() as conn:
            result = conn.execute(text(query), params or {})
            return result.fetchall()
    
    def get_pool_status(self) -> dict:
        """获取连接池状态"""
        if not self.engine:
            return {"error": "引擎未初始化"}
        
        pool = self.engine.pool
        return {
            "size": pool.size(),
            "checked_in": pool.checkedin(),
            "checked_out": pool.checkedout(),
            "overflow": pool.overflow(),
        }


# 全局数据库管理器实例
db_manager = DatabaseManager()


def get_db() -> Generator[Session, None, None]:
    """FastAPI依赖注入使用的数据库会话生成器"""
    yield from db_manager.get_db()


def init_db():
    """初始化数据库"""
    db_manager.init_engine()
    db_manager.create_tables()
    db_manager.create_indexes()
