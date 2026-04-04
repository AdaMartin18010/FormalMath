"""
FormalMath - 数据库查询优化配置
包含连接池配置、查询优化、索引建议等
"""

from sqlalchemy import event
from sqlalchemy.engine import Engine
import logging

logger = logging.getLogger(__name__)

# 数据库连接池配置 - 生产环境优化
DATABASE_POOL_CONFIG = {
    'pool_size': 20,  # 连接池大小
    'max_overflow': 10,  # 超出pool_size的最大连接数
    'pool_timeout': 30,  # 获取连接的超时时间（秒）
    'pool_recycle': 3600,  # 连接回收时间（秒）
    'pool_pre_ping': True,  # 连接前ping测试
    'echo': False,  # 不打印SQL语句
    'echo_pool': False,  # 不打印连接池日志
}

# SQLite特定优化（开发环境）
SQLITE_PRAGMAS = [
    'PRAGMA journal_mode=WAL;',  # Write-Ahead Logging模式
    'PRAGMA synchronous=NORMAL;',  # 同步模式
    'PRAGMA cache_size=-64000;',  # 64MB缓存
    'PRAGMA temp_store=MEMORY;',  # 临时表存储在内存
    'PRAGMA mmap_size=30000000000;',  # 内存映射
    'PRAGMA page_size=4096;',  # 页面大小
]

# PostgreSQL特定优化
POSTGRESQL_OPTIMIZATIONS = {
    'connect_args': {
        'connect_timeout': 10,
        'options': '-c statement_timeout=30000',  # 30秒查询超时
    },
    'execution_options': {
        'isolation_level': 'READ_COMMITTED',
    }
}


@event.listens_for(Engine, "connect")
def set_sqlite_pragmas(dbapi_conn, connection_record):
    """设置SQLite优化参数"""
    cursor = dbapi_conn.cursor()
    for pragma in SQLITE_PRAGMAS:
        try:
            cursor.execute(pragma)
        except Exception as e:
            logger.warning(f"Failed to execute {pragma}: {e}")
    cursor.close()


@event.listens_for(Engine, "before_cursor_execute")
def before_cursor_execute(conn, cursor, statement, parameters, context, executemany):
    """查询执行前回调 - 可用于日志记录"""
    conn.info.setdefault('query_start_time', [])
    import time
    conn.info['query_start_time'].append(time.time())


@event.listens_for(Engine, "after_cursor_execute")
def after_cursor_execute(conn, cursor, statement, parameters, context, executemany):
    """查询执行后回调 - 用于慢查询日志"""
    import time
    total_time = time.time() - conn.info['query_start_time'].pop(-1)
    
    # 记录慢查询（超过1秒）
    if total_time > 1.0:
        logger.warning(
            f"Slow query detected ({total_time:.2f}s): {statement[:200]}"
        )


class QueryOptimizer:
    """查询优化器"""
    
    @staticmethod
    def optimize_query(query, *options):
        """
        应用查询优化选项
        
        Options:
            - 'eager_load': 预加载关联数据
            - 'lazy_load': 延迟加载
            - 'yield_per': 批量获取
            - 'only': 只选择需要的列
        """
        for option in options:
            if isinstance(option, tuple):
                opt_name, opt_value = option
                if opt_name == 'eager_load':
                    query = query.options(opt_value)
                elif opt_name == 'yield_per':
                    query = query.yield_per(opt_value)
                elif opt_name == 'only':
                    query = query.options(opt_value)
        return query
    
    @staticmethod
    def batch_insert(session, model, data_list, batch_size=1000):
        """批量插入优化"""
        from sqlalchemy import insert
        
        for i in range(0, len(data_list), batch_size):
            batch = data_list[i:i + batch_size]
            session.execute(insert(model), batch)
            session.commit()
    
    @staticmethod
    def batch_update(session, model, updates, batch_size=1000):
        """批量更新优化"""
        from sqlalchemy import update
        
        for i in range(0, len(updates), batch_size):
            batch = updates[i:i + batch_size]
            for update_data in batch:
                session.execute(
                    update(model).where(
                        model.id == update_data['id']
                    ).values(**update_data)
                )
            session.commit()


# 推荐索引配置（用于数据库迁移）
RECOMMENDED_INDEXES = {
    'users': [
        ('username', 'idx_users_username'),
        ('email', 'idx_users_email'),
        ('created_at', 'idx_users_created_at'),
    ],
    'math_concepts': [
        ('msc_code', 'idx_concepts_msc'),
        ('category', 'idx_concepts_category'),
        ('difficulty_level', 'idx_concepts_difficulty'),
        ('created_at', 'idx_concepts_created_at'),
    ],
    'learning_progress': [
        ('user_id', 'idx_progress_user'),
        ('concept_id', 'idx_progress_concept'),
        ('user_id', 'concept_id', 'idx_progress_user_concept'),
        ('updated_at', 'idx_progress_updated'),
    ],
    'proof_attempts': [
        ('user_id', 'idx_attempts_user'),
        ('theorem_id', 'idx_attempts_theorem'),
        ('status', 'idx_attempts_status'),
        ('created_at', 'idx_attempts_created'),
    ],
    'lean_theorems': [
        ('name', 'idx_theorems_name'),
        ('module', 'idx_theorems_module'),
        ('formalized', 'idx_theorems_formalized'),
    ],
}


def generate_index_sql(table_name: str, columns: tuple, index_name: str) -> str:
    """生成创建索引的SQL语句"""
    if isinstance(columns, str):
        columns = (columns,)
    
    column_list = ', '.join(columns)
    return f"CREATE INDEX IF NOT EXISTS {index_name} ON {table_name} ({column_list});"


def get_all_index_sql() -> list:
    """获取所有推荐索引的SQL语句"""
    sql_statements = []
    for table, indexes in RECOMMENDED_INDEXES.items():
        for columns, index_name in indexes:
            sql_statements.append(generate_index_sql(table, columns, index_name))
    return sql_statements


# 连接池监控
class ConnectionPoolMonitor:
    """连接池监控器"""
    
    def __init__(self, engine):
        self.engine = engine
    
    def get_stats(self) -> dict:
        """获取连接池统计信息"""
        pool = self.engine.pool
        return {
            'size': pool.size(),
            'checked_in': pool.checkedin(),
            'checked_out': pool.checkedout(),
            'overflow': pool.overflow(),
        }
    
    def is_healthy(self) -> bool:
        """检查连接池健康状态"""
        stats = self.get_stats()
        # 如果溢出连接过多，可能存在问题
        return stats['overflow'] < DATABASE_POOL_CONFIG['max_overflow'] * 0.8
