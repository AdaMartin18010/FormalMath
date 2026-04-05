---
title: FormalMath API - 生产数据库配置文档
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API - 生产数据库配置文档

## 概述

本文档描述了FormalMath API生产环境的数据库架构、配置和运维指南。

## 架构概览

```
┌─────────────────────────────────────────────────────────────────┐
│                        FormalMath API                           │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │
│  │   Write     │  │    Read     │  │        Cache Layer      │  │
│  │  Operations │  │  Operations │  │  ┌─────────────────┐    │  │
│  │      ↓      │  │      ↓      │  │  │  Redis Cluster  │    │  │
│  └─────────────┘  └─────────────┘  │  │  ├─ Master      │    │  │
│         │                │          │  │  ├─ Replica 1   │    │  │
│         ▼                ▼          │  │  ├─ Replica 2   │    │  │
│  ┌─────────────────────────────────┐│  │  └─ Replica N   │    │  │
│  │    PostgreSQL Primary           ││  └─────────────────┘    │  │
│  │    ┌──────────────────────┐    ││                         │  │
│  │    │  Streaming Replication │   ││  ┌─────────────────┐    │  │
│  │    └──────────────────────┘    ││  │  Celery Queue   │    │  │
│  └─────────────────────────────────┘│  │  ├─ Broker      │    │  │
│         │                │          │  │  └─ Result      │    │  │
│         ▼                ▼          │  └─────────────────┘    │  │
│  ┌─────────────┐  ┌─────────────┐  │                         │  │
│  │  Replica 1  │  │  Replica 2  │  │                         │  │
│  │  (Read Only)│  │  (Read Only)│  │                         │  │
│  └─────────────┘  └─────────────┘  │                         │  │
└─────────────────────────────────────────────────────────────────┘
```

## PostgreSQL 配置

### 安装要求

- PostgreSQL 15+ 或 16+
- 至少 8GB RAM（推荐 32GB+）
- SSD 存储

### 关键配置参数

| 参数 | 默认值 | 说明 |
|------|--------|------|
| `max_connections` | 500 | 最大连接数 |
| `shared_buffers` | 8GB | 共享缓冲区（25% RAM） |
| `effective_cache_size` | 24GB | 有效缓存大小（75% RAM） |
| `work_mem` | 32MB | 查询工作内存 |
| `maintenance_work_mem` | 2GB | 维护操作内存 |
| `wal_level` | replica | WAL日志级别 |
| `max_wal_size` | 4GB | 最大WAL大小 |

### 主从复制配置

#### 主节点配置

```ini
# postgresql.conf
wal_level = replica
max_wal_senders = 10
max_replication_slots = 10
wal_keep_size = 2GB
hot_standby = on
```

#### 创建复制用户

```sql
CREATE ROLE replicator WITH REPLICATION LOGIN PASSWORD 'strong_password';
```

#### 从节点配置

```ini
# postgresql.conf
primary_conninfo = 'host=primary_host port=5432 user=replicator password=strong_password'
restore_command = 'cp /var/lib/postgresql/archive/%f %p'
hot_standby = on
```

### 性能优化索引

```sql
-- 知识图谱复合索引
CREATE INDEX idx_kg_node_branch_difficulty 
ON knowledge_graph_nodes(branch, difficulty);

-- 用户进度唯一索引
CREATE UNIQUE INDEX idx_user_progress_user_concept 
ON user_progress(user_id, concept_id);

-- 全文搜索索引
CREATE INDEX idx_concepts_name_trgm 
ON concepts USING gin (name gin_trgm_ops);

-- 覆盖索引
CREATE INDEX idx_concept_relations_covering 
ON knowledge_graph_relations(source_id, target_id, relation_type)
INCLUDE (weight, created_at);
```

## Redis 集群配置

### 部署模式

支持三种部署模式：

1. **Standalone** - 单机模式（开发/测试环境）
2. **Sentinel** - 主从+哨兵模式（中小型生产环境）
3. **Cluster** - 集群模式（大型生产环境）

### Redis Cluster 架构

```
        ┌─────────────┐
        │  Client     │
        └──────┬──────┘
               │
    ┌──────────┼──────────┐
    │          │          │
    ▼          ▼          ▼
┌───────┐ ┌───────┐ ┌───────┐
│Master1│ │Master2│ │Master3│
│:6379  │ │:6380  │ │:6381  │
└───┬───┘ └───┬───┘ └───┬───┘
    │         │         │
    ▼         ▼         ▼
┌───────┐ ┌───────┐ ┌───────┐
│Replica│ │Replica│ │Replica│
│:6382  │ │:6383  │ │:6384  │
└───────┘ └───────┘ └───────┘
```

### 集群搭建步骤

```bash
# 1. 启动6个Redis实例
redis-server /etc/redis/redis-6379.conf
redis-server /etc/redis/redis-6380.conf
redis-server /etc/redis/redis-6381.conf
redis-server /etc/redis/redis-6382.conf
redis-server /etc/redis/redis-6383.conf
redis-server /etc/redis/redis-6384.conf

# 2. 创建集群
redis-cli --cluster create \
  127.0.0.1:6379 127.0.0.1:6380 127.0.0.1:6381 \
  127.0.0.1:6382 127.0.0.1:6383 127.0.0.1:6384 \
  --cluster-replicas 1
```

### 关键配置

```ini
# redis-cluster.conf
cluster-enabled yes
cluster-config-file nodes.conf
cluster-node-timeout 5000
cluster-require-full-coverage no
cluster-replica-validity-factor 10

# 内存管理
maxmemory 4gb
maxmemory-policy allkeys-lru

# 持久化
appendonly yes
appendfsync everysec
auto-aof-rewrite-percentage 100
```

## 连接池配置

### Python应用配置

```python
# 主库连接池
DATABASE_POOL_SIZE=20
DATABASE_MAX_OVERFLOW=30
DATABASE_POOL_TIMEOUT=30
DATABASE_POOL_RECYCLE=3600
DATABASE_POOL_PRE_PING=true

# Redis连接池
REDIS_MAX_CONNECTIONS=100
REDIS_MIN_CONNECTIONS=10
REDIS_SOCKET_TIMEOUT=5.0
REDIS_HEALTH_CHECK_INTERVAL=30
```

### 连接池监控

```python
# 获取连接池状态
status = await db_manager.get_pool_status()
print(status)
# {
#   "primary": {
#     "size": 20,
#     "checked_in": 15,
#     "checked_out": 5,
#     "overflow": 0
#   },
#   "replicas": [...]
# }
```

## 数据库迁移

### 使用 Alembic

```bash
# 初始化迁移环境
alembic init migrations

# 创建迁移脚本
alembic revision --autogenerate -m "create tables"

# 执行升级
alembic upgrade head

# 回滚
alembic downgrade -1

# 查看历史
alembic history --verbose
```

### 生产环境迁移注意事项

1. **备份** - 迁移前必须备份数据库
2. **事务** - 大表迁移应使用分批处理
3. **锁表** - 避免长时间锁表操作
4. **测试** - 先在测试环境验证

## 备份策略

### 备份类型

| 类型 | 频率 | 保留期 | 说明 |
|------|------|--------|------|
| 全量备份 | 每日 | 30天 | pg_dump |
| 增量备份 | 每小时 | 7天 | WAL归档 |
| 实时备份 | 持续 | 3天 | 流复制 |

### 自动备份脚本

```bash
# 执行备份
./scripts/backup/postgresql_backup.sh full

# 验证备份
./scripts/backup/postgresql_backup.sh verify

# 清理过期备份
./scripts/backup/postgresql_backup.sh cleanup
```

### 备份恢复

```bash
# 从全量备份恢复
pg_restore -h localhost -U formalmath -d formalmath backup.dump

# 时间点恢复
pg_basebackup -D /var/lib/postgresql/data -X fetch
# 恢复WAL日志到指定时间点
```

## 监控与告警

### 关键指标

**PostgreSQL:**
- 连接数使用率
- 查询响应时间
- 锁等待
- WAL延迟
- 复制延迟

**Redis:**
- 内存使用率
- 命中率
- 连接数
- 命令延迟
- 集群状态

### 健康检查端点

```python
# 数据库健康检查
GET /health/db

# Redis健康检查
GET /health/redis

# 完整系统检查
GET /health
```

## 故障处理

### 常见故障

| 故障 | 原因 | 解决方案 |
|------|------|----------|
| 连接池耗尽 | 连接未正确释放 | 检查代码连接释放；增加连接池大小 |
| 复制延迟 | 主库写入过快 | 优化查询；增加从库；使用并行复制 |
| Redis内存不足 | 缓存未过期 | 调整TTL；增加内存；优化数据结构 |
| 死锁 | 并发事务冲突 | 优化事务顺序；减少事务范围 |

### 故障转移

#### PostgreSQL

```bash
# 提升从库为主库
pg_ctl promote -D /var/lib/postgresql/data
```

#### Redis Sentinel

```bash
# 查看当前主节点
redis-cli -p 26379 SENTINEL get-master-addr-by-name formalmath-master

# 手动故障转移
redis-cli -p 26379 SENTINEL failover formalmath-master
```

## 安全最佳实践

1. **网络隔离** - 数据库应在私有子网
2. **TLS加密** - 所有连接使用TLS
3. **强密码** - 使用复杂密码并定期更换
4. **最小权限** - 应用使用只读或有限写入权限
5. **审计日志** - 启用查询日志记录

## 性能调优清单

- [ ] 连接池大小适当
- [ ] 索引覆盖率 > 95%
- [ ] 慢查询 < 1%
- [ ] 缓存命中率 > 90%
- [ ] 复制延迟 < 1秒
- [ ] 备份窗口完成
- [ ] 监控告警正常

## 参考文档

- [PostgreSQL官方文档](https://www.postgresql.org/docs/)[需更新]
- [Redis Cluster教程](https://redis.io/topics/cluster-tutorial)[需更新]
- [SQLAlchemy文档](https://docs.sqlalchemy.org/)[需更新]
- [Alembic文档](https://alembic.sqlalchemy.org/)[需更新]
