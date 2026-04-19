---
title: FormalMath API - 生产数据库配置
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath API - 生产数据库配置

## 配置文件清单

### PostgreSQL 配置

| 文件 | 说明 |
|------|------|
| `postgresql.conf` | PostgreSQL 16 生产配置文件 |
|  | - 连接池: max_connections=500 |
|  | - 内存: shared_buffers=8GB, work_mem=32MB |
|  | - WAL: wal_level=replica, archive_mode=on |
|  | - 监控: pg_stat_statements, auto_explain |
|  | - 自动清理: autovacuum调优 |

### Redis 配置

| 文件 | 说明 |
|------|------|
| `redis-cluster.conf` | Redis 7 Cluster 配置 |
|  | - 6节点集群 (3主3从) |
|  | - TLS加密支持 |
|  | - 内存限制: 4GB, allkeys-lru |
|  | - AOF持久化 |
| `redis-sentinel.conf` | Redis Sentinel 配置 |
|  | - 3节点哨兵监控 |
|  | - 自动故障转移 |

### 应用配置

| 文件 | 说明 |
|------|------|
| `app/core/config_production.py` | 生产环境Pydantic配置 |
|  | - 数据库读写分离配置 |
|  | - Redis三种模式支持 |
|  | - 安全配置 (密钥、JWT) |
|  | - 监控和告警配置 |
| `app/core/database_production.py` | 生产数据库连接管理 |
|  | - 异步SQLAlchemy引擎 |
|  | - 读写分离实现 |
|  | - 连接池优化 |
|  | - 健康检查 |
| `app/cache/redis_cluster.py` | Redis集群缓存层 |
|  | - 三种模式自动适配 |
|  | - 分布式锁实现 |
|  | - 滑动窗口限流 |
|  | - 批量操作支持 |

### 数据库迁移

| 文件 | 说明 |
|------|------|
| `alembic.ini` | Alembic 迁移配置 |
| `migrations/env.py` | 迁移环境脚本 (异步支持) |
| `migrations/script.py.mako` | 迁移脚本模板 |

### 备份脚本

| 文件 | 说明 |
|------|------|
| `scripts/backup/postgresql_backup.sh` | Linux PostgreSQL备份脚本 |
| `scripts/backup/postgresql_backup.bat` | Windows PostgreSQL备份脚本 |
| `scripts/backup/redis_backup.sh` | Linux Redis备份脚本 |
| `scripts/backup/redis_backup.bat` | Windows Redis备份脚本 |

备份功能:
- 全量备份 (pg_dump)
- 增量备份 (WAL归档)
- 自动清理过期备份
- S3上传支持
- 备份验证

### Docker部署

| 文件 | 说明 |
|------|------|
| `docker-compose.database.yml` | 数据库服务编排 |
|  | - PostgreSQL 主从复制 |
|  | - Redis 6节点集群 |
|  | - PgAdmin管理工具 |
|  | - 自动备份服务 |

### 辅助脚本

| 文件 | 说明 |
|------|------|
| `scripts/init_database.py` | 数据库初始化脚本 |
| `.env.production.example` | 生产环境变量模板 |
| `docs/DATABASE_PRODUCTION.md` | 完整配置文档 |

## 快速开始

### 1. 使用Docker部署数据库

```bash
# 启动PostgreSQL + Redis集群
docker-compose -f docker-compose.database.yml up -d

# 查看状态
docker-compose -f docker-compose.database.yml ps
```

### 2. 配置环境变量

```bash
# 复制配置文件
cp .env.production.example .env.production

# 编辑配置
vim .env.production
```

### 3. 初始化数据库

```bash
# 验证配置
python scripts/init_database.py verify

# 检查连接
python scripts/init_database.py check

# 初始化表结构
python scripts/init_database.py init
```

### 4. 执行迁移

```bash
# 创建迁移脚本
alembic revision --autogenerate -m "add new tables"

# 执行升级
alembic upgrade head

# 查看状态
alembic current
```

### 5. 配置备份任务

```bash
# Linux - 添加crontab
echo "0 2 * * * /path/to/postgresql_backup.sh full" | crontab -

# Windows - 创建计划任务
schtasks /create /tn "PostgreSQL Backup" /tr "scripts\backup\postgresql_backup.bat full" /sc daily /st 02:00
```

## 架构说明

### 读写分离

```
读请求 ──→ [读连接池] ──→ PostgreSQL Replica 1
                    ├──→ PostgreSQL Replica 2
                    
写请求 ──→ [写连接池] ──→ PostgreSQL Primary
                              │
                              └──→ Streaming Replication ──→ Replicas
```

### Redis模式

```
Standalone:  single-node
                    ↓
Sentinel:    [S1]─[S2]─[S3]
                    ↓
               [Master]─[Replica]
                    ↓
Cluster:     [M1]─[M2]─[M3]
              │     │     │
             [R1]  [R2]  [R3]
```

## 性能参数

### PostgreSQL
- 连接池: 20固定 + 30溢出
- 查询超时: 60秒
- 空闲事务超时: 10分钟
- 连接回收: 1小时

### Redis
- 最大连接: 100/节点
- Socket超时: 5秒
- 健康检查: 30秒
- 集群重定向: 5次

## 监控指标

### 数据库健康检查
```python
# 获取连接池状态
status = await db_manager.get_pool_status()

# 健康检查
health = await db_manager.health_check()
```

### Redis健康检查
```python
# 集群状态
info = await cache.health_check()
```

## 故障排查

### 检查连接池耗尽
```python
# 查看连接状态
status = await db_manager.get_pool_status()
# checked_out 接近 pool_size + max_overflow 时需要扩容
```

### Redis集群故障
```bash
# 检查集群节点
redis-cli -p 6379 CLUSTER NODES

# 检查集群状态
redis-cli -p 6379 CLUSTER INFO
```

## 安全建议

1. ✅ 使用强密码 (32+字符)
2. ✅ 启用TLS加密连接
3. ✅ 数据库部署在私有网络
4. ✅ 定期轮换密钥
5. ✅ 启用审计日志
6. ✅ 最小权限原则

## 参考文档

- [完整数据库文档](../docs/DATABASE_PRODUCTION.md)
- [PostgreSQL官方文档](https://www.postgresql.org/docs/16/)[需更新]
- [Redis Cluster文档](https://redis.io/docs/management/scaling/)[需更新]
- [SQLAlchemy文档](https://docs.sqlalchemy.org/)[需更新]
