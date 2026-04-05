---
title: FormalMath - 生产环境运维手册
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath - 生产环境运维手册

**版本**: v2.0.0  
**创建日期**: 2026年4月4日  
**适用范围**: FormalMath项目生产环境运维  
**文档状态**: ✅ 已批准

---

## 目录

1. [概述](#概述)
2. [日常运维](#日常运维)
3. [监控告警](#监控告警)
4. [故障处理](#故障处理)
5. [备份恢复](#备份恢复)
6. [性能优化](#性能优化)
7. [安全管理](#安全管理)

---

## 概述

### 系统架构

```
┌─────────────────────────────────────────────────────────────┐
│                         用户层                               │
│              (Web浏览器 / 移动设备 / API客户端)               │
└─────────────────────────┬───────────────────────────────────┘
                          │
┌─────────────────────────▼───────────────────────────────────┐
│                      CDN / WAF                               │
│              (CloudFlare / 阿里云CDN)                         │
└─────────────────────────┬───────────────────────────────────┘
                          │
┌─────────────────────────▼───────────────────────────────────┐
│                    负载均衡器 (Nginx)                         │
│              SSL终结 / 反向代理 / 限流 / 缓存                 │
└─────────────────────────┬───────────────────────────────────┘
                          │
        ┌─────────────────┴─────────────────┐
        │                                   │
┌───────▼────────┐              ┌───────────▼────────┐
│   前端服务      │              │     后端API        │
│  (Nginx/SPA)   │              │   (FastAPI/Uvicorn)│
│   端口: 80     │              │    端口: 8000      │
└────────────────┘              └───────────┬────────┘
                                            │
                              ┌─────────────┴─────────────┐
                              │                           │
                    ┌─────────▼────────┐    ┌─────────────▼────────┐
                    │   Redis缓存       │    │   PostgreSQL数据库    │
                    │   端口: 6379     │    │     端口: 5432       │
                    │   (缓存/队列)     │    │    (主从复制)         │
                    └──────────────────┘    └──────────────────────┘
```

### 技术栈

| 组件 | 技术 | 版本 |
|------|------|------|
| 前端 | React + Vite + TypeScript | 18.x |
| 后端 | FastAPI + Python | 3.11 |
| 数据库 | PostgreSQL | 15.x |
| 缓存 | Redis | 7.x |
| 容器 | Docker + Docker Compose | 24.x |
| 编排 | Kubernetes | 1.28+ |
| 监控 | Prometheus + Grafana | latest |
| 日志 | Fluent Bit + Elasticsearch | latest |

---

## 日常运维

### 每日检查清单

```bash
#!/bin/bash
# daily-check.sh - 每日检查脚本

echo "=== FormalMath 每日检查 ==="
echo "检查时间: $(date)"

# 1. 服务状态检查
echo -e "\n[1/5] 服务状态检查..."
docker-compose -f docker-compose.production.yml ps
kubectl get pods -n formalmath-prod

# 2. 资源使用检查
echo -e "\n[2/5] 资源使用检查..."
docker stats --no-stream
echo "---"
kubectl top nodes
kubectl top pods -n formalmath-prod

# 3. 磁盘空间检查
echo -e "\n[3/5] 磁盘空间检查..."
df -h

# 4. 日志检查（错误）
echo -e "\n[4/5] 错误日志检查..."
docker-compose logs --tail=100 backend 2>&1 | grep -i error || echo "无错误日志"

# 5. 备份状态检查
echo -e "\n[5/5] 备份状态检查..."
ls -la /backups/formalmath/

echo -e "\n=== 检查完成 ==="
```

### 日志查看

```bash
# 查看实时日志
docker-compose logs -f backend
docker-compose logs -f frontend

# 查看最近100行
docker-compose logs --tail=100 backend

# 查看特定时间段的日志
docker-compose logs --since="2026-04-04T10:00:00" backend

# 搜索错误日志
docker-compose logs backend 2>&1 | grep -i error

# Kubernetes日志
kubectl logs -f deployment/backend-deployment -n formalmath-prod
kubectl logs -f deployment/backend-deployment -n formalmath-prod --previous  # 上次运行的日志
```

### 服务启停

```bash
# 启动所有服务
docker-compose -f docker-compose.production.yml up -d

# 停止所有服务
docker-compose -f docker-compose.production.yml down

# 重启特定服务
docker-compose -f docker-compose.production.yml restart backend

# 平滑重启（不中断服务）
docker-compose -f docker-compose.production.yml up -d --no-deps --build backend
```

---

## 监控告警

### 关键指标

| 指标 | 正常范围 | 警告阈值 | 严重阈值 |
|------|----------|----------|----------|
| CPU使用率 | < 60% | > 70% | > 85% |
| 内存使用率 | < 70% | > 80% | > 90% |
| 磁盘使用率 | < 70% | > 80% | > 90% |
| API响应时间(P95) | < 200ms | > 500ms | > 1000ms |
| 错误率 | < 0.1% | > 1% | > 5% |
| 数据库连接数 | < 50 | > 70 | > 90 |

### 健康检查端点

```bash
# 后端健康检查
curl -s  | jq .
{
  "status": "healthy",
  "version": "2.0.0",
  "timestamp": "2026-04-04T10:00:00Z",
  "checks": {
    "database": "ok",
    "redis": "ok",
    "disk": "ok"
  }
}

# 前端健康检查
curl -s 
true

# Kubernetes健康检查
kubectl get pods -n formalmath-prod
```

### 告警响应流程

```
收到告警
    │
    ▼
判断告警级别
    │
    ├─► P0 (Critical) ───► 立即处理 ───► 5分钟内响应
    │                           │
    ├─► P1 (Warning) ────► 30分钟内处理
    │                           │
    └─► P2 (Info) ───────► 排期处理
```

---

## 故障处理

### 服务不可用

**症状**: 网站无法访问

**处理步骤**:

```bash
# 1. 检查服务状态
docker-compose ps
kubectl get pods -n formalmath-prod

# 2. 检查日志
docker-compose logs --tail=50 backend

# 3. 检查资源
free -h
df -h
docker stats --no-stream

# 4. 重启服务
docker-compose restart backend
kubectl rollout restart deployment/backend-deployment -n formalmath-prod

# 5. 如无法恢复，执行回滚
./scripts/rollback.sh rollback
```

### 数据库连接池耗尽

**症状**: 应用响应慢，出现数据库连接错误

**处理步骤**:

```sql
-- 1. 查看当前连接数
SELECT count(*) FROM pg_stat_activity;

-- 2. 查看连接详情
SELECT state, count(*) FROM pg_stat_activity GROUP BY state;

-- 3. 终止空闲连接
SELECT pg_terminate_backend(pid) 
FROM pg_stat_activity 
WHERE state = 'idle' 
  AND state_change < NOW() - INTERVAL '1 hour';

-- 4. 临时增加连接池大小
-- 修改配置后重启服务
```

### 内存泄漏

**症状**: 内存持续增长，最终OOM

**处理步骤**:

```bash
# 1. 查看内存使用
docker stats
top -p $(pgrep -d',' node)

# 2. 重启服务（临时解决）
docker-compose restart backend

# 3. 分析内存使用（长期解决）
# 使用 heapdump / profiler 分析
```

### 磁盘空间不足

**症状**: 写入失败，服务异常

**处理步骤**:

```bash
# 1. 查看磁盘使用
df -h

# 2. 查找大文件
du -sh /var/log/* | sort -rh | head -10
du -sh /var/lib/docker/* | sort -rh | head -10

# 3. 清理日志
find /var/log -name "*.log" -mtime +7 -delete

# 4. 清理Docker
docker system prune -a --volumes

# 5. 清理旧备份
find /backups -name "*.sql.gz" -mtime +30 -delete
```

---

## 备份恢复

### 备份策略

| 数据类型 | 备份方式 | 频率 | 保留期 |
|----------|----------|------|--------|
| 数据库 | pg_dump | 每日 | 30天 |
| 数据库 | WAL归档 | 实时 | 7天 |
| 应用配置 | Git | 每次变更 | 永久 |
| Redis | RDB | 每小时 | 7天 |

### 手动备份

```bash
# PostgreSQL备份
pg_dump -h localhost -U formalmath formalmath_db | gzip > /backups/formalmath/backup_$(date +%Y%m%d_%H%M%S).sql.gz

# Redis备份
docker exec formalmath-redis redis-cli SAVE
docker cp formalmath-redis:/data/dump.rdb /backups/formalmath/redis_$(date +%Y%m%d).rdb

# 配置文件备份
tar -czf /backups/formalmath/config_$(date +%Y%m%d).tar.gz docker-compose.yml nginx.conf .env.production
```

### 数据恢复

```bash
# 1. 停止写入服务
docker-compose stop backend
kubectl scale deployment backend-deployment --replicas=0 -n formalmath-prod

# 2. 从备份恢复
gunzip backup_20260404_120000.sql.gz
psql -h localhost -U formalmath -d formalmath_db < backup_20260404_120000.sql

# 3. 验证数据
psql -h localhost -U formalmath -c "SELECT COUNT(*) FROM documents;"

# 4. 恢复服务
docker-compose start backend
kubectl scale deployment backend-deployment --replicas=3 -n formalmath-prod
```

---

## 性能优化

### 数据库优化

```sql
-- 查看慢查询
SELECT query, mean_time, calls 
FROM pg_stat_statements 
ORDER BY mean_time DESC 
LIMIT 10;

-- 查看缺失的索引
SELECT schemaname, tablename, attname as column
FROM pg_stats 
WHERE schemaname = 'public'
  AND n_tup_read > 10000
  AND n_tup_fetch < n_tup_read * 0.5;

-- 添加索引示例
CREATE INDEX CONCURRENTLY idx_documents_category ON documents(category);
```

### 缓存优化

```bash
# Redis监控
redis-cli INFO stats
redis-cli INFO memory

# 查看缓存命中率
redis-cli INFO stats | grep keyspace

# 清理缓存
redis-cli FLUSHDB
```

### 应用优化

```bash
# 调整Gunicorn工作进程数
# 公式: workers = 2 * CPU核心数 + 1
gunicorn main:app --workers 4 --worker-class uvicorn.workers.UvicornWorker

# 启用连接池
# 在配置文件中调整 DATABASE_POOL_SIZE
```

---

## 安全管理

### 安全扫描

```bash
# 镜像安全扫描
docker scan formalmath/backend:latest
trivy image formalmath/backend:latest

# 依赖漏洞扫描
pip-audit
npm audit

# 容器运行时安全
docker-bench-security
```

### 访问控制

```bash
# SSH访问限制
# /etc/ssh/sshd_config
PermitRootLogin no
PasswordAuthentication no
AllowUsers admin deploy

# 防火墙规则
ufw default deny incoming
ufw allow 22/tcp
ufw allow 80/tcp
ufw allow 443/tcp
ufw enable
```

### 日志审计

```bash
# 查看登录日志
last
cat /var/log/auth.log | grep "Accepted"

# 查看命令历史
history

cat ~/.bash_history
```

---

## 附录

### 常用命令速查

```bash
# Docker
docker ps                    # 查看运行中的容器
docker logs <container>      # 查看容器日志
docker exec -it <container> /bin/sh  # 进入容器
docker stats                 # 查看资源使用

# Kubernetes
kubectl get pods             # 查看Pod
kubectl logs <pod>           # 查看Pod日志
kubectl exec -it <pod> -- /bin/sh    # 进入Pod
kubectl top pods             # 查看资源使用
kubectl describe pod <pod>   # 查看Pod详情

# PostgreSQL
psql -h localhost -U formalmath -d formalmath_db  # 连接数据库
\dt                          # 列出表
\du                          # 列出用户
\q                           # 退出

# Redis
redis-cli ping               # 测试连接
redis-cli info               # 查看信息
redis-cli monitor            # 实时监控
```

### 联系信息

| 角色 | 联系方式 | 职责 |
|------|----------|------|
| 运维值班 | ops@formalmath.org | 日常运维、故障处理 |
| 技术负责人 | tech@formalmath.org | 技术决策、架构问题 |
| 安全负责人 | security@formalmath.org | 安全问题、漏洞响应 |
| 应急响应 | emergency@formalmath.org | P0级故障 |

---

**文档版本历史**:

| 版本 | 日期 | 修改人 | 说明 |
|------|------|--------|------|
| v2.0.0 | 2026-04-04 | - | 生产运维手册 |
