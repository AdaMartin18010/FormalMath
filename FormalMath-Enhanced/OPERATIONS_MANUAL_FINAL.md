---
title: FormalMath 运维手册 - 生产环境最终版
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 运维手册 - 生产环境最终版

**版本**: v2.0.0
**更新日期**: 2026-04-04
**适用环境**: Production

---

## 目录

1. [系统架构](#系统架构)
2. [快速参考](#快速参考)
3. [日常运维](#日常运维)
4. [监控告警](#监控告警)
5. [性能优化](#性能优化)
6. [故障处理](#故障处理)
7. [备份恢复](#备份恢复)
8. [安全维护](#安全维护)
9. [灾难恢复](#灾难恢复)

---

## 系统架构

### 架构概览

```
┌─────────────────────────────────────────────────────────────┐
│                         用户层                               │
└───────────────────────┬─────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────┐
│                      Nginx                                   │
│         (反向代理/负载均衡/SSL/缓存/限流)                     │
└───────────────┬───────────────────────┬─────────────────────┘
                │                       │
    ┌───────────▼──────────┐   ┌───────▼────────┐
    │      Frontend        │   │    Backend     │
    │    (React/Vite)      │   │   (FastAPI)    │
    └───────────┬──────────┘   └───────┬────────┘
                │                      │
                │           ┌──────────▼──────────┐
                │           │       Redis         │
                │           │   (缓存/消息队列)    │
                │           └──────────┬──────────┘
                │                      │
                │           ┌──────────▼──────────┐
                │           │   Celery Worker     │
                │           │    (异步任务)        │
                │           └─────────────────────┘
                │
    ┌───────────▼─────────────────────────────────────┐
    │              监控层                               │
    │  Prometheus + Grafana + AlertManager + ELK       │
    └─────────────────────────────────────────────────┘
```

### 服务规格

| 服务 | 实例数 | CPU限制 | 内存限制 | 端口 |
|------|--------|---------|----------|------|
| Nginx | 2 | 1.0 | 512M | 80/443 |
| Backend | 4 | 4.0 | 4G | 8000 |
| Frontend | 2 | 0.25 | 128M | 80 |
| Redis | 1 | 2.0 | 4G | 6379 |
| Celery Worker | 4 | 2.0 | 2G | - |

---

## 快速参考

### 常用命令速查表

```bash
# ========== 服务管理 ==========
# 启动所有服务
docker-compose -f docker-compose.production.yml up -d

# 停止所有服务
docker-compose -f docker-compose.production.yml down

# 重启服务
docker-compose -f docker-compose.production.yml restart <service>

# 查看服务状态
docker-compose -f docker-compose.production.yml ps

# 查看资源使用
docker stats --no-stream

# ========== 日志管理 ==========
# 查看所有日志
docker-compose -f docker-compose.production.yml logs -f --tail=100

# 查看特定服务日志
docker-compose -f docker-compose.production.yml logs -f backend

# 导出日志
docker-compose -f docker-compose.production.yml logs backend > backend.log

# ========== 健康检查 ==========
# 系统健康检查
curl
curl

# 完整健康检查脚本
./scripts/health-check.sh

# ========== 备份恢复 ==========
# 创建全量备份
./scripts/backup-scheduler.sh full

# 恢复备份
./scripts/backup-scheduler.sh restore -d <backup-date>

# ========== 监控访问 ==========
# Grafana
open   # admin/admin

# Prometheus
open

# ========== 性能测试 ==========
# 运行负载测试
cd testing && docker-compose -f docker-compose.load-test.yml up -d

# 访问Locust
open

# ========== 安全扫描 ==========
# 运行安全检查
./scripts/security-hardening.sh full

# 镜像漏洞扫描
docker run --rm aquasec/trivy image formalmath-backend:latest
```

### 关键文件路径

```
项目目录:     /opt/formalmath-enhanced
配置文件:     /opt/formalmath-enhanced/.env.production
日志目录:     /opt/formalmath-enhanced/logs/
备份目录:     /opt/formalmath-enhanced/backups/
数据目录:     /opt/formalmath-enhanced/data/
SSL证书:      /opt/formalmath-enhanced/nginx/ssl/
监控配置:     /opt/formalmath-enhanced/monitoring/
运维脚本:     /opt/formalmath-enhanced/scripts/
```

---

## 日常运维

### 每日检查清单

```bash
# 1. 检查服务状态（5分钟）
docker-compose -f docker-compose.production.yml ps

# 2. 检查资源使用（5分钟）
docker stats --no-stream
df -h
free -h

# 3. 检查日志错误（10分钟）
docker-compose -f docker-compose.production.yml logs --tail=100 | grep -i error

# 4. 检查健康状态（5分钟）
curl -f
curl -f

# 5. 检查备份状态（5分钟）
ls -la /opt/formalmath-enhanced/backups/
```

### 每周维护任务

```bash
# 1. 安全更新检查
sudo apt update && sudo apt list --upgradable

# 2. 日志清理
./scripts/log-rotate.sh clean -d 30

# 3. 备份验证
./scripts/backup-scheduler.sh verify

# 4. SSL证书检查
echo | openssl s_client -servername formalmath.example.com \
  -connect formalmath.example.com:443 2>/dev/null | openssl x509 -noout -dates

# 5. 安全扫描
./scripts/security-hardening.sh full
```

### 每月维护任务

```bash
# 1. 系统更新
sudo apt upgrade -y

# 2. Docker镜像更新
docker-compose -f docker-compose.production.yml pull
docker-compose -f docker-compose.production.yml up -d

# 3. 数据库优化
# 执行VACUUM（SQLite）或分析表（PostgreSQL）

# 4. 密钥轮换
# 更新JWT_SECRET_KEY和SECRET_KEY

# 5. 灾难恢复演练
./scripts/disaster-recovery.sh --all
```

---

## 监控告警

### 监控架构

```
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│  Application │───▶│ Prometheus   │───▶│  Alertmanager│
│   Metrics    │    │  (Metrics)   │    │  (Alerts)    │
└──────────────┘    └──────────────┘    └──────┬───────┘
                                                │
                       ┌──────────────┐         │
                       │   Grafana    │◀────────┘
                       │(Dashboards)  │
                       └──────────────┘
```

### 关键指标阈值

| 指标 | 警告阈值 | 严重阈值 | 检查频率 |
|------|----------|----------|----------|
| CPU使用率 | > 80% | > 95% | 30s |
| 内存使用率 | > 80% | > 95% | 30s |
| 磁盘使用率 | > 85% | > 95% | 30s |
| API错误率 | > 1% | > 5% | 30s |
| API P95延迟 | > 500ms | > 1000ms | 30s |
| 服务可用性 | - | Down | 30s |

### 告警通知配置

```yaml
# Alertmanager配置示例
global:
  smtp_smarthost: 'smtp.example.com:587'
  smtp_from: 'alerts@formalmath.example.com'

route:
  group_by: ['alertname', 'severity']
  group_wait: 30s
  group_interval: 5m
  repeat_interval: 4h
  receiver: 'default'
  routes:
    - match:
        severity: critical
      receiver: 'pagerduty'
      continue: true
    - match:
        severity: warning
      receiver: 'email'

receivers:
  - name: 'default'
    email_configs:
      - to: 'ops@example.com'

  - name: 'pagerduty'
    pagerduty_configs:
      - service_key: '<pagerduty-key>'

  - name: 'email'
    email_configs:
      - to: 'team@example.com'
```

---

## 性能优化

### 性能基准

| 指标 | 目标值 | 测试方法 |
|------|--------|----------|
| 首页加载时间 | < 1s | Lighthouse |
| API响应时间(P95) | < 200ms | Locust |
| 并发用户数 | 1000 | Locust |
| 系统可用性 | 99.9% | 监控 |

### 性能调优参数

#### Nginx优化

```nginx
worker_processes auto;
worker_rlimit_nofile 65535;
worker_connections 2048;
keepalive_requests 1000;
```

#### Backend优化

```python
WORKERS = 8
WORKER_CONNECTIONS = 1000
KEEPALIVE_TIMEOUT = 65
```

#### Redis优化

```bash
maxmemory 4gb
maxmemory-policy allkeys-lru
maxclients 10000
tcp-keepalive 60
```

### 性能监控命令

```bash
# 实时性能监控
watch -n 1 'docker stats --no-stream'

# 查询性能分析
curl ])

# 慢查询分析
docker-compose logs backend | grep "Slow query"
```

---

## 故障处理

### 故障分级

| 级别 | 定义 | 响应时间 | 示例 |
|------|------|----------|------|
| P0 | 系统完全不可用 | 15分钟 | 服务宕机、数据丢失 |
| P1 | 核心功能受影响 | 1小时 | API错误率高、性能严重下降 |
| P2 | 非核心功能受影响 | 4小时 | 部分功能异常、告警误报 |
| P3 | 轻微问题 | 24小时 | 日志异常、优化建议 |

### 常见故障处理

#### 服务无法启动

```bash
# 1. 检查日志
docker-compose logs <service>

# 2. 检查端口占用
sudo netstat -tulpn | grep <port>

# 3. 检查磁盘空间
df -h

# 4. 检查内存
free -h

# 5. 重启服务
docker-compose restart <service>
```

#### 数据库连接失败

```bash
# 1. 检查数据库状态
docker-compose ps

# 2. 检查连接数
docker-compose exec redis redis-cli INFO clients

# 3. 检查数据库文件
ls -la data/

# 4. 恢复备份
./scripts/backup-scheduler.sh restore -d <date>
```

#### 高CPU使用率

```bash
# 1. 查看进程
htop

# 2. 查看容器资源
docker stats --no-stream

# 3. 重启高CPU服务
docker-compose restart <service>

# 4. 检查是否有死循环或大量请求
docker-compose logs <service> | grep -i error
```

#### 内存不足

```bash
# 1. 查看内存使用
free -h
docker stats --no-stream

# 2. 清理缓存
echo 3 > /proc/sys/vm/drop_caches

# 3. 重启服务释放内存
docker-compose restart

# 4. 增加swap（临时方案）
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

### 紧急联系人

| 角色 | 姓名 | 电话 | 邮箱 |
|------|------|------|------|
| 运维负责人 | | | |
| 技术负责人 | | | |
| 安全负责人 | | | |

---

## 备份恢复

### 备份策略

| 类型 | 频率 | 保留期 | 时间 |
|------|------|--------|------|
| 全量备份 | 每周日 | 30天 | 01:00 |
| 增量备份 | 每天 | 7天 | 01:30 |
| 数据库备份 | 每天 | 30天 | 02:00 |
| 配置备份 | 每次变更 | 90天 | 即时 |

### 手动备份

```bash
# 全量备份
./scripts/backup-scheduler.sh full

# 仅数据库
./scripts/backup-scheduler.sh database

# 仅配置文件
./scripts/backup-scheduler.sh config
```

### 恢复操作

```bash
# 列出可用备份
./scripts/backup-scheduler.sh list

# 恢复特定日期备份
./scripts/backup-scheduler.sh restore -d 20260401_120000

# 恢复最新备份
./scripts/backup-scheduler.sh restore -d latest
```

---

## 安全维护

### 安全加固脚本

```bash
# 完整安全检查
./scripts/security-hardening.sh full

# Docker安全检查
./scripts/security-hardening.sh docker

# SSL配置检查
./scripts/security-hardening.sh ssl

# 自动修复安全问题
./scripts/security-hardening.sh fix
```

### 安全更新流程

```bash
# 1. 创建备份
./scripts/backup-scheduler.sh full

# 2. 更新系统
sudo apt update && sudo apt upgrade -y

# 3. 更新Docker镜像
docker-compose -f docker-compose.production.yml pull

# 4. 重启服务
docker-compose -f docker-compose.production.yml up -d

# 5. 验证更新
./scripts/health-check.sh
```

---

## 灾难恢复

### 灾难恢复计划

#### RTO/RPO目标

- **RTO (恢复时间目标)**: < 30分钟
- **RPO (恢复点目标)**: < 24小时

#### 恢复场景

##### 场景1: 完整系统故障

```bash
# 1. 执行恢复脚本
./scripts/disaster-recovery.sh total

# 2. 验证恢复
curl
./scripts/health-check.sh
```

##### 场景2: 数据库损坏

```bash
# 1. 停止相关服务
docker-compose stop backend

# 2. 恢复数据库
./scripts/backup-scheduler.sh restore -d <date>

# 3. 重启服务
docker-compose start backend
```

##### 场景3: 配置错误

```bash
# 1. 恢复配置
git checkout <previous-commit>

# 2. 重启服务
docker-compose restart
```

### 灾难恢复演练

```bash
# 执行所有演练场景
./scripts/disaster-recovery.sh --all

# 模拟运行（不实际执行）
./scripts/disaster-recovery.sh --dry-run total

# 生成演练报告
./scripts/disaster-recovery.sh report
```

---

## 附录

### 快捷别名配置

```bash
# 添加到 ~/.bashrc
alias fm-status='cd /opt/formalmath-enhanced && docker-compose ps'
alias fm-logs='cd /opt/formalmath-enhanced && docker-compose logs -f --tail=100'
alias fm-restart='cd /opt/formalmath-enhanced && docker-compose restart'
alias fm-backup='cd /opt/formalmath-enhanced && ./scripts/backup-scheduler.sh full'
alias fm-health='cd /opt/formalmath-enhanced && ./scripts/health-check.sh'
alias fm-update='cd /opt/formalmath-enhanced && git pull && docker-compose up -d --build'
```

### 文档更新记录

| 版本 | 日期 | 更新内容 | 作者 |
|------|------|----------|------|
| v1.0.0 | 2026-04-03 | 初始版本 | - |
| v2.0.0 | 2026-04-04 | 添加性能优化和灾难恢复 | Production Team |

---

**注意**: 本手册应定期更新，确保与生产环境配置保持一致。
