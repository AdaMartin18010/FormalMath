---
title: FormalMath 运维手册
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 运维手册

## 目录

1. [系统概述](#系统概述)
2. [部署指南](#部署指南)
3. [日常运维](#日常运维)
4. [监控告警](#监控告警)
5. [故障处理](#故障处理)
6. [备份恢复](#备份恢复)
7. [安全维护](#安全维护)

---

## 系统概述

### 架构组件

- **Nginx**: 反向代理和静态文件服务
- **Backend**: FastAPI后端服务
- **Frontend**: React前端应用
- **Redis**: 缓存和消息队列
- **Celery**: 异步任务处理
- **Prometheus/Grafana**: 监控（可选）

### 目录结构

```
FormalMath-Enhanced/
├── api/                    # 后端API代码
├── nginx/                  # Nginx配置
├── scripts/                # 运维脚本
├── deployment/             # 部署配置
├── logs/                   # 日志目录
├── backups/                # 备份目录
├── docker-compose.production.yml
├── Dockerfile.backend.optimized
├── Dockerfile.frontend.optimized
└── .env.production
```

---

## 部署指南

### 环境准备

#### 系统要求

- **OS**: Ubuntu 20.04 LTS 或更高版本
- **CPU**: 4核心以上
- **内存**: 8GB以上
- **磁盘**: 100GB SSD
- **网络**: 公网IP，开放80/443端口

#### 依赖安装

```bash
# 更新系统
sudo apt update && sudo apt upgrade -y

# 安装Docker
curl -fsSL https://get.docker.com[需更新] | sh
sudo usermod -aG docker $USER

# 安装Docker Compose
sudo apt install -y docker-compose-plugin

# 安装其他工具
sudo apt install -y curl wget jq
```

### 生产部署

#### 1. 克隆代码

```bash
cd /opt
git clone https://github.com/your-org/formalmath-enhanced.git
cd formalmath-enhanced
```

#### 2. 配置环境变量

```bash
# 复制环境模板
cp .env.production.example .env.production

# 编辑配置
vim .env.production

# 关键配置项
SECRET_KEY=your-secure-random-secret-key
JWT_SECRET_KEY=your-jwt-secret-key
DATABASE_URL=sqlite:///app/data/formalmath.db
REDIS_PASSWORD=your-redis-password
```

#### 3. 配置SSL证书

```bash
# 使用Let's Encrypt（推荐）
./scripts/ssl-renew.sh init \
  -d formalmath.example.com,www.formalmath.example.com \
  -e admin@example.com

# 或使用自签名证书（测试环境）
./nginx/ssl/generate-self-signed.sh
```

#### 4. 启动服务

```bash
# 构建并启动
./scripts/deploy.sh start

# 带监控启动
./scripts/deploy.sh start -m
```

#### 5. 验证部署

```bash
# 健康检查
./scripts/health-check.sh

# 查看状态
./scripts/deploy.sh status
```

---

## 日常运维

### 常用命令

#### 服务管理

```bash
# 启动服务
./scripts/deploy.sh start

# 停止服务
./scripts/deploy.sh stop

# 重启服务
./scripts/deploy.sh restart

# 查看状态
./scripts/deploy.sh status

# 查看日志
./scripts/deploy.sh logs [service-name]
docker-compose logs -f backend
```

#### 数据库管理

```bash
# 初始化数据库
./scripts/database-migrate.sh init

# 执行迁移
./scripts/database-migrate.sh migrate

# 查看迁移状态
./scripts/database-migrate.sh status

# 备份数据库
./scripts/database-migrate.sh backup
```

#### 日志管理

```bash
# 轮转日志
./scripts/log-rotate.sh rotate

# 清理旧日志
./scripts/log-rotate.sh clean -d 30

# 查看日志大小
./scripts/log-rotate.sh size

# 生成报告
./scripts/log-rotate.sh report
```

### 定时任务

已配置的crontab任务：

```bash
# 数据库备份 - 每天凌晨2点
0 2 * * * /opt/formalmath-enhanced/scripts/database-migrate.sh backup

# 日志轮转 - 每天凌晨4点
0 4 * * * /opt/formalmath-enhanced/scripts/log-rotate.sh rotate

# 日志清理 - 每周日凌晨5点
0 5 * * 0 /opt/formalmath-enhanced/scripts/log-rotate.sh clean

# SSL续期检查 - 每天凌晨3点
0 3 * * * /opt/formalmath-enhanced/scripts/ssl-renew.sh renew

# 全量备份 - 每周日凌晨1点
0 1 * * 0 /opt/formalmath-enhanced/scripts/backup-scheduler.sh full

# 增量备份 - 每天凌晨1点30分
30 1 * * * /opt/formalmath-enhanced/scripts/backup-scheduler.sh incremental
```

---

## 监控告警

### 监控指标

#### 系统指标

- CPU使用率
- 内存使用率
- 磁盘使用率
- 网络流量

#### 应用指标

- 请求QPS
- 响应时间
- 错误率
- 活跃连接数

#### 业务指标

- 用户数
- 任务队列长度
- 缓存命中率

### 告警规则

| 指标 | 阈值 | 级别 | 通知方式 |
|------|------|------|----------|
| CPU使用率 | > 80% | 警告 | 邮件 |
| CPU使用率 | > 95% | 严重 | 短信+邮件 |
| 内存使用率 | > 80% | 警告 | 邮件 |
| 磁盘使用率 | > 85% | 警告 | 邮件 |
| 磁盘使用率 | > 95% | 严重 | 短信+邮件 |
| 服务不可用 | - | 严重 | 短信+邮件 |
| SSL证书过期 | < 7天 | 警告 | 邮件 |
| SSL证书过期 | < 3天 | 严重 | 短信+邮件 |

### 查看监控

```bash
# Prometheus


# Grafana

# 默认账号: admin/admin
```

---

## 故障处理

### 常见问题

#### 服务无法启动

```bash
# 1. 检查日志
docker-compose logs backend

# 2. 检查端口占用
sudo netstat -tulpn | grep 8000

# 3. 检查磁盘空间
df -h

# 4. 重启服务
./scripts/deploy.sh restart
```

#### 数据库连接失败

```bash
# 1. 检查数据库文件
ls -la data/formalmath.db

# 2. 检查权限
docker exec formalmath-backend ls -la /app/data/

# 3. 恢复备份
./scripts/database-migrate.sh restore -d 20240101_120000
```

#### 内存不足

```bash
# 1. 查看内存使用
free -h
docker stats --no-stream

# 2. 重启服务释放内存
./scripts/deploy.sh restart

# 3. 增加swap分区
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

#### 高CPU使用率

```bash
# 1. 查看进程
htop

# 2. 查看容器资源使用
docker stats --no-stream

# 3. 重启问题服务
docker-compose restart backend
```

### 紧急处理流程

1. **服务完全不可用**

   ```bash
   # 快速重启
   docker-compose restart

   # 如无效，重建容器
   docker-compose down
   docker-compose up -d
   ```

2. **数据损坏**

   ```bash
   # 立即停止服务
   docker-compose down

   # 恢复最近备份
   ./scripts/database-migrate.sh restore

   # 启动服务
   docker-compose up -d
   ```

3. **安全事件**

   ```bash
   # 隔离受影响容器
   docker-compose stop backend

   # 检查日志
   grep -i "error\|warning\|attack" logs/nginx/access.log

   # 运行安全检查
   ./scripts/security-hardening.sh full
   ```

---

## 备份恢复

### 备份策略

#### 全量备份（每周）

- 时间：每周日凌晨1点
- 内容：数据目录、配置文件、数据库
- 保留期：30天

#### 增量备份（每天）

- 时间：每天凌晨1点30分
- 内容：变化的数据文件
- 保留期：7天

#### 数据库备份（每天）

- 时间：每天凌晨2点
- 内容：完整数据库导出
- 保留期：30天

### 手动备份

```bash
# 全量备份
./scripts/backup-scheduler.sh full

# 数据库备份
./scripts/backup-scheduler.sh database

# 文件备份
./scripts/backup-scheduler.sh files
```

### 恢复操作

```bash
# 列出可用备份
./scripts/backup-scheduler.sh list

# 恢复全量备份
./scripts/backup-scheduler.sh restore -d 20240101_120000

# 恢复数据库
./scripts/database-migrate.sh restore
```

### 云存储同步

```bash
# 配置云存储
# 编辑 .env.production
S3_BUCKET=your-backup-bucket
S3_REGION=us-east-1
S3_ACCESS_KEY=your-access-key
S3_SECRET_KEY=your-secret-key

# 手动同步
./scripts/backup-scheduler.sh sync
```

---

## 安全维护

### 定期安全任务

#### 每周

- [ ] 检查安全日志
- [ ] 检查登录失败记录
- [ ] 验证备份完整性

#### 每月

- [ ] 运行安全检查脚本
- [ ] 更新系统和依赖
- [ ] 轮换密钥
- [ ] 检查SSL证书过期时间

#### 每季度

- [ ] 安全渗透测试
- [ ] 审查访问日志
- [ ] 更新防火墙规则
- [ ] 灾难恢复演练

### 安全脚本

```bash
# 完整安全检查
./scripts/security-hardening.sh full

# Docker安全检查
./scripts/security-hardening.sh docker

# SSL配置检查
./scripts/security-hardening.sh ssl

# 自动修复
./scripts/security-hardening.sh fix
```

### 更新升级

```bash
# 1. 备份数据
./scripts/backup-scheduler.sh full

# 2. 拉取最新代码
git pull origin main

# 3. 更新部署
./scripts/deploy.sh update

# 4. 验证更新
./scripts/health-check.sh
```

---

## 联系信息

| 角色 | 联系人 | 联系方式 |
|------|--------|----------|
| 运维负责人 | - | - |
| 安全负责人 | - | - |
| 开发团队 | - | - |

## 附录

### 快捷命令参考

```bash
# 快速查看状态
alias fm-status='cd /opt/formalmath-enhanced && ./scripts/deploy.sh status'

# 快速查看日志
alias fm-logs='cd /opt/formalmath-enhanced && docker-compose logs -f --tail=100'

# 快速重启
alias fm-restart='cd /opt/formalmath-enhanced && ./scripts/deploy.sh restart'

# 快速备份
alias fm-backup='cd /opt/formalmath-enhanced && ./scripts/backup-scheduler.sh full'
```

### 重要文件路径

```
配置文件: /opt/formalmath-enhanced/.env.production
日志目录: /opt/formalmath-enhanced/logs/
备份目录: /opt/formalmath-enhanced/backups/
数据目录: /opt/formalmath-enhanced/data/
SSL证书: /opt/formalmath-enhanced/nginx/ssl/
```
