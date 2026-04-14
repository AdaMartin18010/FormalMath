---
title: FormalMath - Docker生产环境部署指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath - Docker生产环境部署指南

本文档描述了如何使用Docker和Docker Compose部署FormalMath项目到生产环境。

## 📋 系统要求

- **Docker**: 20.10+
- **Docker Compose**: 2.0+
- **操作系统**: Linux (Ubuntu 20.04+ 推荐) / macOS / Windows (WSL2)
- **内存**: 最少 4GB RAM
- **磁盘**: 最少 10GB 可用空间

## 🏗️ 架构概览

```
                    ┌─────────────────┐
                    │     Nginx       │
                    │  (反向代理)      │
                    │   端口: 80/443   │
                    └────────┬────────┘
                             │
          ┌──────────────────┼──────────────────┐
          │                  │                  │
          ▼                  ▼                  ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│     Frontend    │ │     Backend     │ │     Redis       │
│   (React/Vite)  │ │   (FastAPI)     │ │    (缓存)       │
│    端口: 80     │ │   端口: 8000    │ │   端口: 6379    │
└─────────────────┘ └─────────────────┘ └─────────────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │  Celery Worker  │
                    │  (异步任务)      │
                    └─────────────────┘
```

## 🚀 快速开始

### 1. 克隆和进入项目目录

```bash
cd FormalMath-Enhanced
```

### 2. 配置环境变量

```bash
# 复制环境变量模板
cp api/.env.example api/.env

# 编辑 .env 文件，设置生产环境配置
vim api/.env
```

**关键配置项：**

```env
# 生产环境设置
DEBUG=false
APP_NAME="FormalMath API"
APP_VERSION="2.0.0"

# 数据库配置（使用SQLite或PostgreSQL）
DATABASE_URL=sqlite:///app/data/formalmath.db
# 或 PostgreSQL: postgresql://user:password@postgres:5432/formalmath

# Redis配置
REDIS_HOST=redis
REDIS_PORT=6379
REDIS_DB=0

# Celery配置
CELERY_BROKER_URL=redis://redis:6379/1
CELERY_RESULT_BACKEND=redis://redis:6379/2

# CORS配置（生产环境限制来源）
CORS_ORIGINS=["https://yourdomain.com[需更新]"]
```

### 3. 构建和启动服务

```bash
# 构建所有镜像
docker-compose build

# 启动所有服务（后台运行）
docker-compose up -d

# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f
```

### 4. 验证部署

```bash
# 健康检查
curl

# API文档
curl

# 前端页面
open http://localhost[需更新]
```

## 🔧 高级配置

### SSL/TLS 配置

1. **准备SSL证书：**

```bash
mkdir -p ssl
cp your-cert.pem ssl/cert.pem
cp your-key.pem ssl/key.pem
```

1. **启用HTTPS配置：**
编辑 `nginx.conf`，取消HTTPS服务器部分的注释。

2. **HTTP重定向到HTTPS：**
在nginx.conf中取消HTTP服务器中的重定向配置注释。

### 环境配置文件

创建 `docker-compose.override.yml` 用于本地开发覆盖：

```yaml
version: '3.8'
services:
  backend:
    volumes:
      - ./api:/app
    environment:
      - DEBUG=true
  frontend:
    ports:
      - "3000:3000"
    command: npm run dev
```

### 数据库迁移

如果使用PostgreSQL，添加迁移服务：

```bash
# 在docker-compose.yml中添加
  db-migrate:
    build:
      context: .
      dockerfile: Dockerfile.backend
    command: alembic upgrade head
    environment:
      - DATABASE_URL=${DATABASE_URL}
    depends_on:
      - postgres
```

## 📊 监控和日志

### 启用监控栈

```bash
# 启动包含Prometheus和Grafana的服务
docker-compose --profile monitoring up -d

# 访问 Grafana:
# 默认账号: admin/admin

# 访问 Prometheus:
```

### 日志管理

```bash
# 查看特定服务日志
docker-compose logs -f backend

# 查看最后100行
docker-compose logs --tail=100 backend

# 导出日志
docker-compose logs backend > backend.log

# 清理日志
docker-compose logs --tail=0 backend > /dev/null
```

## 🔄 更新部署

### 无停机更新

```bash
# 1. 拉取最新代码
git pull origin main

# 2. 重新构建镜像
docker-compose build

# 3. 滚动更新（无停机）
docker-compose up -d --no-deps --build backend
docker-compose up -d --no-deps --build frontend

# 4. 验证新版本
curl
```

### 数据备份

```bash
# 备份SQLite数据库
docker-compose exec backend cp /app/data/formalmath.db /app/data/formalmath.db.backup.$(date +%Y%m%d)

# 备份Redis数据
docker-compose exec redis redis-cli SAVE
docker cp formalmath-redis:/data/dump.rdb ./backup/redis-$(date +%Y%m%d).rdb
```

### 回滚

```bash
# 查看历史镜像
docker images | grep formalmath

# 回滚到特定版本
docker-compose up -d --no-deps backend=<previous-image-tag>
```

## 🛠️ 故障排除

### 常见问题

#### 1. 服务无法启动

```bash
# 检查端口占用
netstat -tuln | grep -E '80|443|8000|6379'

# 查看详细日志
docker-compose logs --no-color backend
```

#### 2. 数据库连接错误

```bash
# 检查数据卷权限
docker-compose exec backend ls -la /app/data

# 重置数据库（谨慎使用）
docker-compose down -v
docker-compose up -d
```

#### 3. Redis连接失败

```bash
# 检查Redis状态
docker-compose exec redis redis-cli ping

# 查看Redis日志
docker-compose logs redis
```

#### 4. 前端静态文件404

```bash
# 检查前端构建
docker-compose exec frontend ls -la /usr/share/nginx/html

# 重新构建前端
docker-compose up -d --build frontend
```

### 性能优化

#### 调整工作进程数

在 `Dockerfile.backend` 中修改：`--workers 4`

根据CPU核心数调整：workers = 2 × CPU核心数 + 1

#### Redis性能调优

编辑 `docker-compose.yml` 中的Redis配置：

```yaml
command: redis-server --appendonly yes --maxmemory 1gb --maxmemory-policy allkeys-lru
```

## 🔒 安全建议

1. **使用非root用户运行容器** ✅ 已配置
2. **限制容器资源使用** ✅ 已配置
3. **定期更新基础镜像**
4. **启用防火墙，只开放必要端口**
5. **使用Docker Secrets管理敏感信息**
6. **启用SSL/TLS加密传输**

### 安全扫描

```bash
# 扫描镜像漏洞
docker scan formalmath-backend:latest
docker scan formalmath-frontend:latest
```

## 📦 生产环境检查清单

- [ ] 环境变量配置正确
- [ ] SSL证书已配置
- [ ] 数据库连接正常
- [ ] Redis缓存正常
- [ ] 健康检查通过
- [ ] 日志系统正常
- [ ] 备份策略已制定
- [ ] 监控告警已配置
- [ ] 防火墙规则已设置
- [ ] 域名解析正确

## 📚 相关文档

- [FastAPI部署文档][https://fastapi.tiangolo.com/deployment/](需更新)
- [Docker Compose文档][https://docs.docker.com/compose/](需更新)
- [Nginx配置指南][https://nginx.org/en/docs/](需更新)
- [Redis持久化][https://redis.io/docs/manual/persistence/](需更新)

## 🤝 支持

如有问题，请查看：

1. 服务日志：`docker-compose logs`
2. 项目文档：`README.md`
3. 提交Issue到项目仓库

---

**版本**: 1.0.0
**最后更新**: 2026-04-04
