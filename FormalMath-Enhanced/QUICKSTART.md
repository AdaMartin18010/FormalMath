# FormalMath 快速开始指南

## 一键部署

### 1. 环境准备

确保服务器满足以下条件：
- Ubuntu 20.04+ / CentOS 7+
- Docker 24.0+
- Docker Compose 2.0+
- 4核CPU / 8GB内存 / 100GB磁盘

### 2. 快速部署

```bash
# 克隆项目
git clone https://github.com/your-org/formalmath-enhanced.git
cd formalmath-enhanced

# 运行部署前检查
./scripts/pre-deploy-check.sh

# 配置环境变量
cp .env.production.example .env.production
# 编辑 .env.production，设置必要的配置

# 启动服务
docker-compose -f docker-compose.production.yml up -d

# 验证部署
./scripts/health-check.sh
```

## 常用命令速查

### 服务管理
```bash
# 启动
./scripts/deploy.sh start

# 停止
./scripts/deploy.sh stop

# 重启
./scripts/deploy.sh restart

# 查看状态
./scripts/deploy.sh status

# 查看日志
./scripts/deploy.sh logs [service-name]
```

### 数据库管理
```bash
# 初始化
./scripts/database-migrate.sh init

# 备份
./scripts/database-migrate.sh backup

# 恢复
./scripts/database-migrate.sh restore -d 20240101_120000
```

### SSL证书
```bash
# 申请证书
./scripts/ssl-renew.sh init -d your-domain.com -e admin@your-domain.com

# 续期检查
./scripts/ssl-renew.sh renew

# 查看状态
./scripts/ssl-renew.sh check
```

### 备份管理
```bash
# 全量备份
./scripts/backup-scheduler.sh full

# 查看备份
./scripts/backup-scheduler.sh list

# 查看状态
./scripts/backup-scheduler.sh status
```

### 日志管理
```bash
# 轮转日志
./scripts/log-rotate.sh rotate

# 查看大小
./scripts/log-rotate.sh size

# 清理旧日志
./scripts/log-rotate.sh clean -d 30
```

### 安全检查
```bash
# 完整检查
./scripts/security-hardening.sh full

# 自动修复
./scripts/security-hardening.sh fix
```

## 访问地址

部署完成后，可通过以下地址访问：

| 服务 | 地址 |
|------|------|
| 主站 | http://your-domain.com |
| API | http://your-domain.com/api/v1 |
| API文档 | http://your-domain.com/docs |
| 监控(Prometheus) | http://your-domain.com:9090 |
| 监控(Grafana) | http://your-domain.com:3000 |

## 故障排查

### 服务无法启动
```bash
# 查看日志
docker-compose logs -f

# 检查端口
sudo netstat -tulpn | grep 8000

# 检查磁盘空间
df -h
```

### 数据库问题
```bash
# 检查数据库连接
docker-compose exec backend python -c "from database import check_connection; check_connection()"

# 重置数据库（危险！）
./scripts/database-migrate.sh reset
```

### SSL问题
```bash
# 检查证书
openssl x509 -in nginx/ssl/formalmath.crt -text -noout

# 重新申请证书
./scripts/ssl-renew.sh init -d your-domain.com -e admin@your-domain.com
```

## 获取帮助

- 查看完整文档：[OPERATIONS_MANUAL.md](OPERATIONS_MANUAL.md)
- 生产检查清单：[PRODUCTION_CHECKLIST.md](PRODUCTION_CHECKLIST.md)
- 部署优化总结：[DEPLOYMENT_OPTIMIZATION_SUMMARY.md](DEPLOYMENT_OPTIMIZATION_SUMMARY.md)
