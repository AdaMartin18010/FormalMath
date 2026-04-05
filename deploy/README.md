---
title: FormalMath - 生产部署配置
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath - 生产部署配置

本目录包含FormalMath项目生产环境的完整部署配置和运维文档。

## 目录结构

```
deploy/
├── cert-manager/           # SSL证书自动管理
│   ├── cluster-issuer.yaml    # Let's Encrypt集群颁发者
│   └── certificates.yaml      # 证书资源配置
├── logging/                # 日志管理配置
│   ├── logrotate.conf         # 日志轮转配置
│   └── fluent-bit.conf        # Fluent Bit日志收集
├── monitoring/             # 监控告警配置
│   ├── prometheus-rules.yaml  # Prometheus告警规则
│   └── alertmanager-config.yaml  # Alertmanager配置
├── production/             # 生产环境配置
│   └── .env.production.template  # 环境变量模板
├── scripts/                # 部署脚本
│   ├── deploy.sh              # 主部署脚本
│   └── rollback.sh            # 回滚脚本
├── docs/                   # 运维文档
│   └── OPERATIONS_GUIDE.md    # 运维手册
├── PRODUCTION_CHECKLIST.md # 部署检查清单
└── README.md              # 本文件
```

## 快速开始

### 1. 环境准备

```bash
# 复制环境变量模板
cp production/.env.production.template production/.env.production

# 编辑环境变量
vim production/.env.production
```

### 2. 执行部署

```bash
# Docker Compose部署
./scripts/deploy.sh deploy -t docker -v v2.0.0

# Kubernetes部署
./scripts/deploy.sh deploy -t k8s -v v2.0.0
```

### 3. 健康检查

```bash
./scripts/deploy.sh health
```

## 配置说明

### 环境变量

生产环境的环境变量模板位于 `production/.env.production.template`，包含以下配置：

- **应用配置**: 应用名称、版本、调试模式等
- **数据库配置**: PostgreSQL连接字符串、连接池配置
- **Redis配置**: 缓存和消息队列配置
- **安全配置**: JWT、会话、CSRF等安全相关配置
- **日志配置**: 日志级别、格式、轮转策略
- **监控配置**: Prometheus、Sentry等监控配置

### SSL证书

使用cert-manager自动管理SSL证书：

```bash
# 安装cert-manager
kubectl apply -f https://github.com/cert-manager/cert-manager/releases/download/v1.13.0/cert-manager.yaml

# 应用集群颁发者
kubectl apply -f cert-manager/cluster-issuer.yaml

# 应用证书配置
kubectl apply -f cert-manager/certificates.yaml
```

### 日志管理

使用Fluent Bit收集日志：

```bash
# 启动Fluent Bit
docker run -d \
  --name fluent-bit \
  -v /var/log:/logs:ro \
  -v /var/lib/docker/containers:/var/lib/docker/containers:ro \
  -v $(pwd)/logging/fluent-bit.conf:/fluent-bit/etc/fluent-bit.conf:ro \
  fluent/fluent-bit:latest
```

### 监控告警

Prometheus告警规则已配置以下告警：

- **服务可用性**: 服务宕机、健康检查失败
- **性能告警**: 高延迟、高错误率
- **资源告警**: CPU、内存、磁盘使用率
- **数据库告警**: 连接数、慢查询、复制延迟
- **SSL证书告警**: 证书即将过期

## 运维命令

### 日常运维

```bash
# 查看服务状态
./scripts/deploy.sh status

# 查看日志
./scripts/deploy.sh logs -s backend

# 扩容
./scripts/deploy.sh scale -s backend -r 5

# 维护模式
./scripts/deploy.sh maintenance on
```

### 故障处理

```bash
# 回滚到上一个版本
./scripts/rollback.sh rollback

# 回滚到指定版本
./scripts/rollback.sh revert -v v1.9.0

# 查看可回滚版本
./scripts/rollback.sh list
```

## 检查清单

部署前请参考 [PRODUCTION_CHECKLIST.md](./PRODUCTION_CHECKLIST.md) 完成所有检查项。

## 文档

- [部署检查清单](./PRODUCTION_CHECKLIST.md)
- [运维手册](./docs/OPERATIONS_GUIDE.md)
- [应急方案详细手册](../00-应急方案详细手册.md)
- [上线检查清单与应急方案](../00-上线检查清单与应急方案.md)

## 联系信息

- 运维值班: ops@formalmath.org
- 技术负责人: tech@formalmath.org
- 应急响应: emergency@formalmath.org

---

**版本**: v2.0.0  
**最后更新**: 2026-04-04
