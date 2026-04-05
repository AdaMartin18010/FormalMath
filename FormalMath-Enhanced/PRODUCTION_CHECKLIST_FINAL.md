---
title: FormalMath 生产环境部署最终检查清单
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 生产环境部署最终检查清单

**版本**: v2.0.0  
**更新日期**: 2026-04-04  
**适用环境**: Production

---

## 部署前最终检查

### 1. 代码与配置检查 ✅

- [ ] 代码已通过所有测试
  ```bash
  cd api && python -m pytest tests/ -v --tb=short
  ```
- [ ] 配置文件语法检查通过
  ```bash
  docker-compose -f docker-compose.production.yml config
  ```
- [ ] 环境变量文件已正确配置
  ```bash
  # 检查必要的环境变量
  grep -E "^(SECRET_KEY|JWT_SECRET_KEY|DATABASE_URL)" .env.production
  ```
- [ ] 默认密钥已更换为随机强密钥
  ```bash
  # 生成新的密钥
  openssl rand -hex 32
  ```

### 2. 安全配置检查 🔒

#### 2.1 容器安全
- [ ] 容器以非root用户运行
- [ ] 容器资源限制已配置 (CPU/Memory)
- [ ] 只读根文件系统已启用
- [ ] 能力限制已配置 (cap_drop: ALL)
- [ ] 健康检查已配置

#### 2.2 网络安全
- [ ] SSL证书已配置并有效
- [ ] TLS 1.2+ 已启用
- [ ] HSTS已配置
- [ ] 安全响应头已配置
- [ ] Nginx限流已配置
- [ ] 防火墙规则已配置
  ```bash
  sudo ufw status verbose
  ```

#### 2.3 应用安全
- [ ] JWT密钥已更换
- [ ] 密码策略已配置
- [ ] CORS限制为生产域名
- [ ] API限流已启用
- [ ] 审计日志已配置

### 3. 性能优化检查 ⚡

#### 3.1 缓存配置
- [ ] Redis缓存已启用
- [ ] 缓存TTL已配置
- [ ] 连接池已优化
  - 数据库连接池: 20
  - Redis最大连接: 100

#### 3.2 数据库优化
- [ ] 数据库索引已创建
  ```bash
  # 执行索引创建
  python api/scripts/create_indexes.py
  ```
- [ ] 连接池配置已优化
- [ ] 慢查询日志已启用

#### 3.3 Nginx优化
- [ ] Worker进程数已优化
- [ ] 连接数限制已配置
- [ ] Gzip压缩已启用
- [ ] 静态文件缓存已配置
- [ ] 代理缓存已配置

### 4. 监控告警配置 📊

#### 4.1 基础监控
- [ ] Prometheus已配置
- [ ] Grafana已配置
- [ ] 健康检查端点正常
  ```bash
  curl http://localhost/health
  curl http://localhost/api/v1/health
  ```

#### 4.2 告警规则
- [ ] CPU使用率告警 (>80%)
- [ ] 内存使用率告警 (>85%)
- [ ] 磁盘使用率告警 (>85%)
- [ ] 服务不可用告警
- [ ] API错误率告警 (>5%)
- [ ] API响应时间告警 (P95>1s)
- [ ] SSL证书过期告警 (<7天)

#### 4.3 日志管理
- [ ] 日志轮转已配置
- [ ] 日志保留策略已设置
- [ ] 集中式日志收集已配置（可选）

### 5. 备份与恢复检查 💾

#### 5.1 备份配置
- [ ] 自动备份脚本已配置
- [ ] 备份目录已创建并挂载
  ```bash
  ls -la /opt/formalmath-enhanced/backups/
  ```
- [ ] 备份保留策略已配置 (30天)
- [ ] 备份加密已启用（推荐）
- [ ] 云存储同步已配置（可选）

#### 5.2 恢复测试
- [ ] 数据库恢复流程已验证
  ```bash
  ./scripts/disaster-recovery.sh --dry-run database
  ```
- [ ] 完整系统恢复流程已验证
  ```bash
  ./scripts/disaster-recovery.sh --dry-run total
  ```
- [ ] RTO目标已确认 (<30分钟)
- [ ] RPO目标已确认 (<24小时)

### 6. 负载测试验证 🚀

#### 6.1 性能基准
- [ ] 单用户响应时间 < 200ms
- [ ] 支持100并发用户
- [ ] 支持1000并发用户（P95 < 500ms）
- [ ] 错误率 < 1%

#### 6.2 负载测试执行
```bash
# 运行负载测试
cd testing
docker-compose -f docker-compose.load-test.yml up -d

# 访问Locust Web界面
open http://localhost:8089

# 设置参数：
# - Number of users: 1000
# - Spawn rate: 100
# - Host: http://nginx
```

#### 6.3 测试结果检查
- [ ] 平均响应时间 < 200ms
- [ ] P95响应时间 < 500ms
- [ ] 错误率 < 1%
- [ ] 系统资源使用正常
  - CPU < 80%
  - 内存 < 80%
  - 磁盘 I/O 正常

### 7. 灾难恢复演练 🛡️

#### 7.1 演练场景
- [ ] 完整系统故障恢复
  ```bash
  ./scripts/disaster-recovery.sh total
  ```
- [ ] 数据库损坏恢复
  ```bash
  ./scripts/disaster-recovery.sh database
  ```
- [ ] 服务降级演练
  ```bash
  ./scripts/disaster-recovery.sh degradation
  ```
- [ ] Redis故障恢复
  ```bash
  ./scripts/disaster-recovery.sh redis
  ```

#### 7.2 演练报告
- [ ] 所有场景RTO已记录
- [ ] 问题已记录并修复
- [ ] 恢复文档已更新

---

## 部署执行步骤

### 步骤1: 准备工作
```bash
# 1. 登录服务器
ssh user@production-server

# 2. 进入项目目录
cd /opt/formalmath-enhanced

# 3. 拉取最新代码
git pull origin main

# 4. 创建备份
./scripts/backup-scheduler.sh full
```

### 步骤2: 构建镜像
```bash
# 1. 构建生产镜像
docker-compose -f docker-compose.production.yml build

# 2. 验证镜像
docker images | grep formalmath

# 3. 安全扫描（可选）
docker run --rm -v /var/run/docker.sock:/var/run/docker.sock \
  aquasec/trivy image formalmath-backend:latest
```

### 步骤3: 启动服务
```bash
# 1. 停止旧版本
docker-compose -f docker-compose.production.yml down

# 2. 启动新版本
docker-compose -f docker-compose.production.yml up -d

# 3. 等待服务就绪
sleep 30

# 4. 检查服务状态
docker-compose -f docker-compose.production.yml ps
```

### 步骤4: 部署验证
```bash
# 1. 健康检查
./scripts/health-check.sh

# 2. API测试
curl -f http://localhost/api/v1/health
curl -f http://localhost/api/v1/concepts

# 3. 前端测试
curl -f http://localhost/

# 4. 日志检查
docker-compose -f docker-compose.production.yml logs --tail=100
```

### 步骤5: 监控确认
```bash
# 1. 检查资源使用
docker stats --no-stream

# 2. 检查告警状态
# 访问 Grafana: http://localhost:3000

# 3. 检查日志
./scripts/log-rotate.sh report
```

---

## 部署后检查

### 即时检查（部署后5分钟）
- [ ] 所有服务状态为 `Up`
- [ ] 健康检查端点返回200
- [ ] 无错误日志
- [ ] CPU/内存使用正常

### 短期检查（部署后1小时）
- [ ] 服务运行稳定
- [ ] 无异常告警
- [ ] 用户可正常访问
- [ ] 响应时间正常

### 长期检查（部署后24小时）
- [ ] 24小时无故障
- [ ] 监控数据完整
- [ ] 备份正常执行
- [ ] 日志轮转正常

---

## 回滚计划

### 触发条件
- 服务不可用 > 5分钟
- 错误率 > 10%
- 严重性能退化
- 安全事件

### 回滚步骤
```bash
# 1. 立即停止服务
docker-compose -f docker-compose.production.yml down

# 2. 恢复数据（如需要）
./scripts/backup-scheduler.sh restore -d <backup-date>

# 3. 切换到上一版本
git checkout <previous-commit>
docker-compose -f docker-compose.production.yml up -d

# 4. 验证回滚
./scripts/health-check.sh
```

---

## 签字确认

| 角色 | 姓名 | 签字 | 日期 |
|------|------|------|------|
| 项目经理 | | | |
| 技术负责人 | | | |
| 运维负责人 | | | |
| 安全负责人 | | | |

---

## 附录

### 快速命令参考
```bash
# 查看状态
./scripts/deploy.sh status

# 查看日志
docker-compose -f docker-compose.production.yml logs -f --tail=100

# 重启服务
./scripts/deploy.sh restart

# 紧急回滚
./scripts/deploy.sh rollback
```

### 重要联系信息
| 情况 | 联系人 | 联系方式 |
|------|--------|----------|
| 技术问题 | | |
| 安全事件 | | |
| 基础设施 | | |

---

**注意**: 此清单必须在每次生产部署前完成，并保留记录至少1年。
