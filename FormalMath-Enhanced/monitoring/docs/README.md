# FormalMath-Enhanced 监控与日志系统

本文档介绍 FormalMath-Enhanced 项目的完整监控与日志收集系统。

## 系统架构

```
┌─────────────────────────────────────────────────────────────────┐
│                      FormalMath-Enhanced                        │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │   API 服务   │  │  学习系统   │  │  认知诊断   │             │
│  │   :8000     │  │   :8001     │  │   :8002     │             │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │
│         │                │                │                     │
│         └────────────────┴────────────────┘                     │
│                          │                                      │
│              ┌───────────┴───────────┐                         │
│              │      指标导出器        │                         │
│              │  /metrics 端点         │                         │
│              └───────────┬───────────┘                         │
└──────────────────────────┼──────────────────────────────────────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
           ▼               ▼               ▼
   ┌──────────────┐ ┌──────────────┐ ┌──────────────┐
   │ Prometheus   │ │   Grafana    │ │   ELK Stack  │
   │   :9090      │ │   :3000      │ │              │
   │              │ │              │ │  ES :9200    │
   │ 指标收集      │ │  可视化      │ │  Kibana:5601 │
   │ 告警规则      │ │  仪表盘      │ │  Logstash    │
   │ 数据存储      │ │              │ │  Filebeat    │
   └──────┬───────┘ └──────────────┘ └──────────────┘
          │
   ┌──────▼───────┐
   │ Alertmanager │
   │   :9093      │
   │              │
   │ 邮件通知      │
   │ Slack通知     │
   │ PagerDuty     │
   └──────────────┘
```

## 快速开始

### 1. 环境准备

确保已安装 Docker 和 Docker Compose：

```bash
docker --version
docker-compose --version
```

### 2. 配置环境变量

```bash
cp .env.example .env
# 编辑 .env 文件，填写必要的配置
```

### 3. 启动监控栈

```bash
# 启动所有服务
docker-compose up -d

# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f prometheus
docker-compose logs -f grafana
docker-compose logs -f elasticsearch
```

### 4. 访问监控界面

| 服务 | 地址 | 默认凭据 |
|------|------|---------|
| Grafana | http://localhost:3000 | admin / (配置文件中设置) |
| Prometheus | http://localhost:9090 | - |
| Alertmanager | http://localhost:9093 | - |
| Kibana | http://localhost:5601 | - |

## 监控组件详解

### Prometheus (指标收集)

**功能：**
- 收集所有服务的指标数据
- 存储时序数据（默认保留15天）
- 执行告警规则

**配置文件：**
- `prometheus/prometheus.yml` - 主配置
- `prometheus/rules/api_alerts.yml` - API 告警
- `prometheus/rules/system_alerts.yml` - 系统告警
- `prometheus/rules/business_alerts.yml` - 业务告警

**常用查询：**

```promql
# API 请求速率
sum(rate(http_requests_total[5m])) by (service)

# 95分位响应时间
histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))

# 错误率
sum(rate(http_requests_total{status=~"5.."}[5m])) / sum(rate(http_requests_total[5m]))

# CPU 使用率
100 - (avg by (instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)
```

### Grafana (可视化)

**预置仪表盘：**

1. **API 性能监控** (`api-performance-dashboard.json`)
   - 请求速率 (RPS)
   - 响应时间分布 (P50/P95/P99)
   - 错误率
   - HTTP 状态码分布

2. **基础设施监控** (`infrastructure-dashboard.json`)
   - CPU 使用率
   - 内存使用率
   - 磁盘使用率
   - 网络流量
   - 系统负载

3. **业务指标监控** (`business-dashboard.json`)
   - 活跃用户
   - 学习路径生成数
   - 认知诊断数
   - Lean4 编译统计
   - AI 形式化统计

**自定义仪表盘：**

1. 登录 Grafana (http://localhost:3000)
2. 点击左侧菜单 "+" -> "Dashboard"
3. 添加面板并选择 Prometheus 数据源
4. 编写 PromQL 查询
5. 保存仪表盘

### ELK Stack (日志收集)

**组件：**

- **Filebeat** - 日志收集器，部署在各服务主机上
- **Logstash** - 日志处理器，解析和过滤日志
- **Elasticsearch** - 日志存储和检索
- **Kibana** - 日志可视化和分析

**日志收集流程：**

```
应用日志 → Filebeat → Logstash → Elasticsearch → Kibana
```

**支持的日志类型：**

| 服务 | 日志路径 | 字段 |
|------|----------|------|
| API | `/var/log/formalmath/api/*.log` | request_id, method, path, status_code, duration |
| 学习系统 | `/var/log/formalmath/adaptive-learning/*.log` | user_id, action, result |
| 认知诊断 | `/var/log/formalmath/cognitive-diagnosis/*.log` | diagnosis_id, accuracy, duration |
| Lean4 | `/var/log/formalmath/lean4/*.log` | file, status, compile_duration |
| AI 形式化 | `/var/log/formalmath/ai-formalization/*.log` | request_id, model, tokens, cost |
| 知识图谱 | `/var/log/formalmath/knowledge-graph/*.log` | query_type, query_duration, results |

**常用 Kibana 搜索：**

```
# 搜索错误日志
level: ERROR

# 搜索特定服务的慢查询
service: api AND duration: > 1000

# 搜索 Lean4 编译错误
service: lean4 AND status: error

# 搜索特定用户的操作
user_id: 12345
```

### Alertmanager (告警通知)

**告警级别：**

| 级别 | 描述 | 响应时间 | 通知渠道 |
|------|------|---------|---------|
| Critical | 系统不可用/核心功能故障 | 立即 | 邮件 + Slack + PagerDuty |
| Warning | 性能下降/非核心故障 | 5分钟内 | 邮件 + Slack |
| Info | 业务指标异常 | 1小时内 | Slack |

**配置通知渠道：**

编辑 `alertmanager/alertmanager.yml` 并设置环境变量：

```bash
export SMTP_PASSWORD="your_smtp_password"
export SLACK_WEBHOOK_URL="https://hooks.slack.com/services/..."
export PAGERDUTY_SERVICE_KEY="your_pagerduty_key"
```

## 告警规则详解

### API 服务告警

| 告警名称 | 条件 | 持续时间 | 说明 |
|---------|------|---------|------|
| APIHighErrorRate | 错误率 > 5% | 2分钟 | 服务故障 |
| APIHighLatency | P95 响应时间 > 1s | 3分钟 | 性能下降 |
| APIDown | 服务无响应 | 1分钟 | 服务宕机 |
| APITrafficDrop | 流量降至30%以下 | 5分钟 | 流量异常 |

### 系统资源告警

| 告警名称 | 条件 | 持续时间 | 说明 |
|---------|------|---------|------|
| HighCPUUsage | CPU > 80% | 5分钟 | 资源不足 |
| HighMemoryUsage | 内存 > 85% | 5分钟 | 内存不足 |
| HighDiskUsage | 磁盘 > 85% | 5分钟 | 磁盘空间不足 |
| CriticalDiskUsage | 磁盘 > 95% | 2分钟 | 磁盘即将满 |

### 业务逻辑告警

| 告警名称 | 条件 | 持续时间 | 说明 |
|---------|------|---------|------|
| LearningPathGenerationFailure | 失败率 > 10% | 5分钟 | 学习功能故障 |
| Lean4CompilationFailure | 失败率 > 20% | 5分钟 | 编译问题 |
| AIFormalizationFailure | 失败率 > 30% | 10分钟 | AI 服务异常 |
| Mathlib4SyncDelayed | 超过24小时未同步 | 1小时 | 数据同步问题 |

## 日常运维

### 查看服务状态

```bash
# 所有服务状态
docker-compose ps

# 资源使用
docker stats

# 磁盘使用
docker system df -v
```

### 备份数据

```bash
# 备份 Prometheus 数据
docker run --rm -v formalmath_prometheus_data:/data -v $(pwd):/backup alpine tar czf /backup/prometheus-backup-$(date +%Y%m%d).tar.gz -C /data .

# 备份 Elasticsearch 快照
# 在 Kibana Dev Tools 中执行：
# PUT /_snapshot/backup_repo/snapshot_$(date +%Y%m%d)?wait_for_completion=true
```

### 更新配置

```bash
# 修改配置后重新加载
docker-compose restart prometheus
docker-compose restart alertmanager

# 热加载 Prometheus 配置
curl -X POST http://localhost:9090/-/reload
```

### 清理旧数据

```bash
# 清理 Elasticsearch 旧索引（保留30天）
curl -X DELETE "localhost:9200/formalmath-logs-$(date -d '30 days ago' +%Y.%m.%d)"

# 清理 Docker 日志
docker system prune -f
```

## 故障排查

### Prometheus 无法启动

```bash
# 检查配置文件语法
docker-compose logs prometheus
promtool check config prometheus/prometheus.yml

# 检查规则文件
promtool check rules prometheus/rules/*.yml
```

### Grafana 无法访问数据源

1. 检查网络连通性：
   ```bash
   docker exec formalmath-grafana ping prometheus
   ```

2. 检查数据源配置：
   ```bash
   docker-compose logs grafana
   ```

3. 验证 Prometheus 健康状态：
   ```bash
   curl http://localhost:9090/-/healthy
   ```

### Elasticsearch 无法启动

```bash
# 检查内存锁定
docker-compose logs elasticsearch

# 增加系统限制
sudo sysctl -w vm.max_map_count=262144
```

### 日志未收集

1. 检查 Filebeat 状态：
   ```bash
   docker-compose logs filebeat
   ```

2. 检查日志路径权限：
   ```bash
   ls -la /var/log/formalmath/
   ```

3. 验证 Logstash 处理：
   ```bash
   docker-compose logs logstash
   ```

## 扩展配置

### 添加新的监控目标

在 `prometheus/prometheus.yml` 中添加：

```yaml
scrape_configs:
  - job_name: 'new-service'
    static_configs:
      - targets: ['new-service:8080']
    metrics_path: /metrics
```

### 添加新的日志收集

在 `filebeat/filebeat.yml` 中添加：

```yaml
filebeat.inputs:
  - type: log
    enabled: true
    paths:
      - /var/log/formalmath/new-service/*.log
    fields:
      service: new-service
```

### 添加新的告警规则

在 `prometheus/rules/` 中创建新的规则文件：

```yaml
groups:
  - name: new_service_alerts
    rules:
      - alert: NewServiceDown
        expr: up{job="new-service"} == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "New Service is down"
```

## 安全建议

1. **启用认证：**
   - Grafana：配置强密码
   - Elasticsearch：启用 X-Pack 安全
   - Prometheus：使用反向代理

2. **网络安全：**
   - 使用防火墙限制端口访问
   - 配置 TLS/SSL 加密
   - 使用 VPN 访问管理界面

3. **数据保护：**
   - 定期备份监控数据
   - 加密敏感配置
   - 审计访问日志

## 参考资料

- [Prometheus 文档](https://prometheus.io/docs/)
- [Grafana 文档](https://grafana.com/docs/)
- [ELK Stack 文档](https://www.elastic.co/guide/index.html)
- [Alertmanager 文档](https://prometheus.io/docs/alerting/latest/alertmanager/)
