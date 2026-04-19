---
title: FormalMath-Enhanced 监控与日志系统 - 概览
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath-Enhanced 监控与日志系统 - 概览

## 📊 系统总览

本监控系统为 FormalMath-Enhanced 项目提供完整的可观测性解决方案，包括：

- **指标收集**：Prometheus + Node Exporter + cAdvisor
- **可视化**：Grafana 预置仪表盘
- **日志收集**：ELK Stack (Elasticsearch + Logstash + Kibana + Filebeat)
- **告警通知**：Alertmanager 多渠道告警

## 📁 文件结构

```
monitoring/
├── docker-compose.yml              # Docker Compose 主配置
├── .env.example                    # 环境变量模板
├── Makefile                        # 常用命令快捷方式
│
├── prometheus/                     # Prometheus 配置
│   ├── prometheus.yml              # 主配置文件
│   └── rules/                      # 告警规则
│       ├── api_alerts.yml          # API 服务告警
│       ├── system_alerts.yml       # 系统资源告警
│       └── business_alerts.yml     # 业务逻辑告警
│
├── grafana/                        # Grafana 配置
│   ├── provisioning/
│   │   ├── datasources/            # 数据源配置
│   │   │   └── datasources.yml
│   │   └── dashboards/             # 仪表盘配置
│   │       └── dashboards.yml
│   └── dashboards/                 # 预置仪表盘 JSON
│       ├── api-performance-dashboard.json
│       ├── infrastructure-dashboard.json
│       └── business-dashboard.json
│
├── alertmanager/                   # Alertmanager 配置
│   └── alertmanager.yml            # 告警路由和通知
│
├── elk/                            # ELK Stack 配置
│   ├── elasticsearch.yml           # ES 配置
│   ├── kibana.yml                  # Kibana 配置
│   ├── filebeat/
│   │   └── filebeat.yml            # 日志收集配置
│   └── logstash/
│       └── pipeline/
│           ├── logstash.conf       # 日志处理管道
│           └── ilm-policy.json     # 索引生命周期策略
│
├── scripts/                        # 实用脚本
│   ├── setup.sh                    # 安装脚本
│   └── health-check.sh             # 健康检查脚本
│
└── docs/                           # 文档
    ├── README.md                   # 完整使用文档
    └── TROUBLESHOOTING.md          # 故障排查指南
```

## 🚀 快速启动

```bash
# 1. 进入监控目录
cd FormalMath-Enhanced/monitoring

# 2. 配置环境变量
cp .env.example .env
# 编辑 .env 文件

# 3. 启动服务
make up
# 或
docker-compose up -d

# 4. 查看状态
make status
```

## 🌐 访问地址

启动后，可以通过以下地址访问监控界面：

| 服务 | 地址 | 用途 |
|------|------|------|
| **Grafana** |  | 可视化仪表盘 |
| **Prometheus** |  | 指标查询和告警状态 |
| **Alertmanager** |  | 告警管理和静默 |
| **Kibana** |  | 日志搜索和分析 |

## 📈 预置仪表盘

### 1. API 性能监控 (`api-performance-dashboard.json`)

- 请求速率 (RPS)
- 响应时间分布 (P50/P95/P99)
- 错误率 (5xx/4xx)
- HTTP 状态码分布
- 数据库查询时间

### 2. 基础设施监控 (`infrastructure-dashboard.json`)

- CPU 使用率
- 内存使用率
- 磁盘使用率
- 网络流量
- 系统负载
- 容器状态

### 3. 业务指标监控 (`business-dashboard.json`)

- 活跃用户统计
- 学习路径生成数
- 认知诊断数
- Lean4 编译统计
- AI 形式化统计
- 定理覆盖进度

## 🔔 告警规则

### API 告警 (`api_alerts.yml`)

| 告警名称 | 触发条件 | 级别 |
|---------|---------|------|
| APIHighErrorRate | 错误率 > 5% | Critical |
| APIHighLatency | P95 > 1s | Warning |
| APIDown | 服务无响应 | Critical |
| APITrafficDrop | 流量 < 30% | Warning |

### 系统告警 (`system_alerts.yml`)

| 告警名称 | 触发条件 | 级别 |
|---------|---------|------|
| HighCPUUsage | CPU > 80% | Warning |
| HighMemoryUsage | 内存 > 85% | Warning |
| HighDiskUsage | 磁盘 > 85% | Warning |
| CriticalDiskUsage | 磁盘 > 95% | Critical |

### 业务告警 (`business_alerts.yml`)

| 告警名称 | 触发条件 | 级别 |
|---------|---------|------|
| LearningPathGenerationFailure | 失败率 > 10% | Warning |
| Lean4CompilationFailure | 失败率 > 20% | Warning |
| AIFormalizationFailure | 失败率 > 30% | Warning |
| Mathlib4SyncDelayed | 24小时未同步 | Warning |

## 📝 日志收集

### 支持的服务

| 服务 | 日志路径 |
|------|----------|
| API | `/var/log/formalmath/api/*.log` |
| 自适应学习 | `/var/log/formalmath/adaptive-learning/*.log` |
| 认知诊断 | `/var/log/formalmath/cognitive-diagnosis/*.log` |
| 评估系统 | `/var/log/formalmath/evaluation-system/*.log` |
| Lean4 | `/var/log/formalmath/lean4/*.log` |
| AI 形式化 | `/var/log/formalmath/ai-formalization/*.log` |
| 知识图谱 | `/var/log/formalmath/knowledge-graph/*.log` |

### 日志处理流程

```
应用日志 → Filebeat 收集 → Logstash 解析 → Elasticsearch 存储 → Kibana 可视化
```

### 日志保留策略

- **热数据**：1天，高性能存储
- **温数据**：3天后，压缩存储
- **冷数据**：30天后，冻结存储
- **删除**：90天后自动删除

## 🛠️ 常用命令

```bash
# 服务管理
make up           # 启动所有服务
make down         # 停止所有服务
make restart      # 重启服务
make status       # 查看服务状态

# 日志查看
make logs                    # 查看所有日志
make logs-prometheus         # 仅查看 Prometheus 日志
make logs-grafana            # 仅查看 Grafana 日志
make logs-elk                # 仅查看 ELK 日志

# 配置管理
make reload                   # 热重载配置
make check-prometheus         # 检查 Prometheus 配置
make check-logstash           # 检查 Logstash 配置

# 数据管理
make backup                   # 备份数据
make clean                    # 清理所有数据（危险！）

# 健康检查
make health                   # 运行健康检查
./scripts/health-check.sh     # 详细健康检查
```

## 📞 告警通知

支持的告警渠道：

- **邮件**：SMTP 配置
- **Slack**：Webhook 配置
- **PagerDuty**：服务密钥配置
- **Webhook**：自定义回调

配置方式：编辑 `.env` 文件并重启 Alertmanager

## 🔧 扩展开发

### 添加新的监控目标

编辑 `prometheus/prometheus.yml`：

```yaml
scrape_configs:
  - job_name: 'new-service'
    static_configs:
      - targets: ['new-service:8080']
```

### 添加新的日志收集

编辑 `elk/filebeat/filebeat.yml`：

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

创建 `prometheus/rules/new_alerts.yml`：

```yaml
groups:
  - name: new_alerts
    rules:
      - alert: NewAlert
        expr: up{job="new-service"} == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "New Service is down"
```

## 📚 相关文档

- [详细使用文档](docs/README.md)
- [故障排查指南](docs/TROUBLESHOOTING.md)
- [Prometheus 文档](https://prometheus.io/docs/)[需更新]
- [Grafana 文档](https://grafana.com/docs/)[需更新]
- [ELK Stack 文档](https://www.elastic.co/guide/index.html)[需更新]

## ⚠️ 注意事项

1. **生产环境**请务必修改默认密码
2. **安全建议**启用 TLS/SSL 加密
3. **资源需求**至少 4GB 内存可用
4. **数据备份**定期备份重要监控数据
5. **网络配置**确保防火墙开放必要端口

---

*FormalMath-Enhanced 监控系统 v1.0*
