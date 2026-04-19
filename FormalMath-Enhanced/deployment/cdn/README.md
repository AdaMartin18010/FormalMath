---
title: FormalMath CDN 与缓存配置
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath CDN 与缓存配置

## 项目概述

本目录包含 FormalMath 项目的完整 CDN 配置和缓存优化策略，支持多层级缓存架构，确保全球用户获得高性能访问体验。

## 配置清单

### 1. CDN 配置文件

| 文件 | 描述 | 用途 |
|-----|------|------|
| `cloudflare_config.yaml` | CloudFlare CDN 配置 | 全球加速、边缘缓存、Workers |
| `cloudfront_config.json` | AWS CloudFront 配置 | AWS 生态 CDN、WAF 防护 |
| `nginx_cache.conf` | Nginx 反向代理配置 | 源站缓存、负载均衡、压缩 |

### 2. 缓存策略配置

| 文件 | 描述 | 覆盖范围 |
|-----|------|---------|
| `static_cache_config.yaml` | 静态资源缓存策略 | JS/CSS/图片/字体/文档 |
| `api_cache_config.yaml` | API 响应缓存策略 | 知识图谱/搜索/用户数据 |
| `browser_cache_policy.yaml` | 浏览器缓存策略 | 客户端缓存控制 |

### 3. 应用层缓存

| 文件 | 描述 | 特性 |
|-----|------|------|
| `cache_middleware_update.py` | 增强版缓存中间件 | CDN友好头、标签管理 |
| `redis_cache_update.py` | 分层缓存管理器 | L1内存/L2Redis/L3CDN |

### 4. 部署与文档

| 文件 | 描述 | 用途 |
|-----|------|------|
| `deploy.sh` | 一键部署脚本 | 自动化部署所有配置 |
| `CDN_OPTIMIZATION_REPORT.md` | 详细优化报告 | 性能指标、架构设计 |
| `QUICKSTART.md` | 快速入门指南 | 快速部署和配置 |
| `README.md` | 本文件 | 配置索引和说明 |

## 快速开始

### 一键部署

```bash
cd deployment/cdn
chmod +x deploy.sh
./deploy.sh all
```

### 分步部署

详见 [QUICKSTART.md](./QUICKSTART.md)

## 缓存架构

```
┌─────────────────────────────────────────────────────────────┐
│                       客户端浏览器                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │  HTTP Cache  │  │ ServiceWorker│  │  LocalStorage│      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                        CDN 边缘层                            │
│  ┌─────────────────┐  ┌─────────────────┐                   │
│  │   CloudFlare    │  │  AWS CloudFront │                   │
│  │  (全球 300+ PoP)│  │ (AWS 区域边缘)   │                   │
│  └─────────────────┘  └─────────────────┘                   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                        源站缓存层                            │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                    Nginx 反向代理                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────┐  │   │
│  │  │ Static Cache │  │  API Cache   │  │  Gzip/   │  │   │
│  │  │    100MB     │  │    50MB      │  │  Brotli  │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────┘  │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                        应用缓存层                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │  L1 Memory   │  │   L2 Redis   │  │  L3 CDN API  │      │
│  │   (60s)      │  │   (1-24h)    │  │  (1h-30d)   │      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
└─────────────────────────────────────────────────────────────┘
```

## 缓存策略速查表

### 静态资源

| 资源类型 | 浏览器缓存 | CDN边缘缓存 | 压缩 |
|---------|-----------|------------|------|
| JS/CSS (版本化) | 1年 | 1年 | Brotli+Gzip |
| JS/CSS (普通) | 7天 | 30天 | Brotli+Gzip |
| 图片 | 30天 | 90天 | - |
| 字体 | 1年 | 1年 | Brotli |
| JSON数据 | 1小时 | 1小时 | Brotli+Gzip |

### API 端点

| 端点 | 浏览器 | Redis | CDN | 用户特定 |
|-----|-------|-------|-----|---------|
| `/concept-graph` | 1小时 | 2小时 | ✅ | ❌ |
| `/concepts` | 30分钟 | 1小时 | ✅ | ❌ |
| `/search` | 1分钟 | 5分钟 | ✅ | ❌ |
| `/progress` | 5分钟 | 10分钟 | ❌ | ✅ |
| `/learning-paths` | 5分钟 | 10分钟 | ❌ | ✅ |
| `/health` | 不缓存 | 不缓存 | ❌ | ❌ |

## 关键配置说明

### 1. CloudFlare 页面规则

```yaml
# 最高优先级
/api/v1/search* -> 1分钟边缘缓存
/static/* -> 30天边缘缓存
/health* -> 不缓存(bypass)
```

### 2. CloudFront 缓存行为

```json
{
  "/api/v1/concept-graph": {
    "TTL": "60/3600/86400",
    "Compress": true,
    "QueryString": true
  }
}
```

### 3. Nginx 缓存键

```nginx
proxy_cache_key "$scheme$request_method$host$request_uri$args";
```

### 4. 应用层缓存键

```python
# 包含版本和语言参数
cache_key = hashlib.md5(
    json.dumps({"args": args, "kwargs": kwargs}, sort_keys=True).encode()
).hexdigest()
```

## 性能目标

| 指标 | 目标值 | 测量方法 |
|-----|-------|---------|
| 全球平均延迟 | < 50ms | CDN 分析 |
| 缓存命中率 | > 90% | 缓存状态日志 |
| 首字节时间 | < 100ms | TTFB 监控 |
| 静态资源加载 | < 300ms | Navigation Timing |
| API 响应(命中) | < 50ms | 应用监控 |

## 部署检查清单

- [ ] DNS 记录配置正确
- [ ] SSL 证书已部署
- [ ] 源站健康检查通过
- [ ] 缓存头验证通过
- [ ] 缓存命中率监控
- [ ] 清理流程测试
- [ ] 故障转移测试
- [ ] 性能基线记录

## 监控和日志

### 关键日志位置

```
Nginx: /var/log/nginx/access.log
      /var/log/nginx/error.log
CloudFlare: Dashboard Analytics
CloudFront: S3 日志桶
Application: /var/log/formalmath/api.log
```

### 监控指标

```yaml
# 缓存命中率
nginx_cache_hit_ratio:
  query: 'sum(nginx_cache_hits) / sum(nginx_cache_requests)'
  threshold: "> 0.90"

# 响应时间
api_response_time:
  query: 'histogram_quantile(0.99, api_response_duration)'
  threshold: "< 100ms"
```

## 故障排除

### 常见问题

| 问题 | 可能原因 | 解决方案 |
|-----|---------|---------|
| 缓存不生效 | Cache-Control 头错误 | 检查响应头 |
| 命中率为0 | 缓存键不匹配 | 检查 URL 参数 |
| 过期内容 | TTL 过长 | 手动清除缓存 |
| API 数据泄露 | 私有数据被缓存 | 设置 private |

### 调试命令

```bash
# 检查缓存头
curl -sI https://api.formalmath.org/api/v1/concepts[需更新] | grep -i cache

# 测试缓存命中
curl -sI https://api.formalmath.org/api/v1/concepts[需更新] | grep -i x-cache

# 查看 Nginx 缓存状态
grep "cache" /var/log/nginx/access.log | tail -20

# 检查 Redis 缓存
redis-cli INFO stats
```

## 更新和维护

### 版本更新

1. 更新静态资源文件名(添加hash)
2. 部署新配置
3. 清理旧缓存
4. 监控缓存命中率

### 定期维护

- 每周: 检查缓存命中率
- 每月: 分析缓存大小
- 每季度: 优化缓存策略

## 安全考虑

- 用户数据使用 `Cache-Control: private`
- 认证端点禁用缓存
- 启用 WAF 防护
- 限制缓存清理权限
- 监控异常访问模式

## 联系和支持

- 查看详细文档: [CDN_OPTIMIZATION_REPORT.md](./CDN_OPTIMIZATION_REPORT.md)
- 快速部署指南: [QUICKSTART.md](./QUICKSTART.md)
- 问题反馈: 创建 Issue 或联系开发团队

---

**最后更新**: 2026-04-04

**版本**: 1.0.0
