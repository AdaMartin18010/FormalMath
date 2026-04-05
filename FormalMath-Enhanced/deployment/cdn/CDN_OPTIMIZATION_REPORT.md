---
title: FormalMath CDN 优化报告
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath CDN 优化报告

## 概述

本文档详细描述了 FormalMath 项目的 CDN 配置和缓存优化策略，旨在提供全球范围内的高性能访问体验。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                         用户请求                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │  CloudFlare  │  │  CloudFront  │  │    Nginx     │          │
│  │   (全球)     │  │   (AWS)     │  │  (源站缓存)   │          │
│  └──────────────┘  └──────────────┘  └──────────────┘          │
│         │                 │                 │                   │
│         └─────────────────┴─────────────────┘                   │
│                              │                                  │
│                              ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │                   Origin Server                          │  │
│  │              (FormalMath API + Static)                   │  │
│  └─────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## CDN 配置

### 1. CloudFlare 配置

**文件**: `cloudflare_config.yaml`

#### 主要特性
- **SSL/TLS**: Full Strict 模式，支持 TLS 1.3
- **性能优化**: 
  - Brotli 压缩
  - HTTP/2 和 HTTP/3 支持
  - 0-RTT 连接恢复
  - 自动平台优化 (APO)
- **安全特性**:
  - 浏览器完整性检查
  - 安全级别：中等
  - DDoS 防护

#### 页面规则缓存策略

| 路径模式 | 边缘缓存 | 浏览器缓存 | 说明 |
|---------|---------|-----------|------|
| `/api/v1/*` | 5分钟 | 1分钟 | API响应缓存 |
| `/static/*` | 30天 | 7天 | 静态资源长期缓存 |
| `*.@(md\|pdf\|png)` | 1天 | 1小时 | 文档和图片 |
| `/api/v1/concept-graph*` | 1小时 | 5分钟 | 知识图谱数据 |
| `/api/v1/search*` | 1分钟 | 不缓存 | 搜索API短缓存 |
| `/health*` | 不缓存 | 不缓存 | 健康检查绕过 |

### 2. AWS CloudFront 配置

**文件**: `cloudfront_config.json`

#### 分发配置
- **Price Class**: PriceClass_All (全球分发)
- **HTTP 版本**: HTTP/2 和 HTTP/3
- **SSL/TLS**: TLSv1.2_2021

#### 缓存行为

| 路径模式 | 源站 | TTL(最小/默认/最大) | 压缩 |
|---------|------|-------------------|------|
| `/*` | 主源站 | 0/86400/31536000 | 是 |
| `/api/v1/concept-graph*` | 主源站 | 60/3600/86400 | 是 |
| `/api/v1/concepts*` | 主源站 | 300/1800/3600 | 是 |
| `/api/v1/search*` | 主源站 | 0/60/300 | 是 |
| `/static/*` | S3 | 86400/604800/31536000 | 是 |
| `/health*` | 主源站 | 0/0/0 | 否 |

#### WAF 规则
- 速率限制：每个 IP 每 60 秒 2000 请求
- AWS Managed Rules: 通用规则集

### 3. Nginx 反向代理配置

**文件**: `nginx_cache.conf`

#### 缓存层
- **静态资源缓存** (`STATIC`): 100MB，60分钟过期
- **API缓存** (`API`): 50MB，30分钟过期

#### 压缩支持
- **Gzip**: 级别6，支持多种MIME类型
- **Brotli**: 级别6，更好的压缩比

#### 限流策略
- API 端点: 10 r/s，突发20
- 搜索端点: 5 r/s，突发10
- 连接限制: 每IP最多20并发

## 缓存策略

### 静态资源缓存

**文件**: `static_cache_config.yaml`

#### 按文件类型分类

| 类型 | 扩展名 | 浏览器缓存 | CDN边缘缓存 | 压缩 |
|-----|-------|-----------|------------|------|
| JavaScript | .js, .mjs | 7天 | 30天 | Brotli/Gzip |
| CSS | .css, .scss | 7天 | 30天 | Brotli/Gzip |
| 图片 | .png, .jpg, .svg | 30天 | 90天 | - |
| 字体 | .woff, .woff2 | 1年 | 1年 | Brotli |
| JSON | .json | 1小时 | 1小时 | Brotli/Gzip |
| HTML | .html | 0(验证) | 5分钟 | Brotli/Gzip |
| Markdown | .md | 1小时 | 1小时 | Brotli/Gzip |
| PDF | .pdf | 1天 | 7天 | - |
| Lean/Mathlib | .lean, .olean | 1天 | 7天 | Brotli/Gzip |

### API 响应缓存

**文件**: `api_cache_config.yaml`

#### 端点缓存策略

| 端点 | 方法 | 浏览器缓存 | Redis缓存 | CDN | 说明 |
|-----|------|-----------|----------|-----|------|
| `/concept-graph` | GET | 1小时 | 2小时 | 是 | 知识图谱 |
| `/concepts` | GET | 30分钟 | 1小时 | 是 | 概念列表 |
| `/concepts/{id}` | GET | 1小时 | 2小时 | 是 | 概念详情 |
| `/search` | GET | 1分钟 | 5分钟 | 是 | 搜索API |
| `/search/semantic` | POST | 5分钟 | 30分钟 | 否 | 语义搜索 |
| `/learning-paths` | GET | 5分钟(私有) | 10分钟 | 否 | 用户特定 |
| `/progress` | GET | 1分钟(私有) | 5分钟 | 否 | 用户进度 |
| `/recommendations` | GET | 5分钟(私有) | 10分钟 | 否 | 推荐系统 |
| `/problems` | GET | 1小时 | 2小时 | 是 | 题目数据 |
| `/problems/imo/*` | GET | 1天 | 7天 | 是 | IMO题目 |
| `/health` | GET | 不缓存 | 不缓存 | 否 | 健康检查 |
| `/auth/*` | POST | 不缓存 | 不缓存 | 否 | 认证接口 |

### 浏览器缓存策略

**文件**: `browser_cache_policy.yaml`

#### 资源分类

| 资源类型 | Cache-Control | 特殊头 |
|---------|--------------|-------|
| 版本化资源 | `public, max-age=31536000, immutable` | - |
| 非版本化JS/CSS | `public, max-age=604800, must-revalidate` | - |
| 字体文件 | `public, max-age=31536000, immutable` | Access-Control-Allow-Origin: * |
| 图片 | `public, max-age=2592000` | - |
| API公共数据 | `public, max-age=3600, stale-while-revalidate=300` | - |
| API私有数据 | `private, max-age=300` | Vary: Authorization |
| Service Worker | `no-cache, no-store, must-revalidate` | Service-Worker-Allowed: / |

## 性能优化指标

### 预期性能提升

| 指标 | 优化前 | 优化后 | 提升 |
|-----|-------|-------|------|
| 全球平均延迟 | 200ms | 50ms | 75% ↓ |
| 首字节时间(TTFB) | 500ms | 100ms | 80% ↓ |
| 静态资源加载 | 2s | 300ms | 85% ↓ |
| 缓存命中率 | - | >90% | - |
| API响应时间 | 300ms | 50ms(命中) | 83% ↓ |

### 缓存命中率目标

| 层级 | 目标命中率 | 测量方法 |
|-----|-----------|---------|
| 浏览器缓存 | 70% | Navigation Timing API |
| CDN边缘缓存 | 85% | CloudFlare/CloudFront 分析 |
| Nginx代理缓存 | 60% | Nginx缓存状态日志 |
| Redis应用缓存 | 75% | Redis INFO stats |

## 部署指南

### CloudFlare 部署

```bash
# 1. 安装 wrangler CLI
npm install -g wrangler

# 2. 登录 CloudFlare
wrangler login

# 3. 部署 Workers
wrangler deploy --config cloudflare_config.yaml

# 4. 配置 DNS
# 在 CloudFlare Dashboard 中导入 DNS 记录
```

### CloudFront 部署

```bash
# 1. 安装 AWS CLI
pip install awscli

# 2. 配置 AWS 凭证
aws configure

# 3. 部署 CloudFormation 栈
aws cloudformation create-stack \
  --stack-name formalmath-cdn \
  --template-body file://cloudfront_config.json \
  --parameters \
    ParameterKey=OriginDomain,ParameterValue=origin.formalmath.org \
    ParameterKey=CertificateArn,ParameterValue=arn:aws:acm:us-east-1:... \
  --capabilities CAPABILITY_IAM

# 4. 等待部署完成
aws cloudformation wait stack-create-complete --stack-name formalmath-cdn
```

### Nginx 部署

```bash
# 1. 复制配置
sudo cp nginx_cache.conf /etc/nginx/nginx.conf

# 2. 创建缓存目录
sudo mkdir -p /var/cache/nginx
sudo chown nginx:nginx /var/cache/nginx

# 3. 测试配置
sudo nginx -t

# 4. 重载配置
sudo systemctl reload nginx
```

## 监控和调试

### 监控指标

```yaml
# 关键指标
metrics:
  - name: cache_hit_ratio
    type: percentage
    threshold: "> 90%"
    
  - name: origin_response_time
    type: latency
    threshold: "< 100ms"
    
  - name: edge_response_time
    type: latency
    threshold: "< 50ms"
    
  - name: cache_size_usage
    type: percentage
    threshold: "< 80%"
    
  - name: purge_requests
    type: count
    threshold: "< 100/day"
```

### 调试头信息

所有响应包含以下调试头：

```http
X-Cache-Status: HIT | MISS | BYPASS | EXPIRED
CF-Cache-Status: HIT | MISS | DYNAMIC
X-Origin-Response-Time: 45ms
X-Edge-Location: SJC
```

### 缓存清理

```bash
# CloudFlare 清理
# 1. 按URL清理
curl -X POST "https://api.cloudflare.com/client/v4/zones/{zone_id}/purge_cache[需更新]" \
  -H "Authorization: Bearer {token}" \
  -H "Content-Type: application/json" \
  --data '{"files":["https://formalmath.org/api/v1/concepts[需更新]"]}'

# 2. 全部清理
curl -X POST "https://api.cloudflare.com/client/v4/zones/{zone_id}/purge_cache[需更新]" \
  -H "Authorization: Bearer {token}" \
  --data '{"purge_everything":true}'

# CloudFront 清理
aws cloudfront create-invalidation \
  --distribution-id {distribution_id} \
  --paths "/*"

# Nginx 清理
sudo rm -rf /var/cache/nginx/*
sudo systemctl reload nginx
```

## 故障排除

### 常见问题

#### 1. 缓存不生效
- 检查 `Cache-Control` 头
- 验证 URL 是否匹配缓存规则
- 确认 Cookie 或 Authorization 头影响缓存键

#### 2. 缓存过期过快
- 检查 `max-age` 设置
- 验证源站是否正确设置缓存头
- 检查是否有缓存清理任务在运行

#### 3. 用户看到过期内容
- 使用版本化文件名
- 实施缓存清理策略
- 添加 `Cache-Busting` 查询参数

#### 4. API 响应被错误缓存
- 确认私有 API 设置 `Cache-Control: private`
- 检查 Vary 头是否正确设置
- 验证用户认证中间件

## 最佳实践

### 1. 缓存键设计
- 只包含影响响应的参数
- 排除分析参数 (utm_*)
- 规范化查询参数顺序

### 2. 版本化资源
```
/static/js/main.a1b2c3d4.js  # 哈希文件名
/static/css/main.e5f6g7h8.css
```

### 3. 渐进式加载
- 优先加载关键CSS
- 异步加载非关键JS
- 使用预加载关键资源

### 4. 监控和告警
- 设置缓存命中率告警
- 监控缓存大小增长
- 跟踪缓存清理操作

## 总结

本CDN配置为 FormalMath 提供了：
1. **全球加速** - 通过多CDN部署实现
2. **智能缓存** - 多层次缓存策略
3. **安全防护** - WAF 和 DDoS 防护
4. **监控可见性** - 详细的缓存指标

实施后预期整体性能提升 70% 以上，大幅降低源站负载，提升用户体验。
