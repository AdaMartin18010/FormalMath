---
title: FormalMath CDN 快速入门指南
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath CDN 快速入门指南

## 概述

本指南帮助您快速部署和配置 FormalMath 项目的 CDN 和缓存系统。

## 目录结构

```
deployment/cdn/
├── cloudflare_config.yaml      # CloudFlare CDN 配置
├── cloudfront_config.json      # AWS CloudFront 配置
├── static_cache_config.yaml    # 静态资源缓存策略
├── api_cache_config.yaml       # API 响应缓存策略
├── browser_cache_policy.yaml   # 浏览器缓存策略
├── nginx_cache.conf            # Nginx 反向代理配置
├── cache_middleware_update.py  # 增强版缓存中间件
├── redis_cache_update.py       # 分层缓存管理器
├── CDN_OPTIMIZATION_REPORT.md  # 详细优化报告
├── deploy.sh                   # 一键部署脚本
└── QUICKSTART.md              # 本文件
```

## 快速部署

### 1. 一键部署 (推荐)

```bash
cd deployment/cdn

# 部署所有 CDN 配置
./deploy.sh all

# 仅部署 Nginx
./deploy.sh nginx

# 仅部署 CloudFlare
./deploy.sh cloudflare

# 仅部署 CloudFront
./deploy.sh cloudfront
```

### 2. 分步部署

#### Nginx (必需)

```bash
# 1. 复制配置
sudo cp nginx_cache.conf /etc/nginx/nginx.conf

# 2. 创建缓存目录
sudo mkdir -p /var/cache/nginx/api /var/cache/nginx/static
sudo chown -R www-data:www-data /var/cache/nginx

# 3. 测试配置
sudo nginx -t

# 4. 重载配置
sudo systemctl reload nginx
```

#### CloudFlare (可选)

```bash
# 1. 安装 wrangler
npm install -g wrangler

# 2. 登录
wrangler login

# 3. 配置 DNS
# 在 CloudFlare Dashboard 中添加 DNS 记录

# 4. 部署 Workers
# 参考 cloudflare_config.yaml 中的 Workers 配置
```

#### AWS CloudFront (可选)

```bash
# 1. 配置 AWS 凭证
aws configure

# 2. 部署 CloudFormation 栈
aws cloudformation create-stack \
  --stack-name formalmath-cdn \
  --template-body file://cloudfront_config.json \
  --parameters \
    ParameterKey=OriginDomain,ParameterValue=your-origin.com \
    ParameterKey=CertificateArn,ParameterValue=arn:aws:acm:... \
  --capabilities CAPABILITY_IAM

# 3. 等待完成
aws cloudformation wait stack-create-complete \
  --stack-name formalmath-cdn
```

### 3. 更新 API 中间件

```bash
# 1. 备份原文件
cp api/app/cache/redis_cache.py api/app/cache/redis_cache.py.backup
cp api/app/middleware/etag.py api/app/middleware/etag.py.backup

# 2. 复制新文件
cp cache_middleware_update.py api/app/middleware/cdn_cache.py
cp redis_cache_update.py api/app/cache/tiered_cache.py

# 3. 更新 main.py 引入新中间件
# 参考 cache_middleware_update.py 顶部的导入示例
```

## 配置详解

### 静态资源缓存

```yaml
# 文件: static_cache_config.yaml

# JavaScript - 7天缓存
.js, .mjs:
  browser: 7天
  cdn: 30天
  compression: brotli + gzip

# 图片 - 30天缓存
.png, .jpg, .svg:
  browser: 30天
  cdn: 90天

# 字体 - 1年缓存
.woff, .woff2:
  browser: 1年
  cdn: 1年
  cors: enabled
```

### API 缓存

```yaml
# 文件: api_cache_config.yaml

# 知识图谱 - 可缓存1小时
/api/v1/concept-graph:
  browser: 1小时
  redis: 2小时
  cdn: 1小时

# 搜索 API - 短缓存
/api/v1/search:
  browser: 1分钟
  redis: 5分钟
  cdn: 1分钟

# 用户数据 - 不缓存
/api/v1/progress:
  private: true
  browser: 5分钟
  cdn: disabled
```

### 浏览器缓存

```yaml
# 文件: browser_cache_policy.yaml

# 版本化资源
*.[hash].js:
  Cache-Control: public, max-age=31536000, immutable

# API 响应
/api/v1/concepts:
  Cache-Control: public, max-age=1800, stale-while-revalidate=300
```

## 验证部署

### 1. 检查缓存头

```bash
# 测试 API 缓存
curl -sI https://api.formalmath.org/api/v1/concepts[需更新] | grep -i cache

# 预期输出:
# cache-control: public, max-age=1800, stale-while-revalidate=300
# cdn-cache-control: max-age=1800

# 测试静态资源
curl -sI https://cdn.formalmath.org/static/main.1234abcd.js[需更新] | grep -i cache

# 预期输出:
# cache-control: public, max-age=604800, immutable
```

### 2. 检查缓存命中

```bash
# 查看 X-Cache-Status 头
curl -sI https://api.formalmath.org/api/v1/concepts[需更新] | grep -i x-cache

# 预期:
# X-Cache-Status: HIT (命中) 或 MISS (未命中)
```

### 3. 运行验证脚本

```bash
./deploy.sh verify
```

## 缓存清理

### 清理全部缓存

```bash
./deploy.sh purge
```

### 清理特定 URL

```bash
# CloudFlare
curl -X POST "https://api.cloudflare.com/client/v4/zones/{zone_id}/purge_cache[需更新]" \
  -H "Authorization: Bearer {token}" \
  -H "Content-Type: application/json" \
  --data '{"files":["https://api.formalmath.org/api/v1/concepts[需更新]"]}'

# CloudFront
aws cloudfront create-invalidation \
  --distribution-id {distribution_id} \
  --paths "/*"

# Nginx
sudo rm -rf /var/cache/nginx/*
sudo systemctl reload nginx
```

### 通过标签清理 (高级)

```python
from api.app.cache.tiered_cache import tiered_cache

# 通过标签删除缓存
await tiered_cache.delete_by_tag("concepts-all")
await tiered_cache.delete_by_tag("imo-2024")
```

## 性能调优

### 1. 监控指标

```yaml
# 关键指标
- 缓存命中率: > 90%
- 平均响应时间: < 50ms (命中)
- 回源率: < 10%
- 缓存大小: < 80% 容量
```

### 2. 调整缓存 TTL

```yaml
# 高变化数据 - 短 TTL
/api/v1/stats:
  ttl: 300  # 5分钟

# 稳定数据 - 长 TTL
/api/v1/problems/imo/*:
  ttl: 86400  # 1天
```

### 3. 启用分层缓存

```python
from api.app.cache.tiered_cache import tiered_cached

@tiered_cached(l1_ttl=60, l2_ttl=3600)
async def get_concepts():
    # L1: 内存 60秒
    # L2: Redis 1小时
    return await db.query_concepts()
```

## 故障排除

### 问题: 缓存不生效

**检查清单:**
1. 检查 `Cache-Control` 响应头
2. 确认请求方法是 GET
3. 检查 Cookie 是否影响缓存
4. 验证 URL 是否匹配缓存规则

```bash
# 调试命令
curl -sv https://api.formalmath.org/api/v1/concepts[需更新] 2>&1 | grep -i cache
```

### 问题: 用户看到过期内容

**解决方案:**
1. 使用版本化文件名: `main.1234abcd.js`
2. 添加缓存清除策略
3. 使用 `stale-while-revalidate`

### 问题: API 响应被错误缓存

**检查:**
1. 确认设置了 `Cache-Control: private`
2. 检查 `Authorization` 头是否影响缓存
3. 验证 `Vary` 头设置

```python
# 正确配置示例
response.headers["cache-control"] = "private, max-age=300"
response.headers["vary"] = "Accept-Encoding, Authorization"
```

## 最佳实践

### 1. 资源版本化

```html
<!-- 推荐 -->
<script src="/static/js/main.a1b2c3d4.js"></script>

<!-- 不推荐 -->
<script src="/static/js/main.js?v=1.2.3"></script>
```

### 2. 渐进式加载

```html
<!-- 预加载关键资源 -->
<link rel="preload" href="/static/css/critical.css" as="style">
<link rel="preload" href="/static/js/main.js" as="script">

<!-- 预连接 -->
<link rel="preconnect" href="https://api.formalmath.org[需更新]">
<link rel="preconnect" href="https://cdn.formalmath.org[需更新]">
```

### 3. 错误处理

```python
# 缓存降级策略
try:
    result = await cache.get(key)
except Exception as e:
    logger.error(f"缓存错误: {e}")
    # 直接查询数据库
    result = await db.query()
```

## 参考文档

- [详细优化报告](./CDN_OPTIMIZATION_REPORT.md)
- [CloudFlare 文档](https://developers.cloudflare.com/)[需更新]
- [AWS CloudFront 文档](https://docs.aws.amazon.com/cloudfront/)[需更新]
- [Nginx 缓存指南](http://nginx.org/en/docs/http/ngx_http_proxy_module.html)[需更新]

## 支持

如有问题，请:
1. 查看详细优化报告
2. 检查日志文件 `/var/log/formalmath-cdn-deploy.log`
3. 联系开发团队
