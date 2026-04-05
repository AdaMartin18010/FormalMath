---
title: FormalMath Nginx 负载均衡配置
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath Nginx 负载均衡配置

生产级 Nginx 负载均衡配置，支持高并发、健康检查、会话保持、SSL终止和智能缓存。

## 特性

- ✅ **负载均衡**：加权轮询、最少连接、IP哈希
- ✅ **健康检查**：被动健康检查 + 主动健康检查支持
- ✅ **会话保持**：IP哈希确保用户会话一致性
- ✅ **SSL终止**：TLS 1.2/1.3、OCSP Stapling、HSTS
- ✅ **智能缓存**：多级缓存策略、缓存预热、后台更新
- ✅ **安全防护**：限流、连接限制、安全响应头
- ✅ **高可用**：备份服务器、优雅降级

## 快速开始

```bash
cd FormalMath-Enhanced/nginx

# Docker 启动
docker-compose up -d

# 测试访问
curl http://localhost/nginx-health
```

## 配置结构

| 文件 | 说明 |
|------|------|
| `nginx.conf` | 主配置文件 |
| `conf.d/upstream.conf` | 负载均衡配置 |
| `conf.d/health_check.conf` | 健康检查配置 |
| `conf.d/ssl.conf` | SSL/TLS 配置 |
| `conf.d/cache.conf` | 缓存策略配置 |

## 详细部署

参见 [DEPLOY.md](DEPLOY.md)

## 监控端点

| 端点 | 说明 |
|------|------|
| `http://localhost:8080/nginx_status` | Nginx 状态 |
| `http://localhost/nginx-health` | 健康检查 |
| `https://formalmath.example.com/health` | 应用健康检查 |
