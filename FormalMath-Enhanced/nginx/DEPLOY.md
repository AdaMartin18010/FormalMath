# FormalMath Nginx 负载均衡部署文档

## 概述

本文档描述 FormalMath 项目的生产级 Nginx 负载均衡配置部署步骤。

## 架构组件

```
                    ┌─────────────────────────────────────┐
                    │           Nginx 负载均衡器           │
                    │  (SSL终止/负载均衡/缓存/健康检查)     │
                    └─────────────────────────────────────┘
                                      │
              ┌───────────────────────┼───────────────────────┐
              │                       │                       │
     ┌────────▼────────┐    ┌─────────▼──────────┐   ┌────────▼────────┐
     │  应用服务器组    │    │    API服务器组      │   │  WebSocket组   │
     │  10.0.1.10-12  │    │   10.0.1.20-22     │   │  10.0.1.30-31  │
     └─────────────────┘    └────────────────────┘   └─────────────────┘
```

## 快速部署

### 1. 环境准备

```bash
# 创建工作目录
mkdir -p /opt/formalmath-nginx
cd /opt/formalmath-nginx

# 创建必要的子目录
mkdir -p conf.d ssl cache logs www
```

### 2. 配置文件部署

```bash
# 复制所有配置文件
cp nginx.conf /opt/formalmath-nginx/
cp conf.d/* /opt/formalmath-nginx/conf.d/
```

### 3. SSL 证书配置

#### 方式一：自签名证书（测试环境）

```bash
cd /opt/formalmath-nginx/ssl
chmod +x generate-self-signed.sh
./generate-self-signed.sh
```

#### 方式二：Let's Encrypt 证书（生产环境）

```bash
# 安装 Certbot
apt-get update
apt-get install -y certbot

# 申请证书
certbot certonly --standalone -d formalmath.example.com

# 创建符号链接
ln -s /etc/letsencrypt/live/formalmath.example.com/fullchain.pem \
    /opt/formalmath-nginx/ssl/formalmath.crt
ln -s /etc/letsencrypt/live/formalmath.example.com/privkey.pem \
    /opt/formalmath-nginx/ssl/formalmath.key
```

### 4. Docker 部署

```bash
# 创建 Docker 网络
docker network create formalmath-network

# 启动服务
docker-compose up -d

# 查看状态
docker-compose ps
docker logs formalmath-nginx
```

### 5. 原生 Nginx 部署

```bash
# 安装 Nginx
apt-get update
apt-get install -y nginx

# 备份默认配置
mv /etc/nginx/nginx.conf /etc/nginx/nginx.conf.bak

# 复制配置
cp /opt/formalmath-nginx/nginx.conf /etc/nginx/
cp /opt/formalmath-nginx/conf.d/* /etc/nginx/conf.d/

# 创建缓存目录
mkdir -p /var/cache/nginx/formalmath /var/cache/nginx/static

# 测试配置
nginx -t

# 重载配置
systemctl reload nginx

# 设置开机启动
systemctl enable nginx
```

## 配置说明

### 负载均衡策略

| 上游组 | 算法 | 会话保持 | 说明 |
|--------|------|----------|------|
| formalmath_app | least_conn | 无 | 最少连接数 |
| formalmath_api | ip_hash | IP哈希 | 同一IP固定后端 |
| formalmath_ws | ip_hash | IP哈希 | WebSocket长连接 |
| formalmath_static | 轮询 | 无 | 静态资源 |

### 健康检查

- **被动检查**：通过 `max_fails` 和 `fail_timeout` 检测
- **主动检查**：需要 nginx_upstream_check_module（开源版）
- **检查端点**：`/health` 返回服务状态

### 缓存策略

| 内容类型 | 缓存时间 | 位置 |
|----------|----------|------|
| API 响应 | 5分钟 | /var/cache/nginx/api |
| 静态资源 | 7天 | /var/cache/nginx/static |
| 页面 | 60分钟 | /var/cache/nginx/pages |
| 微缓存 | 1秒 | 高并发动态内容 |

## 监控与维护

### 查看 Nginx 状态

```bash
# 基本状态
curl http://localhost:8080/nginx_status

# 活跃连接数
curl -s http://localhost:8080/nginx_status | head -1

# 缓存状态
curl -I https://formalmath.example.com/api/v1/concepts | grep X-Cache-Status
```

### 日志分析

```bash
# 实时查看访问日志
tail -f /var/log/nginx/access.log

# 分析错误日志
tail -f /var/log/nginx/error.log

# 查看慢请求
awk '{if ($NF > 1) print $0}' /var/log/nginx/access.log | tail -20
```

### 常用维护命令

```bash
# 测试配置
docker exec formalmath-nginx nginx -t

# 重载配置
docker exec formalmath-nginx nginx -s reload

# 清空缓存
rm -rf /var/cache/nginx/*

# 查看 upstream 状态
# 需要安装 nginx_upstream_check_module
curl http://localhost:8080/upstream_check
```

## 故障排除

### 问题一：502 Bad Gateway

**原因**：后端服务不可达

**解决**：
```bash
# 检查后端服务状态
curl http://10.0.1.10:8080/health

# 检查网络连通性
docker exec formalmath-nginx ping 10.0.1.10

# 查看 Nginx 错误日志
docker logs formalmath-nginx | grep error
```

### 问题二：SSL 证书错误

**原因**：证书配置不正确或过期

**解决**：
```bash
# 检查证书
docker exec formalmath-nginx openssl x509 -in /etc/nginx/ssl/formalmath.crt -text -noout

# 更新证书
certbot renew

# 重载 Nginx
docker exec formalmath-nginx nginx -s reload
```

### 问题三：缓存不生效

**原因**：缓存键配置错误或响应头禁止缓存

**解决**：
```bash
# 检查缓存目录权限
ls -la /var/cache/nginx/

# 检查响应头
curl -I https://formalmath.example.com/api/v1/concepts

# 清除缓存
rm -rf /var/cache/nginx/api/*
```

## 性能优化

### 内核参数优化

```bash
# /etc/sysctl.conf
net.core.somaxconn = 65535
net.ipv4.tcp_max_syn_backlog = 65535
net.ipv4.ip_local_port_range = 1024 65535
net.ipv4.tcp_tw_reuse = 1
net.ipv4.tcp_fin_timeout = 15
net.core.netdev_max_backlog = 65535
```

### 文件描述符限制

```bash
# /etc/security/limits.conf
nginx soft nofile 65535
nginx hard nofile 65535
```

## 安全加固

1. **限制访问状态页面**
   - 仅允许内网 IP 访问 `/nginx_status`

2. **隐藏 Nginx 版本**
   - 配置 `server_tokens off;`

3. **启用 WAF**
   - 建议配合 ModSecurity 使用

4. **DDoS 防护**
   - 已配置限流 (`limit_req`, `limit_conn`)

## 附录

### 配置文件结构

```
/opt/formalmath-nginx/
├── nginx.conf              # 主配置文件
├── docker-compose.yml      # Docker Compose 配置
├── Dockerfile              # 自定义镜像
├── DEPLOY.md              # 本部署文档
├── conf.d/
│   ├── upstream.conf      # 负载均衡配置
│   ├── health_check.conf  # 健康检查配置
│   ├── ssl.conf           # SSL 配置
│   └── cache.conf         # 缓存策略配置
├── ssl/
│   ├── formalmath.crt     # 证书
│   ├── formalmath.key     # 私钥
│   ├── dhparam.pem        # DH 参数
│   ├── generate-self-signed.sh  # 自签名证书脚本
│   └── certbot-renew.sh   # 证书续期脚本
├── cache/                 # 缓存目录
├── logs/                  # 日志目录
└── www/                   # 静态文件目录
```

### 参考文档

- [Nginx 官方文档](http://nginx.org/en/docs/)
- [Nginx 负载均衡指南](http://nginx.org/en/docs/http/load_balancing.html)
- [Mozilla SSL Configuration Generator](https://ssl-config.mozilla.org/)
- [Let's Encrypt 文档](https://letsencrypt.org/docs/)
