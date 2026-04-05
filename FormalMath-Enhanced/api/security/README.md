---
title: FormalMath API 安全模块
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API 安全模块

本目录包含 FormalMath API 的完整安全加固方案。

## 目录结构

```
security/
├── ssl_config.py              # SSL/TLS配置
├── nginx_ssl.conf             # Nginx HTTPS配置
├── docker-compose.security.yml # 安全部署配置
├── security_scanner.py        # 安全扫描工具
├── SECURITY_GUIDE.md          # 安全加固指南
├── SECURITY_HARDENING_REPORT.md  # 加固完成报告
├── security_scan_report.json  # 扫描报告
└── README.md                  # 本文件
```

## 快速开始

### 1. 启用安全中间件

安全中间件已在 `main.py` 中自动启用，无需额外配置。

### 2. 配置生产环境

编辑 `.env` 文件：

```env
DEBUG=false
CORS_ORIGINS=["https://yourdomain.com[需更新]"]
```

### 3. 配置HTTPS

#### 使用 Let's Encrypt

```bash
sudo certbot --nginx -d api.yourdomain.com
```

#### 使用自签名证书（测试）

```bash
openssl genrsa -out formalmath.key 4096
openssl req -new -key formalmath.key -out formalmath.csr
openssl x509 -req -days 365 -in formalmath.csr -signkey formalmath.key -out formalmath.crt
```

### 4. 配置Nginx

```bash
sudo cp nginx_ssl.conf /etc/nginx/conf.d/formalmath.conf
sudo nginx -t
sudo nginx -s reload
```

### 5. 运行安全扫描

```bash
python security_scanner.py .. --format text
```

### 6. Docker安全部署

```bash
# 准备密钥
mkdir -p secrets
cp /path/to/ssl.crt secrets/
cp /path/to/ssl.key secrets/
echo "your_password" > secrets/redis_password.txt

# 启动
docker-compose -f docker-compose.security.yml up -d
```

## 安全功能

### WAF防护

- SQL注入防护
- XSS攻击防护
- 路径遍历防护
- 命令注入防护
- XXE攻击防护
- 恶意User-Agent过滤

### 速率限制

- IP级限制
- 用户级限制
- 端点级限制
- Redis分布式支持

### 安全响应头

- Strict-Transport-Security (HSTS)
- X-Content-Type-Options
- X-Frame-Options
- X-XSS-Protection
- Content-Security-Policy
- Referrer-Policy

## 监控

### 查看WAF日志

```bash
docker logs formalmath_api | grep "WAF"
```

### 查看速率限制日志

```bash
docker logs formalmath_api | grep "Rate limit"
```

## 故障排除

### 问题：SSL证书错误

**解决**：检查证书路径和权限

```bash
sudo ls -la /etc/ssl/certs/
sudo ls -la /etc/ssl/private/
```

### 问题：CORS错误

**解决**：检查CORS_ORIGINS配置

```python
# 查看当前配置
curl https://api.yourdomain.com/[需更新] | jq
```

### 问题：WAF误拦截

**解决**：查看WAF日志，调整规则或添加白名单

```python
# 在main.py中调整
WAFMiddleware(
    excluded_ips=["192.168.1.100"]
)
```

## 参考

- [安全加固指南](SECURITY_GUIDE.md)
- [加固完成报告](SECURITY_HARDENING_REPORT.md)
