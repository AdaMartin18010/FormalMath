---
title: FormalMath API 安全快速参考
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API 安全快速参考

## 安全配置检查表

### 部署前必检项

```bash
# 1. 确认DEBUG已关闭
grep "DEBUG" .env  # 应为 false

# 2. 确认CORS来源已限制
grep "CORS_ORIGINS" .env  # 不应包含 "*"

# 3. 确认SSL证书有效
openssl x509 -in /etc/ssl/certs/formalmath.crt -noout -dates

# 4. 运行安全扫描
python security/security_scanner.py . --format text

# 5. 测试HTTPS
curl -I https://api.yourdomain.com/health
```

## 常用命令

### 安全扫描

```bash
# 快速扫描
python security/security_scanner.py . --format text

# 导出JSON报告
python security/security_scanner.py . -o security_report.json
```

### Docker部署

```bash
# 启动安全部署
docker-compose -f security/docker-compose.security.yml up -d

# 查看日志
docker-compose -f security/docker-compose.security.yml logs -f

# 停止服务
docker-compose -f security/docker-compose.security.yml down
```

### Nginx管理

```bash
# 测试配置
sudo nginx -t

# 重载配置
sudo nginx -s reload

# 查看访问日志
sudo tail -f /var/log/nginx/formalmath_access.log

# 查看错误日志
sudo tail -f /var/log/nginx/formalmath_error.log
```

## 安全配置参数

### 速率限制

| 级别 | 请求/分钟 | 适用场景 |
|------|-----------|----------|
| 普通API | 120 | 一般端点 |
| 搜索 | 60 | 搜索端点 |
| 匿名用户 | 30 | 未认证用户 |

### WAF规则

| 规则ID | 类型 | 动作 |
|--------|------|------|
| SQLI-001 | SQL注入 | 拦截 |
| XSS-001 | XSS攻击 | 拦截 |
| PT-001 | 路径遍历 | 拦截 |
| CI-001 | 命令注入 | 拦截 |

### 安全响应头

```
Strict-Transport-Security: max-age=63072000; includeSubDomains; preload
X-Content-Type-Options: nosniff
X-Frame-Options: DENY
X-XSS-Protection: 1; mode=block
Content-Security-Policy: default-src 'self';
Referrer-Policy: strict-origin-when-cross-origin
```

## 故障排查

### 问题：API返回403

```bash
# 检查WAF日志
docker logs formalmath_api | grep "WAF"

# 检查IP是否被阻止
docker logs formalmath_api | grep "blocked"
```

### 问题：CORS错误

```bash
# 检查CORS配置
curl -H "Origin: https://example.com" -I https://api.yourdomain.com/

# 查看响应头中的CORS信息
```

### 问题：SSL证书过期

```bash
# 检查证书有效期
openssl x509 -in /etc/ssl/certs/formalmath.crt -noout -enddate

# 续期证书 (Let's Encrypt)
sudo certbot renew
```

## 紧急响应

### 发现攻击时

1. 查看WAF拦截日志
2. 临时阻止IP
3. 分析攻击模式
4. 更新WAF规则

### 阻止可疑IP

```python
# 在main.py中添加
WAFMiddleware(
    blocked_ips=["192.168.1.100"]
)
```

### 关闭WAF（紧急情况）

```python
# 临时注释掉WAF中间件
# app.add_middleware(WAFMiddleware, ...)
```

## 联系支持

- 安全问题：security@formalmath.example.com
- 紧急联系：+86-xxx-xxxx-xxxx
