---
title: FormalMath API 生产环境安全加固指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API 生产环境安全加固指南

## 概述

本文档提供 FormalMath API 生产环境的完整安全加固方案，涵盖 HTTPS/TLS、CORS、速率限制、WAF、安全扫描等方面。

## 1. HTTPS/TLS 配置

### 1.1 SSL证书配置

#### 使用 Let's Encrypt 免费证书

```bash
# 安装Certbot
sudo apt-get update
sudo apt-get install certbot python3-certbot-nginx

# 获取证书
sudo certbot --nginx -d api.formalmath.example.com

# 自动续期（默认已配置）
sudo certbot renew --dry-run
```

#### 自签名证书（测试环境）

```bash
# 生成私钥
openssl genrsa -out formalmath.key 4096

# 生成证书签名请求
openssl req -new -key formalmath.key -out formalmath.csr

# 生成自签名证书
openssl x509 -req -days 365 -in formalmath.csr -signkey formalmath.key -out formalmath.crt
```

### 1.2 Nginx SSL配置

参考 `nginx_ssl.conf` 文件，确保以下配置：

- 仅启用 TLS 1.2+
- 使用强密码套件
- 启用HSTS
- 配置OCSP Stapling

### 1.3 Python SSL配置

```python
from security.ssl_config import SSLConfig, get_ssl_uvicorn_config

# 创建SSL配置
ssl_config = SSLConfig(
    cert_file="/etc/ssl/certs/formalmath.crt",
    key_file="/etc/ssl/private/formalmath.key"
)

# 启动Uvicorn时启用HTTPS
import uvicorn
config = get_ssl_uvicorn_config(ssl_config)
uvicorn.run("main:app", host="0.0.0.0", port=443, **config)
```

## 2. CORS 安全策略

### 2.1 生产环境配置

编辑 `.env` 文件：

```env
# 生产环境 - 明确指定允许的源
CORS_ORIGINS=["https://formalmath.example.com", "https://app.formalmath.example.com"]
CORS_ALLOW_CREDENTIALS=true
CORS_ALLOW_METHODS=["GET", "POST", "PUT", "DELETE", "OPTIONS"]
CORS_ALLOW_HEADERS=["Content-Type", "Authorization", "X-Request-ID"]
```

### 2.2 CORS验证中间件

已在 `app/security/cors.py` 中配置，会自动：

- 验证Origin头的有效性
- 阻止null origin攻击
- 记录跨域请求

## 3. 速率限制配置

### 3.1 当前配置

已在 `main.py` 中配置基础速率限制：

```python
app.add_middleware(
    RateLimitMiddleware,
    requests_per_minute=120,
    burst_size=20,
    excluded_paths=["/health", "/docs", "/openapi.json", "/static"]
)
```

### 3.2 Redis-backed 速率限制（推荐生产环境）

```python
from app.middleware.rate_limit import UserBasedRateLimitMiddleware

app.add_middleware(
    UserBasedRateLimitMiddleware,
    anonymous_limit=30,
    authenticated_limit=120
)
```

### 3.3 Nginx 层速率限制

```nginx
# 定义限速区域
limit_req_zone $binary_remote_addr zone=api_limit:10m rate=10r/s;

# 应用限速
location / {
    limit_req zone=api_limit burst=20 nodelay;
    proxy_pass http://backend;
}
```

## 4. Web应用防火墙 (WAF)

### 4.1 内置WAF中间件

已在 `app/security/waf.py` 中实现，包含以下防护规则：

| 规则ID | 名称 | 严重级别 | 描述 |
|--------|------|----------|------|
| SQLI-001 | SQL Injection - Union Select | critical | 检测UNION SELECT注入 |
| SQLI-002 | SQL Injection - Comment | high | 检测SQL注释攻击 |
| XSS-001 | XSS - Script Tag | critical | 检测Script标签注入 |
| XSS-002 | XSS - Event Handler | high | 检测事件处理器注入 |
| PT-001 | Path Traversal | high | 检测路径遍历攻击 |
| CI-001 | Command Injection | critical | 检测命令注入 |
| FI-001 | Local File Inclusion | high | 检测文件包含攻击 |
| XML-001 | XXE Attack | critical | 检测XXE攻击 |
| INFO-001 | Sensitive File Access | medium | 检测敏感文件访问 |
| SCAN-001 | Vulnerability Scanner | medium | 检测漏洞扫描工具 |

### 4.2 启用WAF

在 `main.py` 中添加：

```python
from app.security.waf import WAFMiddleware

app.add_middleware(
    WAFMiddleware,
    blocked_ips=["192.168.1.100"],  # 黑名单IP
    max_violations=5,
    ip_block_duration=3600
)
```

### 4.3 ModSecurity WAF（可选）

Docker Compose中已配置ModSecurity，可通过环境变量调整：

```yaml
environment:
  - PARANOIA=2  # 0-4，数值越高越严格
  - ANOMALY_INBOUND=5
  - ANOMALY_OUTBOUND=4
```

## 5. 安全HTTP响应头

### 5.1 响应头配置

安全中间件自动添加以下响应头：

| 响应头 | 值 | 说明 |
|--------|-----|------|
| Strict-Transport-Security | max-age=63072000; includeSubDomains; preload | HSTS |
| X-Content-Type-Options | nosniff | 防止MIME嗅探 |
| X-Frame-Options | DENY | 防止点击劫持 |
| X-XSS-Protection | 1; mode=block | XSS保护 |
| Content-Security-Policy | 见配置 | 内容安全策略 |
| Referrer-Policy | strict-origin-when-cross-origin | Referrer策略 |
| Permissions-Policy | 见配置 | 权限策略 |

### 5.2 自定义CSP

```python
from app.security.headers import SecurityHeadersMiddleware

app.add_middleware(
    SecurityHeadersMiddleware,
    csp_policy="default-src 'self'; script-src 'self'; ..."
)
```

## 6. 输入验证

### 6.1 输入验证中间件

```python
from app.security.validation import InputValidationMiddleware

app.add_middleware(
    InputValidationMiddleware,
    max_body_size=10*1024*1024,  # 10MB
    max_json_depth=10,
    max_string_length=10000
)
```

### 6.2 参数验证

```python
from app.security.validation import ParameterValidationMiddleware

app.add_middleware(
    ParameterValidationMiddleware,
    max_param_length=100
)
```

## 7. 安全扫描

### 7.1 运行安全扫描

```bash
cd api/security
python security_scanner.py .. -o security_report.json
```

### 7.2 扫描内容

- 敏感信息泄露（密码、密钥、token）
- 不安全代码模式（eval、pickle、shell=True等）
- 危险文件（.env、私钥文件）
- 依赖漏洞
- 配置问题

### 7.3 CI/CD集成

```yaml
# .github/workflows/security.yml
name: Security Scan
on: [push, pull_request]
jobs:
  scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Run Security Scanner
        run: |
          pip install -r requirements.txt
          python api/security/security_scanner.py . --format text
```

## 8. Docker安全部署

### 8.1 使用安全Docker Compose配置

```bash
cd api/security
# 创建secrets目录
mkdir -p secrets
# 放入证书和密钥
cp /etc/ssl/certs/formalmath.crt secrets/ssl.crt
cp /etc/ssl/private/formalmath.key secrets/ssl.key
# 设置密码文件
echo "your_redis_password" > secrets/redis_password.txt

# 启动服务
docker-compose -f docker-compose.security.yml up -d
```

### 8.2 安全特性

- 容器以非特权模式运行
- 只读根文件系统
- 资源限制（CPU/内存）
- 健康检查
- 使用Docker Secrets管理敏感信息
- Fail2ban入侵防御

## 9. 生产环境检查清单

### 部署前检查

- [ ] SSL证书已正确配置且未过期
- [ ] DEBUG模式已禁用
- [ ] CORS来源已明确指定（无通配符）
- [ ] 速率限制已启用
- [ ] WAF规则已启用
- [ ] 安全响应头已配置
- [ ] 安全扫描无严重/高危问题
- [ ] 依赖已更新到最新版本
- [ ] 日志记录已启用
- [ ] 监控和告警已配置

### 运行时监控

- [ ] 异常请求监控
- [ ] 速率限制触发监控
- [ ] WAF拦截日志
- [ ] 错误率监控
- [ ] SSL证书过期提醒

## 10. 安全事件响应

### 10.1 发现安全问题时的步骤

1. **立即响应**
   - 记录事件时间、类型和影响范围
   - 临时阻止可疑IP
   - 保存相关日志

2. **分析调查**
   - 查看WAF拦截日志
   - 分析攻击模式和来源
   - 评估潜在影响

3. **修复加固**
   - 修复安全漏洞
   - 更新WAF规则
   - 加强访问控制

4. **复盘改进**
   - 更新安全策略
   - 完善监控告警
   - 安全培训

## 11. 安全更新流程

### 定期安全维护

- **每周**：查看安全扫描报告
- **每月**：更新依赖包
- **每季度**：安全渗透测试
- **每年**：SSL证书续期、安全策略审查

### 紧急安全更新

```bash
# 1. 更新依赖
pip list --outdated
pip install -U package_name

# 2. 重启服务
docker-compose -f docker-compose.security.yml restart

# 3. 验证更新
curl -s https://api.formalmath.example.com/health

# 4. 监控日志
docker logs -f formalmath_api
```

## 12. 联系与支持

- 安全问题报告：security@formalmath.example.com
- 紧急联系：+86-xxx-xxxx-xxxx
- 文档更新：docs.formalmath.example.com/security

---

**最后更新**: 2026-04-04
**版本**: 1.0
**分类**: 机密 - 内部使用
