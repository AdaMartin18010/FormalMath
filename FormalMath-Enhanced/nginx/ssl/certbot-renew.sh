#!/bin/bash
# Let's Encrypt 证书自动续期脚本

DOMAIN="formalmath.example.com"
WEBROOT="/var/www/certbot"
EMAIL="admin@example.com"
NGINX_CONTAINER="nginx"

# 创建 webroot 目录
mkdir -p $WEBROOT

# 申请/续期证书
certbot certonly \
    --webroot \
    --webroot-path $WEBROOT \
    --domain $DOMAIN \
    --agree-tos \
    --non-interactive \
    --email $EMAIL \
    --deploy-hook "docker exec $NGINX_CONTAINER nginx -s reload"

# 检查执行结果
if [ $? -eq 0 ]; then
    echo "[$(date)] 证书续期成功"
else
    echo "[$(date)] 证书续期失败"
    exit 1
fi
