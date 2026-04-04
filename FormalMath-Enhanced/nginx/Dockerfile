# FormalMath Nginx 负载均衡器镜像

FROM nginx:alpine

# 安装额外模块
RUN apk add --no-cache \
    curl \
    wget \
    bind-tools \
    logrotate

# 创建必要目录
RUN mkdir -p /var/cache/nginx \
    /var/log/nginx \
    /var/www/certbot \
    /etc/nginx/ssl

# 复制配置文件
COPY nginx.conf /etc/nginx/nginx.conf
COPY conf.d/ /etc/nginx/conf.d/
COPY ssl/ /etc/nginx/ssl/

# 设置权限
RUN chown -R nginx:nginx /var/cache/nginx /var/log/nginx

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --quiet --tries=1 --spider http://localhost/nginx-health || exit 1

EXPOSE 80 443 8080

CMD ["nginx", "-g", "daemon off;"]
