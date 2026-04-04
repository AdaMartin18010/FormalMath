# ============================================
# FormalMath Interactive - 多阶段构建 Dockerfile
# ============================================

# -------------------- 阶段1: 依赖安装 --------------------
FROM node:18-alpine AS deps

# 设置工作目录
WORKDIR /app

# 安装系统依赖（用于原生模块编译）
RUN apk add --no-cache libc6-compat python3 make g++

# 复制依赖文件
COPY package.json package-lock.json* yarn.lock* pnpm-lock.yaml* ./

# 根据可用锁文件安装依赖
RUN \
  if [ -f yarn.lock ]; then yarn --frozen-lockfile; \
  elif [ -f package-lock.json ]; then npm ci; \
  elif [ -f pnpm-lock.yaml ]; then yarn global add pnpm && pnpm i --frozen-lockfile; \
  else npm i; \
  fi

# -------------------- 阶段2: 构建应用 --------------------
FROM node:18-alpine AS builder

WORKDIR /app

# 安装 git（用于获取版本信息）
RUN apk add --no-cache git

# 复制依赖
COPY --from=deps /app/node_modules ./node_modules

# 复制源代码
COPY . .

# 设置构建环境变量
ENV NODE_ENV=production
ENV VITE_APP_VERSION=${VITE_APP_VERSION:-1.0.0}
ENV VITE_APP_BUILD_TIME=${VITE_APP_BUILD_TIME:-unknown}

# 构建应用
RUN npm run build

# -------------------- 阶段3: 生产环境 --------------------
FROM nginx:1.25-alpine AS runner

# 安装安全更新
RUN apk upgrade --no-cache

# 创建非 root 用户
RUN addgroup --system --gid 1001 nodejs && \
    adduser --system --uid 1001 --ingroup nodejs nextjs

# 复制 Nginx 配置
COPY nginx.conf /etc/nginx/conf.d/default.conf

# 复制构建产物
COPY --from=builder --chown=nextjs:nodejs /app/dist /usr/share/nginx/html

# 创建必要的 Nginx 目录并设置权限
RUN mkdir -p /var/cache/nginx/client_temp && \
    mkdir -p /var/cache/nginx/proxy_temp && \
    mkdir -p /var/cache/nginx/fastcgi_temp && \
    mkdir -p /var/cache/nginx/uwsgi_temp && \
    mkdir -p /var/cache/nginx/scgi_temp && \
    mkdir -p /var/run && \
    touch /var/run/nginx.pid && \
    chown -R nextjs:nodejs /var/cache/nginx && \
    chown -R nextjs:nodejs /var/run/nginx.pid && \
    chown -R nextjs:nodejs /usr/share/nginx/html && \
    chown -R nextjs:nodejs /etc/nginx/conf.d && \
    chmod -R 755 /usr/share/nginx/html

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD wget --quiet --tries=1 --spider http://localhost:80/ || exit 1

# 暴露端口
EXPOSE 80

# 切换到非 root 用户
USER nextjs

# 启动 Nginx
CMD ["nginx", "-g", "daemon off;"]

# ============================================
# 标签信息
# ============================================
LABEL maintainer="FormalMath Team <team@formalmath.org>" \
      description="FormalMath Interactive - 数学知识图谱交互式可视化平台" \
      version="1.0.0"
