---
title: FormalMath Interactive - 部署文档
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath Interactive - 部署文档

## 📋 目录

- [概述](#概述)
- [环境要求](#环境要求)
- [本地开发](#本地开发)
- [生产部署](#生产部署)
- [Docker 部署](#docker-部署)
- [CI/CD 配置](#cicd-配置)
- [故障排除](#故障排除)

---

## 概述

FormalMath Interactive 是 FormalMath 项目的交互式可视化界面，基于 React + TypeScript + Vite 构建。

### 部署方式

| 方式 | 适用场景 | 复杂度 |
|------|----------|--------|
| GitHub Pages | 静态站点，演示环境 | ⭐ |
| Docker | 独立部署，生产环境 | ⭐⭐ |
| Docker Compose | 完整栈部署，开发/测试 | ⭐⭐⭐ |
| 手动部署 | 自定义服务器 | ⭐⭐ |

---

## 环境要求

### 开发环境

- **Node.js**: >= 18.0.0
- **npm**: >= 9.0.0 或 **yarn**: >= 1.22.0
- **Git**: >= 2.30.0

### 生产环境

- **Web 服务器**: Nginx 1.20+ 或 Apache 2.4+
- **容器运行时**: Docker 20.10+ 和 Docker Compose 2.0+
- **操作系统**: Linux (推荐 Ubuntu 22.04 LTS)

---

## 本地开发

### 1. 克隆仓库

```bash
git clone https://github.com/formalmath/FormalMath.git
cd FormalMath/FormalMath-Interactive
```

### 2. 安装依赖

```bash
npm install
# 或
yarn install
# 或
pnpm install
```

### 3. 启动开发服务器

```bash
npm run dev
```

访问 

### 4. 构建生产版本

```bash
npm run build
```

构建产物位于 `dist/` 目录。

---

## 生产部署

### GitHub Pages 部署

#### 自动部署（推荐）

1. Fork 本仓库到你的 GitHub 账户
2. 进入仓库 **Settings > Pages**
3. 选择 **Source**: GitHub Actions
4. 推送代码到 `main` 分支，自动触发部署

#### 手动配置

```bash
# 安装 gh-pages
npm install -D gh-pages

# 修改 package.json
{
  "scripts": {
    "deploy": "gh-pages -d dist"
  }
}

# 部署
npm run build
npm run deploy
```

### 手动部署到服务器

```bash
# 1. 构建
npm run build

# 2. 上传文件到服务器
scp -r dist/* user@server:/var/www/formalmath/

# 3. 配置 Nginx（参见 nginx.conf）
sudo cp nginx.conf /etc/nginx/sites-available/formalmath
sudo ln -s /etc/nginx/sites-available/formalmath /etc/nginx/sites-enabled/
sudo nginx -t
sudo systemctl reload nginx
```

---

## Docker 部署

### 单容器部署

```bash
# 构建镜像
docker build -t formalmath-interactive:latest .

# 运行容器
docker run -d \
  --name formalmath-frontend \
  -p 80:80 \
  --restart unless-stopped \
  formalmath-interactive:latest

# 查看日志
docker logs -f formalmath-frontend
```

### Docker Compose 部署（完整栈）

```bash
# 启动所有服务
docker-compose up -d

# 查看服务状态
docker-compose ps

# 查看日志
docker-compose logs -f frontend

# 停止服务
docker-compose down

# 完全清理（包括数据卷）
docker-compose down -v
```

### 环境变量

| 变量 | 说明 | 默认值 |
|------|------|--------|
| `NODE_ENV` | 运行环境 | `production` |
| `VITE_API_URL` | 后端 API 地址 | `` |
| `VITE_APP_VERSION` | 应用版本 | `1.0.0` |
| `VITE_APP_BUILD_TIME` | 构建时间 | - |

---

## CI/CD 配置

### GitHub Actions 工作流

工作流文件: `.github/workflows/deploy.yml`

#### 触发条件

- 推送到 `main` 分支
- 手动触发 (`workflow_dispatch`)
- 每周一定期构建

#### 工作流步骤

1. **代码检出**: 获取最新代码
2. **依赖安装**: 缓存并安装 npm 依赖
3. **质量检查**: 类型检查、代码检查、单元测试
4. **构建**: 生成生产版本
5. **部署**: 推送到 GitHub Pages
6. **Docker**: 构建并推送 Docker 镜像
7. **发布**: 创建 GitHub Release (仅标签推送)

#### 必需 Secrets

| Secret | 说明 |
|--------|------|
| `GITHUB_TOKEN` | 自动提供，用于 Pages 部署 |
| `DOCKER_USERNAME` | Docker Hub 用户名 |
| `DOCKER_PASSWORD` | Docker Hub 密码/令牌 |
| `SLACK_WEBHOOK` | (可选) Slack 通知 Webhook |

---

## 故障排除

### 常见问题

#### 1. 构建失败

```bash
# 清除缓存
rm -rf node_modules dist
npm install
npm run build
```

#### 2. 路由 404

确保 Nginx 配置包含 SPA 回退:

```nginx
location / {
    try_files $uri $uri/ /index.html;
}
```

#### 3. API 请求失败

检查代理配置:

```nginx
location /api/ {
    proxy_pass ;
    proxy_set_header Host $host;
}
```

#### 4. 资源加载 404

确认 `base` 配置正确:

```javascript
// vite.config.ts
export default defineConfig({
  base: '/FormalMath/',  // 根据部署路径调整
})
```

### 日志查看

```bash
# Docker
docker logs formalmath-frontend

# Docker Compose
docker-compose logs -f frontend

# Nginx
sudo tail -f /var/log/nginx/formalmath-error.log
```

### 性能优化

1. **启用 Gzip**: 已配置，检查响应头 `Content-Encoding: gzip`
2. **缓存策略**: 静态资源缓存 1 年，HTML 不缓存
3. **CDN**: 推荐使用 Cloudflare 或类似服务
4. **资源压缩**: 构建时自动启用 Terser 压缩

---

## 安全建议

1. **HTTPS**: 生产环境必须启用 HTTPS
2. **CSP**: 添加内容安全策略头
3. **依赖更新**: 定期运行 `npm audit fix`
4. **容器安全**: 使用非 root 用户运行容器
5. **Secrets 管理**: 不在代码中硬编码敏感信息

---

## 联系与支持

- 📧 Email: team@formalmath.org
- 💬 Issues: https://github.com/formalmath/FormalMath/issues
- 📖 Wiki: https://github.com/formalmath/FormalMath/wiki

---

**版本**: 1.0.0  
**更新日期**: 2026-04-04
