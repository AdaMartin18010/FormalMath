---
title: FormalMath Kubernetes 部署文档
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath Kubernetes 部署文档

本文档描述如何在 Kubernetes 集群上部署 FormalMath 应用。

## 目录

- [架构概览](#架构概览)
- [前置条件](#前置条件)
- [快速开始](#快速开始)
- [详细部署](#详细部署)
- [配置说明](#配置说明)
- [监控和日志](#监控和日志)
- [故障排除](#故障排除)

## 架构概览

```
┌─────────────────────────────────────────────────────────────────┐
│                         Ingress                                 │
│              formalmath.example.com                             │
│              api.formalmath.example.com                         │
└─────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┴───────────────┐
                │                               │
        ┌───────▼────────┐              ┌───────▼────────┐
        │   Frontend     │              │    Backend     │
        │   Service      │              │    Service     │
        │   (ClusterIP)  │              │   (ClusterIP)  │
        └───────┬────────┘              └───────┬────────┘
                │                               │
        ┌───────▼────────┐              ┌───────▼────────┐
        │  Frontend      │              │   Backend      │
        │  Deployment    │              │   Deployment   │
        │  (2-6 replicas)│              │  (3-10 replicas)│
        └────────────────┘              └────────────────┘
                       │                │
                       │   ┌────────────┘
                       │   │
                       ▼   ▼
                ┌────────────────┐
                │   PostgreSQL   │
                │     Redis      │
                └────────────────┘
```

## 前置条件

### 必需组件

1. **Kubernetes 集群** (v1.24+)
2. **kubectl** CLI 工具
3. **NGINX Ingress Controller**
4. **Metrics Server** (用于 HPA)

### 可选组件

- **cert-manager**: 用于自动管理 TLS 证书
- **Prometheus**: 用于监控
- **Grafana**: 用于可视化

### 安装依赖

```bash
# 安装 NGINX Ingress Controller
kubectl apply -f https://raw.githubusercontent.com/kubernetes/ingress-nginx/main/deploy/static/provider/cloud/deploy.yaml[需更新]

# 安装 Metrics Server
kubectl apply -f https://github.com/kubernetes-sigs/metrics-server/releases/latest/download/components.yaml

# 安装 cert-manager (可选)
kubectl apply -f https://github.com/cert-manager/cert-manager/releases/download/v1.13.0/cert-manager.yaml
```

## 快速开始

### 1. 克隆仓库

```bash
cd g:\_src\FormalMath\k8s
```

### 2. 配置 Secret

编辑 `03-secret.yaml`，更新敏感信息：

```yaml
stringData:
  DB_PASSWORD: "your-strong-password"
  JWT_SECRET: "your-jwt-secret"
  # ... 其他敏感信息
```

### 3. 部署应用

```bash
# Linux/Mac
chmod +x deploy.sh
./deploy.sh deploy-all

# Windows PowerShell
.\deploy.ps1 deploy-all
```

### 4. 验证部署

```bash
kubectl get pods -n formalmath-prod
kubectl get svc -n formalmath-prod
kubectl get ingress -n formalmath-prod
```

## 详细部署

### 步骤 1: 部署基础资源

```bash
./deploy.sh deploy-base
```

这将创建：
- Namespace
- ConfigMap
- Secret

### 步骤 2: 部署应用

```bash
./deploy.sh deploy-apps
```

这将创建：
- Backend Deployment (3 个副本)
- Frontend Deployment (2 个副本)
- Services

### 步骤 3: 部署 Ingress

```bash
./deploy.sh deploy-ingress
```

### 步骤 4: 部署 HPA

```bash
./deploy.sh deploy-hpa
```

## 配置文件说明

| 文件 | 描述 |
|------|------|
| `01-namespace.yaml` | 命名空间配置 |
| `02-configmap.yaml` | 非敏感配置 |
| `03-secret.yaml` | 敏感信息（需要手动更新） |
| `04-backend-deployment.yaml` | 后端部署配置 |
| `05-frontend-deployment.yaml` | 前端部署配置 |
| `06-service.yaml` | Service 配置 |
| `07-ingress.yaml` | Ingress 配置 |
| `08-hpa.yaml` | HPA 和 PDB 配置 |
| `09-monitoring.yaml` | 监控和网络安全策略 |

## 资源配额

### Backend

| 资源 | 请求 | 限制 |
|------|------|------|
| CPU | 250m | 500m |
| 内存 | 256Mi | 512Mi |
| 副本数 | 3 | 10 |

### Frontend

| 资源 | 请求 | 限制 |
|------|------|------|
| CPU | 100m | 200m |
| 内存 | 64Mi | 128Mi |
| 副本数 | 2 | 6 |

## 部署脚本使用

### 基本命令

```bash
# 完整部署
./deploy.sh deploy-all

# 仅部署应用
./deploy.sh deploy-apps

# 查看状态
./deploy.sh status

# 查看日志
./deploy.sh logs

# 回滚
./deploy.sh rollback

# 手动扩缩容
./deploy.sh scale --replicas 5

# 删除所有资源
./deploy.sh delete
```

### 使用特定镜像标签

```bash
./deploy.sh deploy-apps --image-tag v1.2.3
```

## 监控和日志

### 查看 Pod 日志

```bash
# Backend 日志
kubectl logs -n formalmath-prod -l app=backend --tail=100 -f

# Frontend 日志
kubectl logs -n formalmath-prod -l app=frontend --tail=100 -f

# 特定 Pod 日志
kubectl logs -n formalmath-prod backend-deployment-xxxxx
```

### 查看事件

```bash
kubectl get events -n formalmath-prod --sort-by=.lastTimestamp
```

### 查看资源使用

```bash
# Pod 资源使用
kubectl top pods -n formalmath-prod

# 节点资源使用
kubectl top nodes
```

### HPA 状态

```bash
kubectl get hpa -n formalmath-prod
kubectl describe hpa backend-hpa -n formalmath-prod
```

## 故障排除

### Pod 无法启动

```bash
# 查看 Pod 状态
kubectl describe pod <pod-name> -n formalmath-prod

# 查看 Pod 日志
kubectl logs <pod-name> -n formalmath-prod --previous
```

### 无法访问服务

1. 检查 Pod 状态：
```bash
kubectl get pods -n formalmath-prod
```

2. 检查 Service：
```bash
kubectl get svc -n formalmath-prod
```

3. 检查 Ingress：
```bash
kubectl get ingress -n formalmath-prod
kubectl describe ingress formalmath-ingress -n formalmath-prod
```

4. 测试内部连接：
```bash
kubectl run test --rm -it --image=curlimages/curl --restart=Never -- sh
# 在容器内
curl 
```

### HPA 不工作

1. 检查 Metrics Server：
```bash
kubectl get apiservice v1beta1.metrics.k8s.io
```

2. 检查 HPA 状态：
```bash
kubectl describe hpa backend-hpa -n formalmath-prod
```

### 证书问题

如果使用 cert-manager：

```bash
# 检查证书状态
kubectl get certificates -n formalmath-prod
kubectl describe certificate formalmath-cert -n formalmath-prod

# 检查证书请求
kubectl get certificaterequest -n formalmath-prod
```

## 安全建议

1. **更新 Secret**: 生产环境务必更新所有 Secret
2. **使用网络策略**: 已配置 NetworkPolicy 限制 Pod 间通信
3. **RBAC**: 为不同用户配置适当的 RBAC 权限
4. **Pod 安全**: 配置了 securityContext 运行非 root 用户
5. **资源限制**: 所有 Pod 都设置了资源限制

## 更新部署

### 滚动更新

```bash
# 更新镜像
kubectl set image deployment/backend-deployment backend=formalmath/backend:v1.2.3 -n formalmath-prod

# 监控更新进度
kubectl rollout status deployment/backend-deployment -n formalmath-prod
```

### 回滚

```bash
# 查看历史版本
kubectl rollout history deployment/backend-deployment -n formalmath-prod

# 回滚到上一个版本
kubectl rollout undo deployment/backend-deployment -n formalmath-prod

# 回滚到特定版本
kubectl rollout undo deployment/backend-deployment --to-revision=2 -n formalmath-prod
```

## 清理资源

```bash
# 删除所有资源
./deploy.sh delete

# 或手动删除
kubectl delete namespace formalmath-prod
```

## 联系支持

如有问题，请：
1. 查看日志和事件
2. 检查本文档的故障排除部分
3. 提交 Issue 到项目仓库
