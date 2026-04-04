# FormalMath Kubernetes Deployment Script for PowerShell
# 用于部署 FormalMath 应用到 Kubernetes 集群

param(
    [Parameter(Position=0)]
    [ValidateSet("deploy", "deploy-base", "deploy-apps", "deploy-ingress", "deploy-hpa", "deploy-all", "delete", "status", "logs", "rollback", "scale", "help")]
    [string]$Command = "help",
    
    [string]$ImageTag = "",
    [int]$Replicas = 0
)

# 配置
$NAMESPACE = "formalmath-prod"
$DEPLOYMENT_DIR = Split-Path -Parent $MyInvocation.MyCommand.Path

# 颜色定义
function Write-Info($message) {
    Write-Host "[INFO] $message" -ForegroundColor Cyan
}

function Write-Success($message) {
    Write-Host "[SUCCESS] $message" -ForegroundColor Green
}

function Write-Warn($message) {
    Write-Host "[WARN] $message" -ForegroundColor Yellow
}

function Write-Error($message) {
    Write-Host "[ERROR] $message" -ForegroundColor Red
}

# 打印帮助信息
function Print-Help {
    Write-Host "FormalMath Kubernetes 部署脚本 (PowerShell)" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "用法: .\deploy.ps1 [命令] [选项]"
    Write-Host ""
    Write-Host "命令:"
    Write-Host "  deploy         部署所有资源"
    Write-Host "  deploy-base    仅部署基础资源（namespace, configmap, secret）"
    Write-Host "  deploy-apps    仅部署应用（deployment, service）"
    Write-Host "  deploy-ingress 部署 ingress"
    Write-Host "  deploy-hpa     部署 HPA 和 PDB"
    Write-Host "  deploy-all     完整部署所有资源"
    Write-Host "  delete         删除所有资源"
    Write-Host "  status         查看部署状态"
    Write-Host "  logs           查看日志"
    Write-Host "  rollback       回滚部署"
    Write-Host "  scale          手动扩缩容"
    Write-Host "  help           显示此帮助信息"
    Write-Host ""
    Write-Host "选项:"
    Write-Host "  -ImageTag      指定镜像标签（默认: latest）"
    Write-Host "  -Replicas      指定副本数（用于 scale 命令）"
}

# 检查 kubectl
function Check-Kubectl {
    try {
        $null = Get-Command kubectl -ErrorAction Stop
    } catch {
        Write-Error "kubectl 未安装或未在 PATH 中"
        exit 1
    }
    
    try {
        $null = kubectl cluster-info 2>$null
    } catch {
        Write-Error "无法连接到 Kubernetes 集群"
        exit 1
    }
    
    Write-Success "kubectl 已配置"
}

# 检查命名空间
function Ensure-Namespace {
    $ns = kubectl get namespace $NAMESPACE 2>$null
    if (-not $ns) {
        Write-Info "创建命名空间: $NAMESPACE"
        kubectl apply -f "$DEPLOYMENT_DIR\01-namespace.yaml"
    }
}

# 部署基础资源
function Deploy-Base {
    Write-Info "部署基础资源..."
    
    Ensure-Namespace
    
    kubectl apply -f "$DEPLOYMENT_DIR\01-namespace.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR\02-configmap.yaml"
    
    # 检查 Secret 是否存在
    $secret = kubectl get secret formalmath-secrets -n $NAMESPACE 2>$null
    if (-not $secret) {
        Write-Warn "Secret 不存在，创建示例 Secret"
        kubectl apply -f "$DEPLOYMENT_DIR\03-secret.yaml"
        Write-Warn "请更新 Secret 中的敏感信息！"
    } else {
        Write-Info "Secret 已存在，跳过创建"
    }
    
    Write-Success "基础资源部署完成"
}

# 部署应用
function Deploy-Apps {
    Write-Info "部署应用..."
    
    # 更新镜像标签（如果指定）
    if ($ImageTag) {
        Write-Info "使用镜像标签: $ImageTag"
        (Get-Content "$DEPLOYMENT_DIR\04-backend-deployment.yaml") -replace ":latest", ":$ImageTag" | Set-Content "$DEPLOYMENT_DIR\04-backend-deployment.yaml.tmp"
        (Get-Content "$DEPLOYMENT_DIR\05-frontend-deployment.yaml") -replace ":latest", ":$ImageTag" | Set-Content "$DEPLOYMENT_DIR\05-frontend-deployment.yaml.tmp"
        
        Move-Item "$DEPLOYMENT_DIR\04-backend-deployment.yaml.tmp" "$DEPLOYMENT_DIR\04-backend-deployment.yaml" -Force
        Move-Item "$DEPLOYMENT_DIR\05-frontend-deployment.yaml.tmp" "$DEPLOYMENT_DIR\05-frontend-deployment.yaml" -Force
    }
    
    kubectl apply -f "$DEPLOYMENT_DIR\04-backend-deployment.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR\05-frontend-deployment.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR\06-service.yaml"
    
    Write-Success "应用部署完成"
    
    # 等待就绪
    Write-Info "等待 Pod 就绪..."
    kubectl wait --for=condition=available --timeout=300s deployment/backend-deployment -n $NAMESPACE
    kubectl wait --for=condition=available --timeout=300s deployment/frontend-deployment -n $NAMESPACE
    Write-Success "所有 Pod 已就绪"
}

# 部署 Ingress
function Deploy-Ingress {
    Write-Info "部署 Ingress..."
    
    # 检查 Ingress Controller
    $ingressController = kubectl get pods -n ingress-nginx -l app.kubernetes.io/name=ingress-nginx 2>$null
    if (-not $ingressController) {
        $ingressController = kubectl get pods -n kube-system -l app.kubernetes.io/name=ingress-nginx 2>$null
    }
    
    if (-not $ingressController) {
        Write-Warn "未检测到 NGINX Ingress Controller"
        Write-Warn "请先安装 Ingress Controller:"
        Write-Warn "  kubectl apply -f https://raw.githubusercontent.com/kubernetes/ingress-nginx/main/deploy/static/provider/cloud/deploy.yaml"
    }
    
    kubectl apply -f "$DEPLOYMENT_DIR\07-ingress.yaml"
    Write-Success "Ingress 部署完成"
}

# 部署 HPA
function Deploy-Hpa {
    Write-Info "部署 HPA 和 PDB..."
    
    # 检查 Metrics Server
    $metricsServer = kubectl get apiservice v1beta1.metrics.k8s.io 2>$null
    if (-not $metricsServer) {
        Write-Warn "未检测到 Metrics Server，HPA 可能无法正常工作"
        Write-Warn "请安装 Metrics Server:"
        Write-Warn "  kubectl apply -f https://github.com/kubernetes-sigs/metrics-server/releases/latest/download/components.yaml"
    }
    
    kubectl apply -f "$DEPLOYMENT_DIR\08-hpa.yaml"
    Write-Success "HPA 和 PDB 部署完成"
}

# 完整部署
function Deploy-All {
    Deploy-Base
    Deploy-Apps
    Deploy-Ingress
    Deploy-Hpa
    
    Write-Success "========================================="
    Write-Success "FormalMath 完整部署完成！"
    Write-Success "========================================="
    
    Show-Status
}

# 删除所有资源
function Delete-All {
    Write-Warn "将删除所有 FormalMath 资源..."
    $confirm = Read-Host "确认删除? (y/N)"
    
    if ($confirm -eq 'y' -or $confirm -eq 'Y') {
        Write-Info "删除资源..."
        Get-ChildItem "$DEPLOYMENT_DIR\*.yaml" | ForEach-Object {
            kubectl delete -f $_.FullName --ignore-not-found=true 2>$null
        }
        Write-Success "资源删除完成"
    } else {
        Write-Info "取消删除"
    }
}

# 显示状态
function Show-Status {
    Write-Info "部署状态:"
    Write-Host ""
    
    Write-Host "命名空间:" -ForegroundColor Cyan
    kubectl get namespace $NAMESPACE
    
    Write-Host ""
    Write-Host "Deployment:" -ForegroundColor Cyan
    kubectl get deployments -n $NAMESPACE
    
    Write-Host ""
    Write-Host "Pods:" -ForegroundColor Cyan
    kubectl get pods -n $NAMESPACE
    
    Write-Host ""
    Write-Host "Services:" -ForegroundColor Cyan
    kubectl get services -n $NAMESPACE
    
    Write-Host ""
    Write-Host "Ingress:" -ForegroundColor Cyan
    kubectl get ingress -n $NAMESPACE
    
    Write-Host ""
    Write-Host "HPA:" -ForegroundColor Cyan
    kubectl get hpa -n $NAMESPACE 2>$null
}

# 查看日志
function Show-Logs {
    Write-Info "查看日志..."
    
    Write-Host "选择服务:"
    Write-Host "1) Backend"
    Write-Host "2) Frontend"
    $choice = Read-Host "请输入选项 (1/2)"
    
    switch ($choice) {
        "1" { kubectl logs -n $NAMESPACE -l app=backend,tier=api --tail=100 -f }
        "2" { kubectl logs -n $NAMESPACE -l app=frontend,tier=web --tail=100 -f }
        default { Write-Error "无效选项" }
    }
}

# 回滚部署
function Rollback {
    Write-Info "回滚部署..."
    
    Write-Host "选择要回滚的服务:"
    Write-Host "1) Backend"
    Write-Host "2) Frontend"
    Write-Host "3) 全部"
    $choice = Read-Host "请输入选项 (1/2/3)"
    
    switch ($choice) {
        "1" { kubectl rollout undo deployment/backend-deployment -n $NAMESPACE }
        "2" { kubectl rollout undo deployment/frontend-deployment -n $NAMESPACE }
        "3" {
            kubectl rollout undo deployment/backend-deployment -n $NAMESPACE
            kubectl rollout undo deployment/frontend-deployment -n $NAMESPACE
        }
        default {
            Write-Error "无效选项"
            return
        }
    }
    
    Write-Success "回滚完成"
}

# 手动扩缩容
function Scale {
    if ($Replicas -eq 0) {
        $Replicas = Read-Host "请输入副本数"
        $Replicas = [int]$Replicas
    }
    
    if ($Replicas -le 0) {
        Write-Error "副本数必须是正整数"
        return
    }
    
    Write-Info "扩容到 $Replicas 个副本..."
    
    kubectl scale deployment/backend-deployment --replicas=$Replicas -n $NAMESPACE
    kubectl scale deployment/frontend-deployment --replicas=$Replicas -n $NAMESPACE
    
    Write-Success "扩缩容完成"
}

# 主逻辑
switch ($Command) {
    "deploy" {
        Check-Kubectl
        Deploy-Apps
    }
    "deploy-base" {
        Check-Kubectl
        Deploy-Base
    }
    "deploy-apps" {
        Check-Kubectl
        Deploy-Apps
    }
    "deploy-ingress" {
        Check-Kubectl
        Deploy-Ingress
    }
    "deploy-hpa" {
        Check-Kubectl
        Deploy-Hpa
    }
    "deploy-all" {
        Check-Kubectl
        Deploy-All
    }
    "delete" {
        Check-Kubectl
        Delete-All
    }
    "status" {
        Check-Kubectl
        Show-Status
    }
    "logs" {
        Check-Kubectl
        Show-Logs
    }
    "rollback" {
        Check-Kubectl
        Rollback
    }
    "scale" {
        Check-Kubectl
        Scale
    }
    default {
        Print-Help
    }
}
