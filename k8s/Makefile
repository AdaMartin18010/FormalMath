# FormalMath Kubernetes Deployment Makefile

NAMESPACE := formalmath-prod
KUBECTL := kubectl
KUSTOMIZE := kustomize

.PHONY: help deploy deploy-kustomize delete status logs test verify

help: ## 显示帮助信息
	@echo "FormalMath Kubernetes 部署"
	@echo ""
	@echo "可用的命令:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-20s\033[0m %s\n", $$1, $$2}'

dev: ## 部署到开发环境
	@echo "部署到开发环境..."
	$(KUBECTL) apply -k overlays/dev 2>/dev/null || $(KUSTOMIZE) build overlays/dev | $(KUBECTL) apply -f -

staging: ## 部署到测试环境
	@echo "部署到测试环境..."
	$(KUBECTL) apply -k overlays/staging 2>/dev/null || $(KUSTOMIZE) build overlays/staging | $(KUBECTL) apply -f -

prod: ## 部署到生产环境
	@echo "部署到生产环境..."
	$(KUBECTL) apply -k overlays/production 2>/dev/null || $(KUSTOMIZE) build overlays/production | $(KUBECTL) apply -f -

deploy: ## 部署所有资源
	@echo "部署所有资源..."
	$(KUSTOMIZE) build . | $(KUBECTL) apply -f -

deploy-kustomize: ## 使用 kustomize 部署
	@echo "使用 kustomize 部署..."
	$(KUSTOMIZE) build . | $(KUBECTL) apply -f -

delete: ## 删除所有资源
	@echo "删除所有资源..."
	$(KUBECTL) delete namespace $(NAMESPACE) --ignore-not-found=true

status: ## 查看部署状态
	@echo "=== 命名空间 ==="
	$(KUBECTL) get namespace $(NAMESPACE)
	@echo ""
	@echo "=== Deployments ==="
	$(KUBECTL) get deployments -n $(NAMESPACE)
	@echo ""
	@echo "=== Pods ==="
	$(KUBECTL) get pods -n $(NAMESPACE)
	@echo ""
	@echo "=== Services ==="
	$(KUBECTL) get services -n $(NAMESPACE)
	@echo ""
	@echo "=== Ingress ==="
	$(KUBECTL) get ingress -n $(NAMESPACE)
	@echo ""
	@echo "=== HPA ==="
	$(KUBECTL) get hpa -n $(NAMESPACE) 2>/dev/null || echo "HPA 未部署"

logs-backend: ## 查看后端日志
	$(KUBECTL) logs -n $(NAMESPACE) -l app=backend,tier=api --tail=100 -f

logs-frontend: ## 查看前端日志
	$(KUBECTL) logs -n $(NAMESPACE) -l app=frontend,tier=web --tail=100 -f

logs: ## 选择查看日志
	@read -p "查看哪个服务的日志? (backend/frontend): " service; \
	if [ "$$service" = "backend" ]; then \
		$(MAKE) logs-backend; \
	elif [ "$$service" = "frontend" ]; then \
		$(MAKE) logs-frontend; \
	else \
		echo "无效选项"; \
	fi

describe-pod: ## 查看 Pod 详情
	@read -p "请输入 Pod 名称: " pod; \
	$(KUBECTL) describe pod $$pod -n $(NAMESPACE)

events: ## 查看事件
	$(KUBECTL) get events -n $(NAMESPACE) --sort-by=.lastTimestamp

top: ## 查看资源使用情况
	@echo "=== Pod 资源使用 ==="
	$(KUBECTL) top pods -n $(NAMESPACE) 2>/dev/null || echo "Metrics Server 未安装"
	@echo ""
	@echo "=== 节点资源使用 ==="
	$(KUBECTL) top nodes 2>/dev/null || echo "Metrics Server 未安装"

scale-backend: ## 扩缩容后端
	@read -p "请输入后端副本数: " replicas; \
	$(KUBECTL) scale deployment/backend-deployment --replicas=$$replicas -n $(NAMESPACE)

scale-frontend: ## 扩缩容前端
	@read -p "请输入前端副本数: " replicas; \
	$(KUBECTL) scale deployment/frontend-deployment --replicas=$$replicas -n $(NAMESPACE)

rollback-backend: ## 回滚后端
	$(KUBECTL) rollout undo deployment/backend-deployment -n $(NAMESPACE)

rollback-frontend: ## 回滚前端
	$(KUBECTL) rollout undo deployment/frontend-deployment -n $(NAMESPACE)

restart-backend: ## 重启后端
	$(KUBECTL) rollout restart deployment/backend-deployment -n $(NAMESPACE)

restart-frontend: ## 重启前端
	$(KUBECTL) rollout restart deployment/frontend-deployment -n $(NAMESPACE)

port-forward-backend: ## 端口转发后端
	@echo "将本地 3000 端口转发到后端服务..."
	$(KUBECTL) port-forward svc/backend-service 3000:3000 -n $(NAMESPACE)

port-forward-frontend: ## 端口转发前端
	@echo "将本地 8080 端口转发到前端服务..."
	$(KUBECTL) port-forward svc/frontend-service 8080:80 -n $(NAMESPACE)

shell-backend: ## 进入后端容器
	@pod=$$($(KUBECTL) get pods -n $(NAMESPACE) -l app=backend,tier=api -o jsonpath="{.items[0].metadata.name}"); \
	$(KUBECTL) exec -it $$pod -n $(NAMESPACE) -- /bin/sh

shell-frontend: ## 进入前端容器
	@pod=$$($(KUBECTL) get pods -n $(NAMESPACE) -l app=frontend,tier=web -o jsonpath="{.items[0].metadata.name}"); \
	$(KUBECTL) exec -it $$pod -n $(NAMESPACE) -- /bin/sh

test: ## 运行健康检查
	@echo "=== 测试后端健康检查 ==="
	@pod=$$($(KUBECTL) get pods -n $(NAMESPACE) -l app=backend,tier=api -o jsonpath="{.items[0].metadata.name}"); \
	$(KUBECTL) exec $$pod -n $(NAMESPACE) -- wget -qO- http://localhost:3000/api/v1/health 2>/dev/null || echo "健康检查端点未响应"

verify: ## 验证部署
	@echo "=== 验证部署 ==="
	@echo ""
	@echo "1. 检查所有 Pod 是否就绪..."
	@$(KUBECTL) get pods -n $(NAMESPACE) -o jsonpath="{range .items[*]}{.metadata.name}{'\t'}{.status.phase}{'\t'}{.status.containerStatuses[0].ready}{'\n'}{end}"
	@echo ""
	@echo "2. 检查服务..."
	@$(KUBECTL) get svc -n $(NAMESPACE)
	@echo ""
	@echo "3. 检查 Ingress..."
	@$(KUBECTL) get ingress -n $(NAMESPACE)
	@echo ""
	@echo "验证完成!"

update-image: ## 更新镜像
	@read -p "请输入服务 (backend/frontend): " service; \
	read -p "请输入镜像标签: " tag; \
	if [ "$$service" = "backend" ]; then \
		$(KUBECTL) set image deployment/backend-deployment backend=formalmath/backend:$$tag -n $(NAMESPACE); \
	elif [ "$$service" = "frontend" ]; then \
		$(KUBECTL) set image deployment/frontend-deployment frontend=formalmath/frontend:$$tag -n $(NAMESPACE); \
	else \
		echo "无效选项"; \
	fi

build-kustomize: ## 构建 kustomize 输出
	$(KUSTOMIZE) build .

dry-run: ## 模拟部署（不实际执行）
	$(KUSTOMIZE) build . | $(KUBECTL) apply -f - --dry-run=client

diff: ## 查看配置差异
	$(KUSTOMIZE) build . | $(KUBECTL) diff -f - 2>/dev/null || echo "无差异或命令不支持"

# 安装依赖
install-ingress: ## 安装 NGINX Ingress Controller
	$(KUBECTL) apply -f https://raw.githubusercontent.com/kubernetes/ingress-nginx/main/deploy/static/provider/cloud/deploy.yaml

install-metrics: ## 安装 Metrics Server
	$(KUBECTL) apply -f https://github.com/kubernetes-sigs/metrics-server/releases/latest/download/components.yaml

install-cert-manager: ## 安装 cert-manager
	$(KUBECTL) apply -f https://github.com/cert-manager/cert-manager/releases/download/v1.13.0/cert-manager.yaml
