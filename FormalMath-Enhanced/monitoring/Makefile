# FormalMath-Enhanced 监控与日志系统 Makefile

.PHONY: help up down restart logs status clean backup

# 默认目标
help:
	@echo "FormalMath-Enhanced 监控系统"
	@echo ""
	@echo "可用命令:"
	@echo "  make up          - 启动所有监控服务"
	@echo "  make down        - 停止所有监控服务"
	@echo "  make restart     - 重启所有监控服务"
	@echo "  make logs        - 查看所有服务日志"
	@echo "  make status      - 查看服务状态"
	@echo "  make clean       - 清理数据和卷"
	@echo "  make backup      - 备份数据"
	@echo "  make prometheus  - 仅启动 Prometheus"
	@echo "  make grafana     - 仅启动 Grafana"
	@echo "  make elk         - 仅启动 ELK Stack"
	@echo "  make reload      - 热重载配置"

# 启动所有服务
up:
	@echo "启动 FormalMath 监控系统..."
	docker-compose up -d
	@echo "等待服务启动..."
	@sleep 10
	@echo "服务已启动:"
	@echo "  Grafana:      http://localhost:3000"
	@echo "  Prometheus:   http://localhost:9090"
	@echo "  Alertmanager: http://localhost:9093"
	@echo "  Kibana:       http://localhost:5601"

# 停止所有服务
down:
	@echo "停止监控系统..."
	docker-compose down

# 重启服务
restart: down up

# 查看日志
logs:
	docker-compose logs -f

logs-prometheus:
	docker-compose logs -f prometheus

logs-grafana:
	docker-compose logs -f grafana

logs-elk:
	docker-compose logs -f elasticsearch logstash kibana

# 查看状态
status:
	@echo "服务状态:"
	@docker-compose ps
	@echo ""
	@echo "资源使用:"
	@docker stats --no-stream --format "table {{.Name}}\t{{.CPUPerc}}\t{{.MemUsage}}\t{{.NetIO}}\t{{.BlockIO}}"

# 清理数据和卷
clean:
	@echo "警告: 这将删除所有监控数据!"
	@read -p "确定继续? [y/N] " confirm && [ $$confirm = y ] || exit 1
	docker-compose down -v
	docker volume rm -f monitoring_prometheus_data monitoring_grafana_data monitoring_elasticsearch_data monitoring_alertmanager_data monitoring_filebeat_data

docker-clean:
	docker system prune -f
	docker volume prune -f

# 备份数据
backup:
	@echo "创建备份..."
	@mkdir -p backups/$(shell date +%Y%m%d)
	
	# 备份 Prometheus 数据
	docker run --rm -v monitoring_prometheus_data:/data -v $(PWD)/backups/$(shell date +%Y%m%d):/backup alpine \
		tar czf /backup/prometheus-backup.tar.gz -C /data .
	
	# 备份 Grafana 数据
	docker run --rm -v monitoring_grafana_data:/data -v $(PWD)/backups/$(shell date +%Y%m%d):/backup alpine \
		tar czf /backup/grafana-backup.tar.gz -C /data .
	
	@echo "备份完成: backups/$(shell date +%Y%m%d)/"

# 恢复数据
restore:
	@if [ -z "$(DATE)" ]; then \
		echo "使用方法: make restore DATE=20240101"; \
		exit 1; \
	fi
	@echo "从 backups/$(DATE)/ 恢复数据..."
	
	# 停止服务
	docker-compose down
	
	# 恢复 Prometheus
	docker run --rm -v monitoring_prometheus_data:/data -v $(PWD)/backups/$(DATE):/backup alpine \
		tar xzf /backup/prometheus-backup.tar.gz -C /data
	
	# 恢复 Grafana
	docker run --rm -v monitoring_grafana_data:/data -v $(PWD)/backups/$(DATE):/backup alpine \
		tar xzf /backup/grafana-backup.tar.gz -C /data
	
	# 启动服务
	docker-compose up -d

# 单独启动服务
prometheus:
	docker-compose up -d prometheus node-exporter cadvisor

grafana:
	docker-compose up -d grafana

elk:
	docker-compose up -d elasticsearch logstash kibana filebeat

alertmanager:
	docker-compose up -d alertmanager

# 热重载配置
reload-prometheus:
	@echo "热重载 Prometheus 配置..."
	@curl -X POST http://localhost:9090/-/reload
	@echo "完成"

reload-alertmanager:
	@echo "热重载 Alertmanager 配置..."
	@curl -X POST http://localhost:9093/-/reload
	@echo "完成"

reload: reload-prometheus reload-alertmanager

# 配置检查
check-prometheus:
	@docker run --rm -v $(PWD)/prometheus:/prom prom/prometheus:v2.47.0 \
		promtool check config /prom/prometheus.yml
	@docker run --rm -v $(PWD)/prometheus:/prom prom/prometheus:v2.47.0 \
		promtool check rules /prom/rules/*.yml
	@echo "Prometheus 配置检查通过"

check-logstash:
	@docker-compose exec logstash bin/logstash --config.test_and_exit -f /usr/share/logstash/pipeline/

check: check-prometheus check-logstash

# 健康检查
health:
	@echo "检查服务健康状态..."
	@curl -sf http://localhost:9090/-/healthy && echo "Prometheus: OK" || echo "Prometheus: FAIL"
	@curl -sf http://localhost:3000/api/health && echo "Grafana: OK" || echo "Grafana: FAIL"
	@curl -sf http://localhost:9200/_cluster/health && echo "Elasticsearch: OK" || echo "Elasticsearch: FAIL"
	@curl -sf http://localhost:5601/api/status && echo "Kibana: OK" || echo "Kibana: FAIL"

# 测试告警
test-alert:
	@echo "发送测试告警..."
	@curl -X POST http://localhost:9093/-/reload

# 更新镜像
update:
	@echo "拉取最新镜像..."
	docker-compose pull
	@echo "重启服务..."
	docker-compose up -d

# 显示指标示例
metrics-examples:
	@echo "=== Prometheus 查询示例 ==="
	@echo ""
	@echo "1. API 请求速率:"
	@echo '   sum(rate(http_requests_total[5m])) by (service)'
	@echo ""
	@echo "2. 响应时间 P95:"
	@echo '   histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))'
	@echo ""
	@echo "3. 错误率:"
	@echo '   sum(rate(http_requests_total{status=~"5.."}[5m])) / sum(rate(http_requests_total[5m]))'
	@echo ""
	@echo "4. CPU 使用率:"
	@echo '   100 - (avg by (instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)'
	@echo ""
	@echo "5. 内存使用率:"
	@echo '   (node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes) / node_memory_MemTotal_bytes * 100'

# 初始化
init:
	@echo "初始化监控系统..."
	@mkdir -p /var/log/formalmath/api
	@mkdir -p /var/log/formalmath/adaptive-learning
	@mkdir -p /var/log/formalmath/cognitive-diagnosis
	@mkdir -p /var/log/formalmath/evaluation-system
	@mkdir -p /var/log/formalmath/lean4
	@mkdir -p /var/log/formalmath/ai-formalization
	@mkdir -p /var/log/formalmath/knowledge-graph
	@cp .env.example .env
	@echo "请编辑 .env 文件配置环境变量"
