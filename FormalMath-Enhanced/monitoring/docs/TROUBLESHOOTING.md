# 故障排查指南

## 常见问题及解决方案

### 1. Prometheus 问题

#### 问题：Prometheus 无法启动

**症状：**
```
docker-compose up prometheus
# 容器立即退出
```

**排查步骤：**

```bash
# 查看日志
docker-compose logs prometheus

# 检查配置文件语法
docker run --rm -v $(pwd)/prometheus:/prom prom/prometheus:v2.47.0 \
  promtool check config /prom/prometheus.yml

# 检查规则文件
docker run --rm -v $(pwd)/prometheus:/prom prom/prometheus:v2.47.0 \
  promtool check rules /prom/rules/*.yml
```

**常见原因：**
- YAML 语法错误（缩进问题）
- 文件路径错误
- 端口被占用

**解决：**
```bash
# 修复 YAML 语法
# 使用在线 YAML 验证器验证配置文件

# 检查端口占用
netstat -tlnp | grep 9090
# 或
lsof -i :9090
```

#### 问题：指标未收集

**排查：**
```bash
# 检查目标状态
curl http://localhost:9090/api/v1/targets | jq

# 直接测试端点
curl http://api:8000/metrics

# 检查网络连通性
docker exec formalmath-prometheus wget -O- http://api:8000/metrics
```

### 2. Grafana 问题

#### 问题：数据源连接失败

**排查：**
```bash
# 从 Grafana 容器测试连接
docker exec formalmath-grafana wget -O- http://prometheus:9090/api/v1/status/targets

# 检查数据源配置
docker-compose logs grafana | grep "datasource"
```

**解决：**
- 确认 Prometheus 服务名正确
- 检查网络配置
- 验证 URL 格式

#### 问题：仪表盘为空

**排查：**
```bash
# 检查 Prometheus 是否有数据
curl 'http://localhost:9090/api/v1/query?query=up'

# 检查时间范围
curl 'http://localhost:9090/api/v1/query_range?query=up&start=2024-01-01T00:00:00Z&end=2024-01-02T00:00:00Z&step=1h'
```

### 3. Elasticsearch 问题

#### 问题：内存不足

**症状：**
```
ERROR: [1] bootstrap checks failed
[1]: memory locking requested for elasticsearch process but memory is not locked
```

**解决：**
```bash
# 临时增加限制
sudo sysctl -w vm.max_map_count=262144

# 永久配置
echo "vm.max_map_count=262144" | sudo tee -a /etc/sysctl.conf
sudo sysctl -p

# 在 Linux 上配置 ulimit
echo "elasticsearch soft memlock unlimited" | sudo tee -a /etc/security/limits.conf
echo "elasticsearch hard memlock unlimited" | sudo tee -a /etc/security/limits.conf
```

#### 问题：磁盘水印错误

**症状：**
```
CLUSTER BLOCK: FORBIDDEN/12/index read-only / allow delete (api)
```

**解决：**
```bash
# 清理磁盘空间
# 然后解除只读模式
curl -X PUT "localhost:9200/_all/_settings" -H 'Content-Type: application/json' -d'{
  "index": {
    "blocks": {
      "read_only_allow_delete": null
    }
  }
}'
```

### 4. Logstash 问题

#### 问题：日志未处理

**排查：**
```bash
# 查看 Logstash 日志
docker-compose logs logstash | tail -100

# 测试配置
docker exec formalmath-logstash bin/logstash --config.test_and_exit -f /usr/share/logstash/pipeline/
```

**常见原因：**
- Grok 模式不匹配
- 日期格式解析失败
- 输出目标不可用

#### 问题：性能缓慢

**优化：**
```ruby
# 在 logstash.conf 中添加批量处理
output {
  elasticsearch {
    # 增加批量大小
    flush_size => 1000
    # 增加工作线程
    workers => 4
  }
}
```

### 5. Filebeat 问题

#### 问题：无法读取日志文件

**排查：**
```bash
# 检查文件权限
docker exec formalmath-filebeat ls -la /var/log/formalmath/

# 检查文件是否存在
ls -la /var/log/formalmath/

# 查看 Filebeat 日志
docker-compose logs filebeat | grep -i error
```

**解决：**
```bash
# 修复权限
sudo chmod -R 755 /var/log/formalmath/
sudo chown -R 1000:1000 /var/log/formalmath/

# 重新加载 Filebeat
docker-compose restart filebeat
```

### 6. 网络问题

#### 问题：容器间无法通信

**排查：**
```bash
# 检查网络
docker network ls
docker network inspect monitoring_monitoring

# 测试连通性
docker exec formalmath-prometheus ping grafana
docker exec formalmath-grafana ping prometheus
```

**解决：**
```bash
# 重启网络
docker-compose down
docker network rm monitoring_monitoring
docker-compose up -d
```

## 性能优化

### Prometheus 优化

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'formalmath'

# 存储优化
--storage.tsdb.retention.time=30d
--storage.tsdb.retention.size=50GB
--storage.tsdb.min-block-duration=2h
--storage.tsdb.max-block-duration=2h
```

### Elasticsearch 优化

```yaml
# elasticsearch.yml
# 减少分片数量
index.number_of_shards: 1
index.number_of_replicas: 0

# 刷新间隔
index.refresh_interval: 30s

# 批量队列
thread_pool.write.queue_size: 1000
```

### Logstash 优化

```yaml
# 增加 JVM 堆内存
LS_JAVA_OPTS: "-Xmx2g -Xms2g"

# 管道配置
pipeline.workers: 4
pipeline.batch.size: 1000
pipeline.batch.delay: 50
```

## 调试技巧

### 启用调试日志

```bash
# Prometheus 调试
docker-compose exec prometheus --log.level=debug

# Logstash 调试
export LOGSTASH_DEBUG=true
docker-compose up -d logstash

# Filebeat 调试
docker-compose exec filebeat filebeat -e -d "*"
```

### 手动测试指标端点

```bash
# 测试服务指标
curl -s http://localhost:8000/metrics | head -20

# 测试 Node Exporter
curl -s http://localhost:9100/metrics | grep node_cpu

# 测试 cAdvisor
curl -s http://localhost:8080/metrics | grep container_cpu
```

### 查看原始日志

```bash
# 查看 Filebeat 采集的原始日志
docker-compose exec filebeat cat /var/log/formalmath/api/app.log | head -20

# 查看 Logstash 处理的日志
docker-compose logs logstash | grep "output"
```

## 获取帮助

1. 查看组件日志：`docker-compose logs [service]`
2. 检查配置文件语法
3. 验证网络连通性
4. 查看官方文档
5. 搜索 GitHub Issues
