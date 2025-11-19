# 代数结构Python实现日志与监控指南

## 概述

本文档提供代数结构Python实现项目的完整日志记录和监控指南，包括日志配置、错误处理、性能监控、告警系统和最佳实践。

## 目录

- [日志与监控概述](#日志与监控概述)
- [日志记录](#日志记录)
- [错误处理](#错误处理)
- [性能监控](#性能监控)
- [告警系统](#告警系统)
- [日志分析](#日志分析)
- [监控工具](#监控工具)
- [最佳实践](#最佳实践)
- [常见问题](#常见问题)
- [故障排除](#故障排除)

## 日志与监控概述

### 为什么需要日志和监控

1. **问题诊断**: 快速定位和解决问题
2. **性能分析**: 了解系统性能瓶颈
3. **安全审计**: 追踪安全相关事件
4. **业务洞察**: 了解系统使用情况
5. **合规要求**: 满足审计和合规要求

### 日志和监控原则

- **结构化**: 使用结构化日志格式
- **可搜索**: 便于搜索和分析
- **可扩展**: 支持多种输出目标
- **性能**: 不影响系统性能
- **安全**: 不记录敏感信息

## 日志记录

### 日志级别

```python
import logging

# 日志级别（从低到高）
logging.DEBUG      # 详细调试信息
logging.INFO       # 一般信息
logging.WARNING    # 警告信息
logging.ERROR      # 错误信息
logging.CRITICAL   # 严重错误
```

### 基本配置

```python
import logging
import sys

# 基本配置
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S',
    handlers=[
        logging.FileHandler('algebraic_structures.log'),
        logging.StreamHandler(sys.stdout)
    ]
)

logger = logging.getLogger(__name__)
```

### 高级配置

```python
import logging
import logging.handlers
import json
from pathlib import Path

def setup_logging(
    log_level: str = "INFO",
    log_dir: Path = Path("logs"),
    log_file: str = "algebraic_structures.log",
    max_bytes: int = 10 * 1024 * 1024,  # 10MB
    backup_count: int = 5
):
    """设置日志配置"""
    log_dir.mkdir(exist_ok=True)

    # 创建格式化器
    formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )

    # 文件处理器（带轮转）
    file_handler = logging.handlers.RotatingFileHandler(
        log_dir / log_file,
        maxBytes=max_bytes,
        backupCount=backup_count
    )
    file_handler.setFormatter(formatter)
    file_handler.setLevel(logging.DEBUG)

    # 控制台处理器
    console_handler = logging.StreamHandler()
    console_handler.setFormatter(formatter)
    console_handler.setLevel(getattr(logging, log_level))

    # 根日志记录器
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG)
    root_logger.addHandler(file_handler)
    root_logger.addHandler(console_handler)

    return root_logger
```

### 结构化日志

```python
import logging
import json

class StructuredFormatter(logging.Formatter):
    """结构化日志格式化器"""

    def format(self, record):
        log_data = {
            'timestamp': self.formatTime(record, self.datefmt),
            'level': record.levelname,
            'logger': record.name,
            'message': record.getMessage(),
            'module': record.module,
            'function': record.funcName,
            'line': record.lineno
        }

        # 添加异常信息
        if record.exc_info:
            log_data['exception'] = self.formatException(record.exc_info)

        # 添加额外字段
        if hasattr(record, 'extra'):
            log_data.update(record.extra)

        return json.dumps(log_data, ensure_ascii=False)

# 使用结构化日志
handler = logging.StreamHandler()
handler.setFormatter(StructuredFormatter())
logger.addHandler(handler)

logger.info("群运算完成", extra={
    'group_order': 6,
    'operation': 'multiplication',
    'duration_ms': 12.5
})
```

### 日志记录示例

```python
import logging

logger = logging.getLogger(__name__)

class Group:
    """群类示例"""

    def __init__(self, elements, operation):
        logger.debug(f"创建群: {len(elements)}个元素")
        self.elements = elements
        self.operation = operation
        logger.info(f"群创建成功: 阶={len(elements)}")

    def multiply(self, a, b):
        """群运算"""
        logger.debug(f"执行群运算: {a} * {b}")
        try:
            result = self.operation(a, b)
            logger.debug(f"群运算结果: {result}")
            return result
        except Exception as e:
            logger.error(f"群运算失败: {a} * {b}", exc_info=True)
            raise

    def find_subgroups(self):
        """查找子群"""
        logger.info("开始查找子群")
        try:
            subgroups = self._compute_subgroups()
            logger.info(f"找到 {len(subgroups)} 个子群")
            return subgroups
        except Exception as e:
            logger.error("子群查找失败", exc_info=True)
            raise
```

### 日志上下文

```python
import logging
from contextvars import ContextVar

# 上下文变量
request_id_var: ContextVar[str] = ContextVar('request_id', default='')

class ContextFilter(logging.Filter):
    """添加上下文的日志过滤器"""

    def filter(self, record):
        record.request_id = request_id_var.get()
        return True

# 使用上下文
def process_group(group_id: str):
    """处理群"""
    request_id_var.set(group_id)
    logger.info("开始处理群")
    # ... 处理逻辑
    logger.info("群处理完成")
```

## 错误处理

### 自定义异常

```python
class AlgebraicStructureError(Exception):
    """代数结构基础异常"""
    pass

class GroupError(AlgebraicStructureError):
    """群相关错误"""
    pass

class RingError(AlgebraicStructureError):
    """环相关错误"""
    pass

class ValidationError(AlgebraicStructureError):
    """验证错误"""
    pass

class ComputationError(AlgebraicStructureError):
    """计算错误"""
    pass
```

### 错误处理模式

```python
import logging
from functools import wraps

logger = logging.getLogger(__name__)

def handle_errors(func):
    """错误处理装饰器"""
    @wraps(func)
    def wrapper(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except ValidationError as e:
            logger.warning(f"验证错误: {e}")
            raise
        except ComputationError as e:
            logger.error(f"计算错误: {e}", exc_info=True)
            raise
        except Exception as e:
            logger.critical(f"未预期的错误: {e}", exc_info=True)
            raise AlgebraicStructureError(f"未预期的错误: {e}") from e
    return wrapper

@handle_errors
def group_operation(group, a, b):
    """群运算"""
    if a not in group:
        raise ValidationError(f"{a} 不在群中")
    if b not in group:
        raise ValidationError(f"{b} 不在群中")

    try:
        return group.operation(a, b)
    except Exception as e:
        raise ComputationError(f"运算失败: {e}") from e
```

### 错误恢复

```python
import logging
from functools import wraps
import time

logger = logging.getLogger(__name__)

def retry_on_error(max_retries: int = 3, delay: float = 1.0):
    """错误重试装饰器"""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            for attempt in range(max_retries):
                try:
                    return func(*args, **kwargs)
                except Exception as e:
                    if attempt == max_retries - 1:
                        logger.error(f"重试 {max_retries} 次后仍然失败: {e}")
                        raise
                    logger.warning(f"尝试 {attempt + 1}/{max_retries} 失败: {e}，{delay}秒后重试")
                    time.sleep(delay)
        return wrapper
    return decorator

@retry_on_error(max_retries=3, delay=1.0)
def find_subgroups_with_retry(group):
    """带重试的子群查找"""
    return find_all_subgroups(group)
```

### 错误报告

```python
import logging
import traceback
from datetime import datetime

class ErrorReporter:
    """错误报告器"""

    def __init__(self, log_file: str = "errors.log"):
        self.log_file = log_file
        self.logger = logging.getLogger("error_reporter")

    def report_error(
        self,
        error: Exception,
        context: dict = None,
        severity: str = "error"
    ):
        """报告错误"""
        error_info = {
            'timestamp': datetime.now().isoformat(),
            'error_type': type(error).__name__,
            'error_message': str(error),
            'traceback': traceback.format_exc(),
            'severity': severity,
            'context': context or {}
        }

        # 记录到日志
        if severity == "critical":
            self.logger.critical(f"严重错误: {error_info}")
        elif severity == "error":
            self.logger.error(f"错误: {error_info}")
        else:
            self.logger.warning(f"警告: {error_info}")

        # 写入错误日志文件
        with open(self.log_file, 'a', encoding='utf-8') as f:
            import json
            f.write(json.dumps(error_info, ensure_ascii=False) + '\n')

        return error_info

# 使用错误报告器
error_reporter = ErrorReporter()

try:
    result = complex_computation()
except Exception as e:
    error_reporter.report_error(
        e,
        context={'operation': 'complex_computation', 'input': input_data},
        severity='error'
    )
```

## 性能监控

### 性能指标收集

```python
import logging
import time
from functools import wraps
from collections import defaultdict

logger = logging.getLogger(__name__)

class PerformanceMonitor:
    """性能监控器"""

    def __init__(self):
        self.metrics = defaultdict(list)

    def record_metric(self, name: str, value: float, unit: str = "ms"):
        """记录性能指标"""
        self.metrics[name].append({
            'value': value,
            'unit': unit,
            'timestamp': time.time()
        })
        logger.debug(f"性能指标: {name}={value}{unit}")

    def get_statistics(self, name: str):
        """获取统计信息"""
        if name not in self.metrics:
            return None

        values = [m['value'] for m in self.metrics[name]]
        return {
            'count': len(values),
            'min': min(values),
            'max': max(values),
            'mean': sum(values) / len(values),
            'median': sorted(values)[len(values) // 2]
        }

    def log_statistics(self):
        """记录统计信息"""
        for name in self.metrics:
            stats = self.get_statistics(name)
            logger.info(f"性能统计 {name}: {stats}")

# 全局性能监控器
performance_monitor = PerformanceMonitor()

def monitor_performance(func):
    """性能监控装饰器"""
    @wraps(func)
    def wrapper(*args, **kwargs):
        start_time = time.time()
        try:
            result = func(*args, **kwargs)
            duration = (time.time() - start_time) * 1000  # 转换为毫秒
            performance_monitor.record_metric(
                f"{func.__name__}_duration",
                duration
            )
            logger.debug(f"{func.__name__} 执行时间: {duration:.2f}ms")
            return result
        except Exception as e:
            duration = (time.time() - start_time) * 1000
            performance_monitor.record_metric(
                f"{func.__name__}_error_duration",
                duration
            )
            raise
    return wrapper

@monitor_performance
def find_subgroups(group):
    """查找子群（带性能监控）"""
    return find_all_subgroups(group)
```

### 资源使用监控

```python
import logging
import psutil
import os

logger = logging.getLogger(__name__)

class ResourceMonitor:
    """资源监控器"""

    def __init__(self):
        self.process = psutil.Process(os.getpid())

    def get_cpu_usage(self):
        """获取CPU使用率"""
        return self.process.cpu_percent(interval=1)

    def get_memory_usage(self):
        """获取内存使用"""
        memory_info = self.process.memory_info()
        return {
            'rss': memory_info.rss / 1024 / 1024,  # MB
            'vms': memory_info.vms / 1024 / 1024,  # MB
            'percent': self.process.memory_percent()
        }

    def log_resources(self):
        """记录资源使用"""
        cpu = self.get_cpu_usage()
        memory = self.get_memory_usage()

        logger.info(f"资源使用 - CPU: {cpu}%, 内存: {memory['rss']:.2f}MB ({memory['percent']:.2f}%)")

        return {
            'cpu': cpu,
            'memory': memory
        }

# 使用资源监控
resource_monitor = ResourceMonitor()

def monitor_resources(func):
    """资源监控装饰器"""
    @wraps(func)
    def wrapper(*args, **kwargs):
        # 执行前
        before = resource_monitor.log_resources()

        try:
            result = func(*args, **kwargs)
        finally:
            # 执行后
            after = resource_monitor.log_resources()
            logger.debug(f"资源变化 - CPU: {after['cpu'] - before['cpu']:.2f}%, "
                        f"内存: {after['memory']['rss'] - before['memory']['rss']:.2f}MB")

        return result
    return wrapper
```

## 告警系统

### 告警配置

```python
import logging
from typing import Callable, List
from dataclasses import dataclass
from enum import Enum

class AlertLevel(Enum):
    """告警级别"""
    INFO = "info"
    WARNING = "warning"
    ERROR = "error"
    CRITICAL = "critical"

@dataclass
class Alert:
    """告警"""
    level: AlertLevel
    message: str
    timestamp: float
    context: dict = None

class AlertManager:
    """告警管理器"""

    def __init__(self):
        self.handlers: List[Callable[[Alert], None]] = []
        self.logger = logging.getLogger("alert_manager")

    def register_handler(self, handler: Callable[[Alert], None]):
        """注册告警处理器"""
        self.handlers.append(handler)

    def send_alert(self, alert: Alert):
        """发送告警"""
        # 记录日志
        if alert.level == AlertLevel.CRITICAL:
            self.logger.critical(f"严重告警: {alert.message}")
        elif alert.level == AlertLevel.ERROR:
            self.logger.error(f"错误告警: {alert.message}")
        elif alert.level == AlertLevel.WARNING:
            self.logger.warning(f"警告告警: {alert.message}")
        else:
            self.logger.info(f"信息告警: {alert.message}")

        # 调用所有处理器
        for handler in self.handlers:
            try:
                handler(alert)
            except Exception as e:
                self.logger.error(f"告警处理器失败: {e}", exc_info=True)

    def alert(
        self,
        level: AlertLevel,
        message: str,
        context: dict = None
    ):
        """创建并发送告警"""
        import time
        alert = Alert(
            level=level,
            message=message,
            timestamp=time.time(),
            context=context
        )
        self.send_alert(alert)

# 告警处理器示例
def email_alert_handler(alert: Alert):
    """邮件告警处理器"""
    if alert.level in [AlertLevel.ERROR, AlertLevel.CRITICAL]:
        # 发送邮件
        pass

def slack_alert_handler(alert: Alert):
    """Slack告警处理器"""
    if alert.level in [AlertLevel.ERROR, AlertLevel.CRITICAL]:
        # 发送Slack消息
        pass

# 使用告警系统
alert_manager = AlertManager()
alert_manager.register_handler(email_alert_handler)
alert_manager.register_handler(slack_alert_handler)

# 发送告警
alert_manager.alert(
    AlertLevel.ERROR,
    "子群查找失败",
    context={'group_order': 100, 'error': str(e)}
)
```

### 阈值告警

```python
class ThresholdMonitor:
    """阈值监控器"""

    def __init__(self, alert_manager: AlertManager):
        self.alert_manager = alert_manager
        self.thresholds = {}

    def set_threshold(self, metric: str, warning: float, error: float, critical: float):
        """设置阈值"""
        self.thresholds[metric] = {
            'warning': warning,
            'error': error,
            'critical': critical
        }

    def check_threshold(self, metric: str, value: float):
        """检查阈值"""
        if metric not in self.thresholds:
            return

        thresholds = self.thresholds[metric]

        if value >= thresholds['critical']:
            self.alert_manager.alert(
                AlertLevel.CRITICAL,
                f"{metric} 超过严重阈值: {value} >= {thresholds['critical']}",
                context={'metric': metric, 'value': value}
            )
        elif value >= thresholds['error']:
            self.alert_manager.alert(
                AlertLevel.ERROR,
                f"{metric} 超过错误阈值: {value} >= {thresholds['error']}",
                context={'metric': metric, 'value': value}
            )
        elif value >= thresholds['warning']:
            self.alert_manager.alert(
                AlertLevel.WARNING,
                f"{metric} 超过警告阈值: {value} >= {thresholds['warning']}",
                context={'metric': metric, 'value': value}
            )

# 使用阈值监控
threshold_monitor = ThresholdMonitor(alert_manager)
threshold_monitor.set_threshold('cpu_usage', warning=70, error=85, critical=95)
threshold_monitor.set_threshold('memory_usage', warning=80, error=90, critical=95)

# 检查阈值
cpu_usage = resource_monitor.get_cpu_usage()
threshold_monitor.check_threshold('cpu_usage', cpu_usage)
```

## 日志分析

### 日志查询

```python
import re
from pathlib import Path
from typing import List, Dict

class LogAnalyzer:
    """日志分析器"""

    def __init__(self, log_file: Path):
        self.log_file = log_file

    def search_logs(
        self,
        pattern: str,
        level: str = None,
        start_time: str = None,
        end_time: str = None
    ) -> List[Dict]:
        """搜索日志"""
        results = []
        regex = re.compile(pattern)

        with open(self.log_file, 'r', encoding='utf-8') as f:
            for line in f:
                # 解析日志行
                log_entry = self._parse_log_line(line)
                if not log_entry:
                    continue

                # 过滤级别
                if level and log_entry['level'] != level:
                    continue

                # 过滤时间
                if start_time and log_entry['timestamp'] < start_time:
                    continue
                if end_time and log_entry['timestamp'] > end_time:
                    continue

                # 匹配模式
                if regex.search(line):
                    results.append(log_entry)

        return results

    def _parse_log_line(self, line: str) -> Dict:
        """解析日志行"""
        # 简单的日志解析（实际应使用更健壮的解析器）
        match = re.match(r'(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) - (\w+) - (\w+) - (.*)', line)
        if match:
            return {
                'timestamp': match.group(1),
                'logger': match.group(2),
                'level': match.group(3),
                'message': match.group(4)
            }
        return None

    def count_errors(self, start_time: str = None, end_time: str = None) -> int:
        """统计错误数量"""
        errors = self.search_logs(
            pattern='ERROR|CRITICAL',
            start_time=start_time,
            end_time=end_time
        )
        return len(errors)

    def get_error_summary(self) -> Dict:
        """获取错误摘要"""
        errors = self.search_logs(pattern='ERROR|CRITICAL')

        error_types = {}
        for error in errors:
            error_type = error.get('error_type', 'Unknown')
            error_types[error_type] = error_types.get(error_type, 0) + 1

        return {
            'total_errors': len(errors),
            'error_types': error_types
        }
```

## 监控工具

### Prometheus集成

```python
from prometheus_client import Counter, Histogram, Gauge, start_http_server

# 定义指标
operation_counter = Counter(
    'algebraic_operations_total',
    'Total number of algebraic operations',
    ['operation_type', 'structure_type']
)

operation_duration = Histogram(
    'algebraic_operation_duration_seconds',
    'Duration of algebraic operations',
    ['operation_type', 'structure_type']
)

active_groups = Gauge(
    'active_groups',
    'Number of active groups'
)

# 使用指标
def monitored_group_operation(group, a, b):
    """带监控的群运算"""
    with operation_duration.labels('multiply', 'group').time():
        result = group.operation(a, b)
        operation_counter.labels('multiply', 'group').inc()
        return result

# 启动Prometheus HTTP服务器
start_http_server(8000)
```

### Grafana仪表板

```json
{
  "dashboard": {
    "title": "代数结构监控",
    "panels": [
      {
        "title": "操作计数",
        "targets": [
          {
            "expr": "rate(algebraic_operations_total[5m])"
          }
        ]
      },
      {
        "title": "操作延迟",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, algebraic_operation_duration_seconds_bucket)"
          }
        ]
      }
    ]
  }
}
```

## 最佳实践

### 1. 日志级别使用

- **DEBUG**: 详细的调试信息，仅在开发时使用
- **INFO**: 一般信息，记录重要操作
- **WARNING**: 警告信息，可能的问题
- **ERROR**: 错误信息，需要关注
- **CRITICAL**: 严重错误，需要立即处理

### 2. 日志格式

- 使用结构化日志格式（JSON）
- 包含时间戳、级别、模块、消息
- 添加上下文信息（请求ID、用户ID等）

### 3. 性能考虑

- 使用异步日志处理器
- 避免在循环中记录大量日志
- 使用日志级别控制输出量

### 4. 安全性

- 不记录敏感信息（密码、密钥等）
- 对日志文件设置适当权限
- 定期清理旧日志

### 5. 监控指标

- 监控关键业务指标
- 设置合理的告警阈值
- 定期审查和调整阈值

## 常见问题

### Q1: 如何选择合适的日志级别？

**A**:

- DEBUG: 开发调试
- INFO: 正常操作
- WARNING: 潜在问题
- ERROR: 错误情况
- CRITICAL: 严重错误

### Q2: 日志文件过大怎么办？

**A**:

- 使用日志轮转（RotatingFileHandler）
- 设置最大文件大小和备份数量
- 定期清理旧日志

### Q3: 如何提高日志性能？

**A**:

- 使用异步日志处理器
- 避免在热路径中记录日志
- 使用适当的日志级别

### Q4: 如何监控分布式系统？

**A**:

- 使用集中式日志系统（ELK、Loki等）
- 使用分布式追踪（Jaeger、Zipkin等）
- 使用指标收集系统（Prometheus等）

### Q5: 如何处理日志中的敏感信息？

**A**:

- 使用日志过滤器移除敏感信息
- 在记录前脱敏数据
- 设置日志访问权限

## 故障排除

### 日志文件无法写入

```python
# 检查文件权限
import os
log_file = Path("logs/app.log")
log_file.parent.mkdir(parents=True, exist_ok=True)
log_file.touch()

# 检查磁盘空间
import shutil
free_space = shutil.disk_usage('.').free
if free_space < 1024 * 1024:  # 小于1MB
    logger.warning("磁盘空间不足")
```

### 性能监控影响性能

```python
# 使用采样减少监控开销
import random

def sampled_monitor(sample_rate: float = 0.1):
    """采样监控装饰器"""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            if random.random() < sample_rate:
                return monitor_performance(func)(*args, **kwargs)
            return func(*args, **kwargs)
        return wrapper
    return decorator
```

## 资源链接

### 相关文档

- **[开发者指南](00-Python实现-代数结构开发者指南.md)**: 开发环境和技术细节
- **[性能调优指南](00-Python实现-代数结构性能调优指南.md)**: 性能优化方法
- **[CI/CD指南](00-Python实现-代数结构CI-CD指南.md)**: CI/CD配置和监控

### 外部资源

- **Python logging文档**: <https://docs.python.org/3/library/logging.html>
- **Prometheus文档**: <https://prometheus.io/docs/>
- **Grafana文档**: <https://grafana.com/docs/>

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
