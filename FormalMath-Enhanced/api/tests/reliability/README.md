---
title: FormalMath API 可靠性测试
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath API 可靠性测试

本目录包含FormalMath后端API的全面可靠性验证测试套件。

## 测试范围

### 1. 功能测试 (`test_api_functional.py`)
验证所有API端点的功能正确性：
- 健康检查端点
- 知识图谱端点
- 学习路径端点
- 异步任务端点
- 搜索端点
- 推荐系统端点
- 学习引擎端点
- 输入验证和响应格式

### 2. 性能测试 (`test_api_performance.py`)
验证API的并发处理和响应时间：
- 并发请求处理
- 响应时间基准测试
- 缓存性能测试
- 数据库连接池性能
- 负载测试

### 3. 安全测试 (`test_api_security.py`)
验证API的安全性：
- SQL注入防护
- XSS攻击防护
- 路径遍历防护
- 输入验证
- 数据泄露检查
- CORS配置

### 4. 容错测试 (`test_api_fault_tolerance.py`)
验证异常处理和恢复机制：
- 异常输入处理
- 服务依赖故障
- 数据库错误处理
- 缓存故障降级
- 恢复机制

## 运行测试

### 运行所有测试

```bash
python tests/reliability/run_all_tests.py --all
```

### 运行特定测试类型

```bash
# 仅功能测试
python tests/reliability/run_all_tests.py --functional

# 仅性能测试
python tests/reliability/run_all_tests.py --performance

# 仅安全测试
python tests/reliability/run_all_tests.py --security

# 仅容错测试
python tests/reliability/run_all_tests.py --fault
```

### 使用pytest直接运行

```bash
# 运行所有可靠性测试
pytest tests/reliability/ -v

# 运行功能测试
pytest tests/reliability/test_api_functional.py -v

# 运行性能测试（较慢）
pytest tests/reliability/test_api_performance.py -v -m performance

# 运行安全测试
pytest tests/reliability/test_api_security.py -v -m security

# 运行容错测试
pytest tests/reliability/test_api_fault_tolerance.py -v -m fault_tolerance

# 运行慢速测试
pytest tests/reliability/ -v --run-slow
```

## 测试报告

测试运行后会生成详细报告：
- 报告文件：`tests/reliability/test_report.md`
- 包含：测试结果汇总、详细输出、改进建议

## 性能基准

### 响应时间阈值

| 端点类型 | 平均响应时间 | P95响应时间 | 成功率 |
|---------|-------------|------------|--------|
| 健康检查 | < 100ms | < 200ms | > 99.9% |
| 概念列表 | < 500ms | < 1000ms | > 95% |
| 图谱统计 | < 300ms | < 600ms | > 95% |
| 搜索 | < 1000ms | < 2000ms | > 90% |

### 并发用户测试

测试以下并发级别：
- 1个并发用户（基准）
- 10个并发用户（轻度负载）
- 50个并发用户（中度负载）
- 100个并发用户（重度负载）

## 文件结构

```
tests/reliability/
├── README.md                       # 本文件
├── conftest.py                     # Pytest配置
├── run_all_tests.py               # 测试运行器
├── test_api_functional.py         # 功能测试
├── test_api_performance.py        # 性能测试
├── test_api_security.py           # 安全测试
├── test_api_fault_tolerance.py    # 容错测试
└── test_report.md                 # 生成的测试报告
```

## 环境要求

- Python 3.8+
- pytest
- pytest-asyncio
- httpx
- FastAPI TestClient

## 注意事项

1. **数据库依赖**: 测试使用内存SQLite数据库，不需要外部数据库
2. **Redis依赖**: 部分测试会跳过如果Redis不可用
3. **Celery依赖**: 异步任务测试会跳过如果Celery Worker未运行
4. **性能测试**: 可能需要较长时间，请耐心等待

## 持续集成

建议在CI/CD管道中运行以下命令：

```bash
# 快速测试（CI）
pytest tests/reliability/test_api_functional.py -v

# 完整测试（ nightly）
pytest tests/reliability/ -v --run-slow
```

## 故障排除

### 导入错误

确保已安装所有依赖：
```bash
pip install -r requirements.txt
pip install pytest pytest-asyncio httpx
```

### 数据库锁定错误

SQLite并发测试可能会遇到锁定错误，这是预期的行为。

### Redis连接错误

如果Redis不可用，相关测试会自动跳过。
