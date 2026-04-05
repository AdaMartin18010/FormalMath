---
title: FormalMath 性能测试套件
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 性能测试套件

FormalMath 项目的全面性能测试解决方案，包括负载测试、压力测试、API性能测试和前端性能测试。

## 📋 目录

- [概述](#概述)
- [快速开始](#快速开始)
- [测试类型](#测试类型)
- [配置说明](#配置说明)
- [运行测试](#运行测试)
- [生成报告](#生成报告)
- [优化建议](#优化建议)

## 概述

本性能测试套件用于评估 FormalMath 系统在不同负载条件下的性能表现，帮助识别性能瓶颈并提供优化建议。

### 测试覆盖范围

| 测试类型 | 工具 | 描述 |
|---------|------|------|
| 负载测试 | Locust | 模拟正常用户负载，测试系统稳定性 |
| 压力测试 | Locust | 逐步增加负载，找出系统极限 |
| API性能测试 | pytest-benchmark | 细粒度API响应时间测试 |
| 前端性能测试 | Cypress + Lighthouse | 页面加载和渲染性能 |

## 快速开始

### 1. 安装依赖

```bash
cd tests/performance
pip install -r requirements.txt
```

### 2. 运行所有测试

```bash
python run_performance_tests.py
```

### 3. 查看报告

测试完成后，报告将保存在 `reports/` 目录：

```bash
open reports/performance_report_*.html
```

## 测试类型

### 🚀 负载测试 (Load Test)

模拟正常用户访问模式，验证系统在预期负载下的表现。

**默认参数：**
- 并发用户：100
- 持续时间：5分钟
- 思考时间：1-5秒

**用户行为模拟：**
- 40% - 浏览概念列表
- 30% - 查看概念详情
- 20% - 搜索内容
- 15% - 查看数学家
- 10% - 查看课程

**运行命令：**

```bash
# 使用默认参数
python run_performance_tests.py --load-test-only

# 自定义参数
python run_performance_tests.py --users 200 --duration 600

# 使用Locust Web界面
locust -f load_test.py --host=
```

### 🔥 压力测试 (Stress Test)

通过阶梯式增加负载，测试系统极限性能和稳定性。

**测试策略：**
1. 从50用户开始
2. 每60秒增加50用户
3. 最大1000用户
4. 错误率超过5%时停止

**运行命令：**

```bash
python run_performance_tests.py --stress-test

# 或直接使用Locust
locust -f stress_test.py --host= --class-picker
```

### 🔌 API性能测试

使用 pytest-benchmark 对关键API端点进行精确的性能测量。

**测试端点：**
- `/api/health` - 健康检查
- `/api/concepts` - 概念列表
- `/api/concepts/{id}` - 概念详情
- `/api/mathematicians` - 数学家列表
- `/api/search` - 搜索
- `/api/courses` - 课程列表

**性能目标：**
- 平均响应时间 < 200ms
- P95响应时间 < 500ms
- 错误率 < 1%

**运行命令：**

```bash
# 作为pytest运行
pytest api_performance_test.py -v --benchmark-only

# 生成JSON报告
pytest api_performance_test.py --benchmark-json=reports/api_benchmark.json

# 保存基准对比
pytest api_performance_test.py --benchmark-save=baseline
```

### 🎨 前端性能测试

使用 Cypress 测试前端页面性能，包括：

- 页面加载时间
- 首次内容绘制 (FCP)
- 最大内容绘制 (LCP)
- 可交互时间 (TTI)
- 累积布局偏移 (CLS)
- 资源加载大小

**性能预算：**

| 指标 | 目标值 |
|------|--------|
| FCP | < 1.8s |
| LCP | < 2.5s |
| TTI | < 3.5s |
| CLS | < 0.1 |
| JavaScript | < 500KB |
| CSS | < 100KB |

**运行命令：**

```bash
# 运行Cypress测试
cd ../frontend
npx cypress run --spec "../performance/frontend_performance_test.cy.ts"

# 交互式模式
npx cypress open
```

## 配置说明

### 环境配置

编辑 `config.py` 或在运行时指定环境：

```python
# config.py
ENVIRONMENTS = {
    "development": {
        "base_url": "",
        "api_url": ""
    },
    "staging": {
        "base_url": "https://staging.formalmath.org[需更新]",
        "api_url": "https://api-staging.formalmath.org[需更新]"
    },
    "production": {
        "base_url": "https://formalmath.org[需更新]",
        "api_url": "https://api.formalmath.org[需更新]"
    }
}
```

### 命令行参数

```bash
python run_performance_tests.py --help

# 选项:
#   --env {development,staging,production}
#                         测试环境
#   --users USERS         负载测试并发用户数
#   --duration DURATION   负载测试持续时间(秒)
#   --load-test-only      只运行负载测试
#   --api-test-only       只运行API性能测试
#   --stress-test         运行压力测试
```

## 运行测试

### 完整测试流程

```bash
# 1. 确保测试环境运行
cd ../backend && python -m uvicorn main:app --reload
cd ../frontend && npm run dev

# 2. 运行性能测试
cd tests/performance
python run_performance_tests.py --env development

# 3. 查看报告
open reports/performance_report_*.html
```

### 分布式负载测试

对于大规模负载测试，可以使用Locust的分布式模式：

```bash
# 启动主节点
locust -f load_test.py --master

# 启动多个工作节点
locust -f load_test.py --worker --master-host=localhost
```

### CI/CD集成

```yaml
# .github/workflows/performance.yml
name: Performance Tests

on:
  schedule:
    - cron: '0 2 * * 0'  # 每周日凌晨2点

jobs:
  performance:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      
      - name: Install dependencies
        run: pip install -r tests/performance/requirements.txt
      
      - name: Run performance tests
        run: python tests/performance/run_performance_tests.py --env staging
      
      - name: Upload report
        uses: actions/upload-artifact@v3
        with:
          name: performance-report
          path: tests/performance/reports/
```

## 生成报告

### 自动报告生成

测试完成后会自动生成HTML报告，包含：

- 测试摘要仪表板
- 响应时间分布图表
- API性能对比
- 前端性能指标
- 优化建议

### 手动生成报告

```python
from generate_report import ReportGenerator

generator = ReportGenerator()
report_path = generator.generate_report(
    load_test_data={...},
    api_test_data=[...],
    frontend_test_data=[...]
)
```

### 报告示例

![报告示例](docs/report-screenshot.png)

## 优化建议

### 常见性能问题及解决方案

#### 1. 高响应时间

**症状：** 平均响应时间 > 500ms

**解决方案：**
- 启用数据库查询缓存
- 使用Redis缓存热点数据
- 优化数据库索引
- 实施分页查询

#### 2. 低吞吐量

**症状：** 吞吐量 < 50 req/s

**解决方案：**
- 增加应用服务器实例
- 使用负载均衡器
- 优化连接池配置
- 启用Gzip压缩

#### 3. 高错误率

**症状：** 错误率 > 5%

**解决方案：**
- 检查服务器日志定位错误
- 增加超时时间
- 实施熔断降级策略
- 优化资源限制

#### 4. 前端加载慢

**症状：** LCP > 2.5s

**解决方案：**
- 实施代码分割
- 懒加载非关键资源
- 优化图片大小和格式
- 使用CDN加速静态资源

### 性能调优检查清单

- [ ] 启用HTTP/2
- [ ] 配置浏览器缓存
- [ ] 启用Gzip/Brotli压缩
- [ ] 优化数据库查询
- [ ] 使用Redis缓存
- [ ] 配置CDN
- [ ] 实施懒加载
- [ ] 优化图片资源
- [ ] 代码分割
- [ ] 服务端渲染(SSR)

## 📁 文件结构

```
performance/
├── README.md                      # 本文档
├── requirements.txt               # Python依赖
├── config.py                      # 测试配置
├── load_test.py                   # 负载测试脚本
├── stress_test.py                 # 压力测试脚本
├── api_performance_test.py        # API性能测试
├── frontend_performance_test.cy.ts # 前端性能测试
├── generate_report.py             # 报告生成器
├── run_performance_tests.py       # 测试运行器
├── reports/                       # 测试报告输出
└── results/                       # 原始测试数据
```

## 📊 性能基准

### 目标性能指标

| 指标 | 目标 | 警告 | 危险 |
|------|------|------|------|
| 平均响应时间 | < 200ms | < 500ms | > 1000ms |
| P95响应时间 | < 500ms | < 1000ms | > 2000ms |
| 错误率 | < 1% | < 5% | > 10% |
| 吞吐量 | > 100 rps | > 50 rps | < 50 rps |
| LCP | < 2.5s | < 4s | > 4s |

### 历史基准

测试报告会保存历史数据，可用于：
- 对比不同版本的性能变化
- 识别性能回归
- 验证优化效果

```bash
# 对比当前与基准
pytest api_performance_test.py --benchmark-compare
```

## 🔧 故障排除

### 常见问题

#### Locust无法启动

```bash
# 检查安装
pip show locust

# 重新安装
pip install locust --upgrade
```

#### 端口被占用

```bash
# 查找占用端口的进程
lsof -i :8089

# 使用不同端口
locust -f load_test.py --web-port 8090
```

#### 测试过程中内存不足

```bash
# 减少并发用户数
python run_performance_tests.py --users 50

# 或分批运行测试
python run_performance_tests.py --load-test-only
python run_performance_tests.py --api-test-only
```

## 📚 参考资源

- [Locust文档](https://docs.locust.io/)[需更新]
- [pytest-benchmark文档](https://pytest-benchmark.readthedocs.io/)[需更新]
- [Cypress性能测试](https://docs.cypress.io/guides/references/best-practices)[需更新]
- [Web Vitals](https://web.dev/vitals/)[需更新]
- [Google PageSpeed Insights](https://developers.google.com/speed/pagespeed/insights/)[需更新]

## 🤝 贡献

欢迎提交Issue和PR来改进性能测试套件。

---

**最后更新：** 2026年4月4日
