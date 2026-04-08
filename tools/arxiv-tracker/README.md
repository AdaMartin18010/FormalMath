# FormalMath arXiv前沿跟踪系统

自动化跟踪arXiv数学领域最新论文，提取与FormalMath知识库相关的研究进展。

## 功能特性

- 📡 **arXiv API集成**: 自动获取15+数学领域的最新论文
- 🔍 **智能筛选**: 基于关键词、MSC分类、日期等多维度筛选
- 📊 **相关性评分**: 多维度评分算法（关键词、概念、数学家、MSC）
- 💡 **更新建议**: 自动生成知识库更新建议
- 📑 **报告生成**: 支持Markdown/JSON/HTML格式报告
- ⚙️ **灵活配置**: 通过YAML配置文件自定义跟踪策略

## 跟踪领域

系统覆盖15个核心数学领域，与FormalMath项目分支对应：

| arXiv分类 | 英文名称 | 中文名称 | 对应分支 |
|-----------|----------|----------|----------|
| math.AG | Algebraic Geometry | 代数几何 | 分支03-几何与拓扑 |
| math.AT | Algebraic Topology | 代数拓扑 | 分支03-几何与拓扑 |
| math.CT | Category Theory | 范畴论 | 分支09-代数 |
| math.GR | Group Theory | 群论 | 分支09-代数 |
| math.NT | Number Theory | 数论 | 分支01-基础 |
| math.CV | Complex Variables | 复分析 | 分支07-分析 |
| math.FA | Functional Analysis | 泛函分析 | 分支07-分析 |
| math.DG | Differential Geometry | 微分几何 | 分支03-几何与拓扑 |
| math.GT | Geometric Topology | 几何拓扑 | 分支03-几何与拓扑 |
| math.LO | Logic | 逻辑 | 分支01-基础 |
| math.PR | Probability | 概率论 | 分支05-概率统计 |
| math.ST | Statistics | 统计 | 分支05-概率统计 |
| math.NA | Numerical Analysis | 数值分析 | 分支13-计算数学 |
| math.RA | Rings and Algebras | 环与代数 | 分支09-代数 |
| math.RT | Representation Theory | 表示论 | 分支09-代数 |

## 快速开始

### 安装依赖

```bash
pip install -r requirements.txt
```

### 运行完整跟踪

```bash
python main.py
```

### 跟踪单个分类

```bash
python main.py --category math.CT
```

### 指定时间范围

```bash
# 跟踪最近14天
python main.py --days 14

# 输出JSON格式报告
python main.py --days 14 --format json
```

### 测试模式

```bash
python main.py --test
```

## 系统架构

```
arxiv-tracker/
├── config.yaml           # 系统配置文件
├── main.py               # 主程序入口
├── arxiv_client.py       # arXiv API客户端
├── paper_filter.py       # 论文筛选器
├── relevance_scorer.py   # 相关性评分器
├── update_suggester.py   # 更新建议生成器
├── report_generator.py   # 报告生成器
├── requirements.txt      # Python依赖
└── README.md             # 使用文档
```

## 配置文件说明

`config.yaml` 包含以下主要配置：

### arXiv API配置
```yaml
arxiv:
  api_base_url: "http://export.arxiv.org/api/query"
  rate_limit: 3              # 每秒请求数
  timeout: 30                # 超时时间
  max_results_per_query: 100 # 每查询最大结果
```

### 跟踪领域配置
```yaml
tracking_categories:
  - id: "math.CT"
    name: "Category Theory"
    name_zh: "范畴论"
    formalmath_branch: "分支09-代数"
    keywords: ["category", "functor", "natural transformation"]
```

### 相关性评分权重
```yaml
relevance_scoring:
  weights:
    keyword_match: 0.35
    concept_match: 0.30
    mathematician_match: 0.15
    msc_match: 0.20
```

## 核心模块说明

### arxiv_client.py

提供与arXiv API的交互功能：

```python
from arxiv_client import ArxivClient

client = ArxivClient()
papers = client.search_by_category("math.CT", max_results=50)
```

### paper_filter.py

基于多维度条件筛选论文：

```python
from paper_filter import PaperFilter, FilterCriteria

filter = PaperFilter()
criteria = FilterCriteria(
    include_keywords=["category", "functor"],
    exclude_keywords=["withdrawn"]
)
results = filter.filter_papers(papers, criteria)
```

### relevance_scorer.py

计算论文与知识库的相关性：

```python
from relevance_scorer import RelevanceScorer

scorer = RelevanceScorer()
score = scorer.score_paper(paper)
print(f"总体分数: {score.overall_score}")
print(f"关键词: {score.keyword_score}")
print(f"概念: {score.concept_score}")
```

### update_suggester.py

生成知识库更新建议：

```python
from update_suggester import UpdateSuggester

suggester = UpdateSuggester()
suggestions = suggester.generate_suggestions(papers_with_scores)
```

### report_generator.py

生成各类报告：

```python
from report_generator import ReportGenerator

generator = ReportGenerator()
report_path = generator.generate_weekly_report(
    papers_by_category,
    output_format="markdown"
)
```

## 输出报告

### 周度报告 (Markdown)

包含以下内容：
- 执行摘要
- 按领域统计
- 高相关性论文详情
- 知识库更新建议
- 热门话题

### 更新建议报告

包含以下类型建议：
- 概念内容更新
- 新增概念
- 新增定理/结果
- 参考文献更新
- 新增数学家
- 综述推荐

## 定时任务

### 使用cron (Linux/macOS)

```bash
# 每周一上午9点运行
0 9 * * 1 cd /path/to/arxiv-tracker && python main.py
```

### 使用Windows任务计划程序

1. 打开任务计划程序
2. 创建基本任务
3. 设置触发器（每周一 9:00）
4. 设置操作（启动程序：python.exe，参数：main.py）

## 注意事项

1. **API速率限制**: arXiv API限制每秒3次请求，系统已内置速率控制
2. **网络访问**: 需要访问 `export.arxiv.org`
3. **存储空间**: 报告和日志会占用磁盘空间，定期清理
4. **数据隐私**: 系统仅读取公开数据，不发送敏感信息

## 故障排除

### 连接超时
- 检查网络连接
- 增加配置中的 `timeout` 值
- 考虑使用代理

### 无结果返回
- 检查分类ID是否正确
- 缩短 `lookback_days` 查看更早数据
- 检查关键词配置

### 评分不准确
- 更新 `keywords` 配置
- 调整 `weights` 权重
- 更新知识库数据文件

## 扩展开发

### 添加新分类

在 `config.yaml` 中添加：

```yaml
tracking_categories:
  - id: "math.XX"
    name: "New Category"
    name_zh: "新分类"
    formalmath_branch: "分支XX-名称"
    keywords: ["keyword1", "keyword2"]
```

### 自定义评分算法

继承 `RelevanceScorer` 类并重写方法：

```python
class CustomScorer(RelevanceScorer):
    def _score_keywords(self, paper, category):
        # 自定义关键词评分逻辑
        pass
```

## 许可证

与FormalMath项目一致。

## 贡献指南

欢迎提交Issue和PR，请确保：
- 代码通过基本测试
- 添加适当的日志
- 更新文档

---

*FormalMath arXiv前沿跟踪系统 v1.0.0*
