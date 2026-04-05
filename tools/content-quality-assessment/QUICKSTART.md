---
title: FormalMath 内容质量评估系统 - 快速开始指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 内容质量评估系统 - 快速开始指南

## 系统概述

FormalMath内容质量评估系统提供数学文档的自动化质量检测，包括完整性、准确性、可读性、国际化和学习效果五个维度的评估。

## 快速开始

### 1. 命令行使用

#### 评估单个文件
```bash
python main.py assess path/to/document.md
```

#### 评估目录（递归）
```bash
python main.py assess docs/01-基础数学/集合论 -r -f all --extract-issues
```

#### 参数说明
- `path`: 要评估的文件或目录
- `-o, --output-dir`: 输出目录 (默认: output)
- `-f, --format`: 输出格式 (json|html|markdown|csv|all)
- `--extract-issues`: 同时提取问题清单
- `--fail-on-issues`: 发现问题时返回非零退出码

### 2. 演示运行

```bash
python demo_demo.py
```

此命令会：
1. 评估样本文档
2. 批量评估实际文档
3. 生成多种格式报告
4. 提取问题清单

### 3. Python API使用

#### 基础评估
```python
from quality_assessor import ContentQualityAssessor
from report_generator import ReportGenerator

# 创建评估器
assessor = ContentQualityAssessor()

# 评估单个文件
result = assessor.assess_file("docs/example.md")
print(f"评分: {result.overall_score:.2f}")
print(f"等级: {result.quality_level}")

# 生成HTML报告
generator = ReportGenerator()
generator.generate_html_report([result], assessor.get_summary())
```

#### 批量评估
```python
# 评估整个目录
results = assessor.assess_directory("docs/01-基础数学", "**/*.md")

# 获取汇总
summary = assessor.get_summary()
print(f"平均分数: {summary['average_score']:.2f}")
```

#### 问题提取
```python
from issue_extractor import IssueExtractor

extractor = IssueExtractor()

# 从结果中提取问题
for result in results:
    extractor.extract_from_result(result.__dict__)

# 生成问题清单
extractor.generate_issue_report("issues.md")

# 生成行动计划
plan = extractor.generate_action_plan()
print(f"预估总工时: {plan['total_estimated_hours']} 小时")
```

## 评估维度说明

| 维度 | 权重 | 评估内容 |
|------|------|----------|
| 完整性 | 25% | 概念定义、定理证明、示例、引用、MSC编码 |
| 准确性 | 25% | 公式语法、引用格式、链接有效性、符号一致性 |
| 可读性 | 20% | 句子长度、段落结构、标题层级、复杂度 |
| 国际化 | 15% | 英文术语、术语一致性、文化适应性 |
| 学习效果 | 15% | 难度评估、学习时长、掌握概率、练习多样性 |

## 质量等级

| 等级 | 分数 | 描述 |
|------|------|------|
| 🟢 EXCELLENT | 90-100 | 优秀 |
| 🔵 GOOD | 80-89 | 良好 |
| 🟡 ACCEPTABLE | 60-79 | 可接受 |
| 🟠 NEEDS_IMPROVEMENT | 40-59 | 需改进 |
| 🔴 POOR | 0-39 | 差 |

## 输出文件

运行评估后，会在输出目录生成以下文件：

- `assessment_*.json` - 完整评估数据
- `assessment_*.html` - 可视化HTML报告
- `assessment_*.md` - Markdown格式报告
- `assessment_*.csv` - CSV表格数据
- `issues_*.md` - 问题清单报告
- `issues_*.json` - 问题清单数据

## 常见问题

### Q: 系统需要安装依赖吗？
A: 不需要。系统仅使用Python标准库，无需额外安装。

### Q: 支持哪些文档格式？
A: 目前主要支持Markdown格式（*.md）。

### Q: 如何自定义评估标准？
A: 编辑 `config.py` 文件中的配置参数。

### Q: 评估结果准确吗？
A: 系统基于启发式规则进行评估，结果仅供参考。建议结合人工审核。

## 项目结构

```
content-quality-assessment/
├── __init__.py           # 模块入口
├── quality_assessor.py   # 质量评估核心
├── report_generator.py   # 报告生成器
├── issue_extractor.py    # 问题提取器
├── config.py             # 配置文件
├── main.py               # 命令行入口
├── README.md             # 完整文档
├── QUICKSTART.md         # 本快速开始指南
├── requirements.txt      # 依赖说明
├── demo_demo.py          # 演示脚本
└── demo/                 # 演示目录
    ├── sample_document.md
    └── output/           # 演示输出
```

## 下一步

1. 运行 `python demo_demo.py` 查看系统功能
2. 使用 `python main.py assess <path>` 评估自己的文档
3. 查阅 `README.md` 了解完整功能
4. 根据需要修改 `config.py` 调整评估标准

---

**版本**: 1.0.0  
**更新日期**: 2026年4月4日
