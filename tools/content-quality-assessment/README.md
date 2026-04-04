# FormalMath 内容质量评估系统

## 概述

FormalMath内容质量评估系统是一个自动化的数学文档质量检测工具，用于评估FormalMath项目中数学文档的完整性、准确性、可读性、国际化程度和学习效果。

## 功能特性

### 1. 完整性检查 (Completeness Assessment)
- ✅ 概念定义完整性检测
- ✅ 定理证明覆盖度分析
- ✅ 示例覆盖度统计
- ✅ 参考文献检查
- ✅ MSC编码验证

### 2. 准确性验证 (Accuracy Validation)
- ✅ 数学公式语法检查
- ✅ 引用格式验证
- ✅ 链接完整性检测
- ✅ 符号一致性检查
- ✅ 逻辑一致性分析

### 3. 可读性评估 (Readability Evaluation)
- ✅ 句子长度分析
- ✅ 段落结构评估
- ✅ 复杂度指标计算
- ✅ 标题层级检查
- ✅ 公式密度评估

### 4. 国际化评估 (Internationalization Assessment)
- ✅ 多语言一致性检查
- ✅ 术语翻译验证
- ✅ 文化适应性评估
- ✅ 英文术语覆盖度

### 5. 学习效果预测 (Learning Effect Prediction)
- ✅ 内容难度评估
- ✅ 学习时长预测
- ✅ 掌握概率估计
- ✅ 前置知识清晰度
- ✅ 练习多样性分析

## 安装与配置

### 环境要求
- Python 3.8+
- 无额外依赖（仅使用标准库）

### 安装步骤

1. 确保Python环境已安装：
```bash
python --version
```

2. 无需额外安装，直接使用：
```bash
cd tools/content-quality-assessment
```

## 使用方法

### 命令行使用

#### 评估单个文件
```bash
python quality_assessor.py path/to/document.md
```

#### 评估整个目录
```bash
python quality_assessor.py path/to/directory -r -o output.json
```

#### 参数说明
- `path`: 要评估的文件或目录路径
- `-o, --output`: 输出结果文件路径
- `-f, --format`: 输出格式 (json, html, markdown)
- `-r, --recursive`: 递归评估目录

### Python API使用

#### 基础用法
```python
from quality_assessor import ContentQualityAssessor
from report_generator import ReportGenerator

# 创建评估器
assessor = ContentQualityAssessor()

# 评估单个文件
result = assessor.assess_file("docs/01-基础数学/集合论/01-集合论基础.md")

print(f"文件: {result.file_name}")
print(f"总体评分: {result.overall_score:.2f}")
print(f"质量等级: {result.quality_level}")

# 生成报告
generator = ReportGenerator()
generator.generate_html_report([result], assessor.get_summary())
```

#### 批量评估
```python
# 评估整个目录
results = assessor.assess_directory("docs/01-基础数学")

# 获取汇总统计
summary = assessor.get_summary()
print(f"平均分数: {summary['average_score']:.2f}")
print(f"质量问题: {summary['high_priority_issues']} 个")
```

#### 生成多种格式报告
```python
from report_generator import ReportGenerator

generator = ReportGenerator(output_dir="reports")

# HTML报告（可视化）
html_path = generator.generate_html_report(results, summary)

# Markdown报告（便于版本控制）
md_path = generator.generate_markdown_report(results, summary)

# JSON报告（数据交换）
json_path = generator.generate_json_report(results, summary)

# CSV报告（表格分析）
csv_path = generator.generate_csv_report(results)
```

#### 提取和导出问题
```python
from issue_extractor import IssueExtractor

extractor = IssueExtractor()

# 从评估结果中提取问题
for result in results:
    extractor.extract_from_result(result.__dict__)

# 生成问题清单报告
report_path = extractor.generate_issue_report()

# 导出JSON格式
json_path = extractor.export_issues_json()

# 获取行动计划
action_plan = extractor.generate_action_plan()
print(f"预估总工时: {action_plan['total_estimated_hours']} 小时")
```

## 评估指标详解

### 完整性评分 (25%权重)

| 检查项 | 权重 | 说明 |
|--------|------|------|
| 概念定义 | 高 | 是否包含清晰的定义部分 |
| 定理证明 | 高 | 定理与证明的匹配度 |
| 示例覆盖 | 中 | 示例数量与质量 |
| 参考文献 | 低 | 引用完整性 |
| MSC编码 | 低 | 数学主题分类编码 |

### 准确性评分 (25%权重)

| 检查项 | 检测内容 |
|--------|----------|
| 公式语法 | 括号匹配、格式正确性 |
| 引用格式 | 引用一致性 |
| 链接检查 | 内部/外部链接有效性 |
| 符号一致 | 数学符号使用统一 |

### 可读性评分 (20%权重)

| 指标 | 理想范围 | 检测方法 |
|------|----------|----------|
| 句子长度 | 15-25字 | 平均字符数 |
| 段落长度 | 3-5句 | 平均句子数 |
| 复杂词比例 | 10-20% | 长词统计 |
| 标题结构 | 层级连续 | 层级跳跃检测 |

### 国际化评分 (15%权重)

| 检查项 | 评估标准 |
|--------|----------|
| 英文术语 | 关键术语英文对照 |
| 术语一致性 | 中英术语使用统一 |
| 文化适应 | 国际化内容特征 |
| 翻译完整 | 无遗漏翻译 |

### 学习效果评分 (15%权重)

| 指标 | 计算方法 |
|------|----------|
| 难度评估 | 关键词频率分析 |
| 学习时长 | 内容长度 + 复杂度 |
| 掌握概率 | 练习完整性 |
| 前置知识 | 预备知识清晰度 |

## 质量等级定义

| 等级 | 分数范围 | 描述 | 建议操作 |
|------|----------|------|----------|
| EXCELLENT | 90-100 | 优秀 | 可作为标杆 |
| GOOD | 80-89 | 良好 | 小幅改进 |
| ACCEPTABLE | 60-79 | 可接受 | 需关注改进 |
| NEEDS_IMPROVEMENT | 40-59 | 需改进 | 优先修复 |
| POOR | 0-39 | 差 | 必须重写 |

## 问题清单分类

### 按严重程度
- 🔴 **High**: 影响理解的核心问题
- 🟡 **Medium**: 影响体验的重要问题
- 🔵 **Low**: 建议改进的优化项

### 按类型
- **内容缺失**: 缺少必要的内容元素
- **公式错误**: 数学公式语法问题
- **引用问题**: 引用格式或链接问题
- **符号不一致**: 数学符号混用
- **可读性问题**: 影响阅读体验
- **国际化问题**: 多语言内容问题
- **学习效果问题**: 影响学习效果

## 输出示例

### 控制台输出
```
评估完成: 15个文件
平均分: 76.5
最高分: 92.3
最低分: 45.2
高优先级问题: 8
质量分布:
  - EXCELLENT: 2
  - GOOD: 5
  - ACCEPTABLE: 5
  - NEEDS_IMPROVEMENT: 2
  - POOR: 1
```

### JSON输出结构
```json
{
  "summary": {
    "total_files": 15,
    "average_score": 76.5,
    "quality_distribution": {...}
  },
  "results": [
    {
      "file_name": "example.md",
      "overall_score": 85.2,
      "quality_level": "GOOD",
      "completeness": {...},
      "accuracy": {...},
      "readability": {...},
      "internationalization": {...},
      "learning_effect": {...},
      "recommendations": [...],
      "issues": [...]
    }
  ]
}
```

## 配置文件

可通过修改评估参数来调整评分标准：

```python
# quality_assessor.py 中的参数
self.formula_patterns = [...]  # 公式匹配模式
self.math_terms = {...}        # 数学术语词典
```

## 集成到CI/CD

### GitHub Actions示例
```yaml
name: Content Quality Check

on: [push, pull_request]

jobs:
  quality-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Set up Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.8'
      - name: Run quality assessment
        run: |
          python tools/content-quality-assessment/quality_assessor.py docs/ -r -o report.json
      - name: Upload report
        uses: actions/upload-artifact@v2
        with:
          name: quality-report
          path: report.json
```

## 开发计划

### 已完成功能
- [x] 基础质量评估
- [x] 多格式报告生成
- [x] 问题清单提取
- [x] 行动计划生成

### 计划功能
- [ ] 增量评估（仅检查修改的文件）
- [ ] 历史趋势分析
- [ ] 自动修复建议
- [ ] Web界面
- [ ] 与其他系统集成

## 贡献指南

欢迎提交Issue和PR来改进这个工具。

### 提交Issue
- 描述遇到的问题
- 提供示例文档
- 说明期望的行为

### 提交PR
- 遵循现有代码风格
- 添加必要的测试
- 更新文档

## 许可证

MIT License - 详见项目根目录LICENSE文件

## 联系方式

- 项目主页: FormalMath项目
- 问题反馈: GitHub Issues

---

**版本**: 1.0.0  
**最后更新**: 2026年4月4日
