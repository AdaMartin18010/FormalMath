# FormalMath 评估系统

FormalMath Assessment System - 面向形式化数学知识库的多维度评估系统

## 概述

FormalMath 评估系统是一个全面的数学学习能力评估框架，支持：

- **五维数学能力评估**（MAA标准对齐）：概念理解、程序流畅性、策略能力、适应性推理、数学产出
- **过程性评价**：跟踪学习过程、评估参与度、分析学习行为
- **增值评价**：评估能力提升和知识增长
- **表现性评价**：评估真实任务情境中的表现
- **发散思维评价**：评估创造性思维能力

## 文件结构

```
tools/assessment-system/
├── README.md                    # 本文件
├── assessment_system.py         # 核心评估系统
├── evaluation_criteria.py       # 评价指标定义
├── scoring_engine.py            # 评分引擎
├── feedback_generator.py        # 反馈生成器
├── report_generator.py          # 报告生成器
└── demo.py                      # 演示脚本
```

## 安装与依赖

### 系统要求

- Python 3.8+
- 无第三方依赖（仅使用Python标准库）

### 安装步骤

1. 确保Python版本符合要求:
```bash
python --version
```

2. 无需额外安装，直接使用

## 快速开始

### 1. 导入评估系统

```python
from assessment_system import FormalMathAssessmentSystem, AssessmentConfig, AssessmentType
from evaluation_criteria import LearnerProfile, MathematicalAbilityProfile
```

### 2. 初始化系统

```python
# 使用默认配置
assessment_system = FormalMathAssessmentSystem()

# 或使用自定义配置
config = AssessmentConfig(
    ability_weights={
        'conceptual_understanding': 0.20,
        'procedural_fluency': 0.20,
        'strategic_competence': 0.25,
        'adaptive_reasoning': 0.25,
        'productive_disposition': 0.10
    }
)
assessment_system = FormalMathAssessmentSystem(config)
```

### 3. 注册学习者

```python
# 注册新学习者
profile = assessment_system.register_learner("student_001", "张三")
```

### 4. 设置能力档案

```python
from evaluation_criteria import (
    ConceptualUnderstanding, ProceduralFluency, StrategicCompetence,
    AdaptiveReasoning, ProductiveDisposition
)

# 创建能力档案
ability_profile = MathematicalAbilityProfile(
    conceptual_understanding=ConceptualUnderstanding(
        concept_mastery=75.0,
        principle_comprehension=70.0,
        relationship_grasp=65.0
    ),
    procedural_fluency=ProceduralFluency(
        accuracy=80.0,
        efficiency=70.0,
        flexibility=60.0
    ),
    strategic_competence=StrategicCompetence(
        problem_analysis=65.0,
        strategy_formulation=70.0,
        strategy_execution=60.0
    ),
    adaptive_reasoning=AdaptiveReasoning(
        logical_thinking=70.0,
        justification_ability=65.0,
        explanation_clarity=60.0
    ),
    productive_disposition=ProductiveDisposition(
        confidence=75.0,
        persistence=80.0,
        appreciation=70.0
    )
)

# 更新学习者能力档案
assessment_system.update_learner_ability("student_001", ability_profile)
```

### 5. 进行评估

#### 形成性评价

```python
result = assessment_system.conduct_formative_assessment("student_001")
print(f"综合得分: {result.overall_score}")
print(f"能力等级: {result.level}")
```

#### 总结性评价

```python
result = assessment_system.conduct_summative_assessment("student_001")
```

#### 过程性评价

```python
# 记录学习活动
assessment_system.record_learning_activity("student_001", {
    'date': '2026-02-15',
    'duration': 45,  # 分钟
    'topics': ['代数', '几何'],
    'is_active_learning': True
})

# 进行过程性评价
result = assessment_system.conduct_process_assessment(
    "student_001",
    learning_path={'content_items': ['章节1', '章节2']},
    period_days=7
)
```

#### 增值评价

```python
result = assessment_system.conduct_value_added_assessment(
    "student_001",
    period_days=30
)
```

### 6. 生成报告

```python
from report_generator import ReportType, ReportFormat

# 生成能力评估报告
report = assessment_system.generate_report(
    ReportType.ABILITY,
    "student_001",
    detailed=True
)

# 导出为Markdown
assessment_system.export_report(
    report,
    ReportFormat.MARKDOWN,
    "report.md"
)

# 导出为HTML
assessment_system.export_report(
    report,
    ReportFormat.HTML,
    "report.html"
)

# 导出为JSON
assessment_system.export_report(
    report,
    ReportFormat.JSON,
    "report.json"
)
```

## 核心功能详解

### 1. 五维数学能力评估

基于MAA（美国数学协会）标准，评估五个核心维度：

| 维度 | 描述 | 核心指标 |
|------|------|----------|
| 概念理解 | 对数学概念、原理、关系的理解程度 | 概念掌握度、原理理解度、关系把握度 |
| 程序流畅性 | 执行数学程序的灵活、准确、高效程度 | 准确性、效率、灵活性 |
| 策略能力 | 制定和运用数学策略解决问题的能力 | 问题分析、策略制定、策略执行 |
| 适应性推理 | 进行逻辑思考、解释、论证的能力 | 逻辑思维、论证能力、解释清晰度 |
| 数学产出 | 将数学视为有意义、有价值、可掌握的学科的态度 | 自信心、坚持性、欣赏度 |

### 2. 评分引擎

```python
from scoring_engine import ScoringEngine

scoring_engine = ScoringEngine()

# 评估数学能力
result = scoring_engine.evaluate_mathematical_ability(ability_profile)

# 评估学习过程
process_scores = scoring_engine.evaluate_process(
    learner_profile, learning_history, learning_path
)

# 评估增值
value_added = scoring_engine.evaluate_value_added(learner_profile)
```

### 3. 反馈生成

```python
from feedback_generator import FeedbackGenerator

feedback_gen = FeedbackGenerator()

# 生成综合反馈
feedback_report = feedback_gen.generate_feedback(
    learner_profile, assessment_result
)

# 生成过程性反馈
process_feedback = feedback_gen.generate_process_feedback(
    learner_id, process_scores
)
```

### 4. 实时反馈

```python
# 答题反馈
feedback = assessment_system.generate_answer_feedback(
    learner_id="student_001",
    is_correct=True,
    attempt_count=1,
    time_spent=120  # 秒
)

# 学习过程实时反馈
realtime_feedback = assessment_system.generate_real_time_feedback(
    learner_id="student_001",
    interaction_data={
        'error_count': 3,
        'time_spent': 600,
        'consecutive_correct': 5
    }
)
```

### 5. 报告生成

支持多种报告类型：

- `ReportType.PROGRESS` - 学习进度报告
- `ReportType.ABILITY` - 能力评估报告
- `ReportType.VALUE_ADDED` - 增值评价报告
- `ReportType.COMPREHENSIVE` - 综合评价报告

支持多种导出格式：

- `ReportFormat.JSON` - JSON格式
- `ReportFormat.MARKDOWN` - Markdown格式
- `ReportFormat.HTML` - HTML格式

## 运行演示

```bash
cd tools/assessment-system
python demo.py
```

演示脚本展示以下功能：

1. 基础评估功能
2. 评分引擎使用
3. 反馈生成
4. 完整评估系统流程
5. 表现性评价
6. 发散思维评价
7. 实时反馈
8. 认知诊断系统对接

## 与认知诊断系统对接

评估系统提供与认知诊断系统的对接接口：

```python
# 注册诊断回调
def diagnosis_callback(data):
    print(f"接收到诊断数据: {data}")

assessment_system.register_diagnosis_callback(diagnosis_callback)

# 获取学习者诊断档案
diagnosis_profile = assessment_system.get_learner_diagnosis_profile("student_001")

# 通知诊断系统
assessment_system.notify_diagnosis_system({
    'type': 'ability_update',
    'learner_id': 'student_001'
})
```

## API 参考

### AssessmentSystem 主要方法

| 方法 | 描述 |
|------|------|
| `register_learner(learner_id, name)` | 注册学习者 |
| `update_learner_ability(learner_id, ability)` | 更新能力档案 |
| `update_learner_knowledge(learner_id, concept, mastery)` | 更新知识状态 |
| `record_learning_activity(learner_id, data)` | 记录学习活动 |
| `conduct_formative_assessment(learner_id)` | 形成性评价 |
| `conduct_summative_assessment(learner_id)` | 总结性评价 |
| `conduct_process_assessment(learner_id, ...)` | 过程性评价 |
| `conduct_value_added_assessment(learner_id, ...)` | 增值评价 |
| `conduct_performance_assessment(learner_id, data)` | 表现性评价 |
| `conduct_divergent_assessment(learner_id, data)` | 发散思维评价 |
| `generate_report(report_type, learner_id, ...)` | 生成报告 |
| `export_report(report, format, filepath)` | 导出报告 |

### 评分等级

| 等级 | 分数范围 | 描述 |
|------|----------|------|
| EXPERT | 95-100 | 专家 - 能够创造新知和指导他人 |
| ADVANCED | 80-95 | 高级 - 能够灵活应用和迁移知识 |
| PROFICIENT | 60-80 | 熟练 - 能够独立应用知识和技能 |
| DEVELOPING | 40-60 | 发展中 - 正在发展理解和应用能力 |
| BEGINNER | 0-40 | 初级 - 正在建立基础概念和技能 |

## 配置选项

### AssessmentConfig 配置项

```python
config = AssessmentConfig(
    # 能力维度权重
    ability_weights={
        'conceptual_understanding': 0.20,
        'procedural_fluency': 0.20,
        'strategic_competence': 0.25,
        'adaptive_reasoning': 0.25,
        'productive_disposition': 0.10
    },
    
    # 评分阈值
    thresholds={
        'excellent': 80.0,
        'good': 60.0,
        'passing': 40.0
    },
    
    # 评估周期（天）
    evaluation_periods={
        'formative': 7,
        'summative': 30,
        'process': 7,
        'value_added': 30
    },
    
    # 反馈配置
    feedback_config={
        'generate_real_time': True,
        'generate_summary': True,
        'suggestion_count': 5
    }
)
```

## 设计文档

本评估系统的详细设计文档位于：

```
project/00-评价体系框架设计文档-2025年11月30日.md
```

## 贡献与维护

本评估系统为 FormalMath 形式化数学知识库项目的组成部分。

## 许可

与 FormalMath 项目保持一致。
