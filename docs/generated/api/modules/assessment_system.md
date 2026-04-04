---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# assessment_system

**源文件**: `tools\assessment-system\assessment_system.py`

## 类

### AssessmentConfig

```python
class AssessmentConfig

```

评估配置

### AssessmentSession

```python
class AssessmentSession

```

评估会话

### AssessmentResult

```python
class AssessmentResult

```

评估结果

### FormalMathAssessmentSystem

```python
class FormalMathAssessmentSystem

```

FormalMath 评估系统核心类

整合所有评估功能，提供统一的评估接口

Attributes:
    config: 评估配置
    scoring_engine: 评分引擎
    feedback_generator: 反馈生成器
    report_generator: 报告生成器
    sessions: 活跃评估会话

