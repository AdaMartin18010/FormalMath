---
msc_primary: 00

  - 00A99
title: scoring_engine
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# scoring_engine

**源文件**: `tools\assessment-system\scoring_engine.py`

## 类

### ScoringAlgorithm

```python
class ScoringAlgorithm

```

评分算法基类

### WeightedScoringModel

```python
class WeightedScoringModel

```

加权评分模型

支持多维度加权评分，可配置不同维度和指标的权重

### ValueAddedScoringModel

```python
class ValueAddedScoringModel

```

增值评分模型

评估学习者在一定时期内的能力提升和价值增值

### PerformanceScoringModel

```python
class PerformanceScoringModel

```

表现性评分模型

评估学习者在真实任务情境中的表现

### DivergentThinkingScoringModel

```python
class DivergentThinkingScoringModel

```

发散思维评分模型

评估学习者的创造性思维能力

### ProcessScoringModel

```python
class ProcessScoringModel

```

过程性评分模型

评估学习过程中的参与度和行为

### ScoringEngine

```python
class ScoringEngine

```

评分引擎主类

整合所有评分模型，提供统一的评分接口

