---
msc_primary: 00A99
msc_secondary:
- 00A99
title: user_profile
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# user_profile

**源文件**: `tools\personalized-recommendation\user_profile.py`

## 类

### LearningStyle

```python
class LearningStyle

```

学习风格类型 - 基于Felder-Silverman学习风格模型简化版

### ProficiencyLevel

```python
class ProficiencyLevel

```

熟练度等级

### LearningGoalPriority

```python
class LearningGoalPriority

```

学习目标优先级

### ConceptMastery

```python
class ConceptMastery

```

概念掌握度记录

### LearningPreference

```python
class LearningPreference

```

学习偏好设置

### TimePreference

```python
class TimePreference

```

时间偏好设置

### LearningGoal

```python
class LearningGoal

```

学习目标定义

### LearningHistory

```python
class LearningHistory

```

学习历史记录

### UserProfile

```python
class UserProfile

```

用户画像 - 个性化学习路径推荐的核心数据结构

包含用户的学习特征、目标、偏好和历史记录

## 函数

### create_preset_profile

```python
def create_preset_profile(preset_type: str, name: str = , email: str = ) -> UserProfile

```

从预设模板创建用户画像

**参数**:

- `preset_type: str`
- `name: str`
- `email: str`

