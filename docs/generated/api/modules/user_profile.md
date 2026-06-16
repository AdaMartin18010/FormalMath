---
msc_primary: '00

  - 00A99'
title: user_profile
processed_at: '2026-04-05'
review_status: draft
references:
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
msc_primary: "00A99"
msc_secondary: ['00-00']
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
---
**参考文献**

1. 相关教材与学术论文。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845