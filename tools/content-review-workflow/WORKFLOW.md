# 内容审核工作流详细文档

本文档详细描述内容审核工作流的设计原理、使用方法和最佳实践。

## 目录

1. [系统架构](#系统架构)
2. [审核流程详解](#审核流程详解)
3. [质量检查规则](#质量检查规则)
4. [人工审核指南](#人工审核指南)
5. [状态管理](#状态管理)
6. [报告系统](#报告系统)
7. [最佳实践](#最佳实践)

## 系统架构

### 整体架构

```
┌─────────────────────────────────────────────────────────────┐
│                    Content Review Workflow                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │   Submit     │→ │    Auto      │→ │   Manual     │      │
│  │   Document   │  │   Review     │  │   Review     │      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
│         │                 │                 │               │
│         ↓                 ↓                 ↓               │
│  ┌──────────────────────────────────────────────────┐     │
│  │              Review Tracker                       │     │
│  │         (State Management)                        │     │
│  └──────────────────────────────────────────────────┘     │
│         │                                                 │
│         ↓                                                 │
│  ┌──────────────────────────────────────────────────┐     │
│  │           Report Generator                        │     │
│  └──────────────────────────────────────────────────┘     │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 核心组件

#### 1. ContentReviewWorkflow (主控模块)
- 整合所有子系统
- 提供统一的API接口
- 管理审核生命周期

#### 2. QualityChecker (质量检查器)
- 自动质量评估
- 多维度检查规则
- 可扩展的检查框架

#### 3. ReviewTracker (状态追踪)
- 审核状态管理
- 事件记录
- 持久化存储

#### 4. ManualReviewWorkflow (人工审核)
- 交互式审核流程
- 决策支持
- 批量处理

#### 5. ReviewReportGenerator (报告生成)
- 多格式输出
- 统计分析
- 可视化支持

## 审核流程详解

### 标准审核流程

```
1. 文档提交
   └── 提交者上传文档
   └── 系统自动创建审核记录
   └── 状态: PENDING

2. 质量预检
   └── 自动质量检查
   └── 生成质量报告
   └── 计算质量得分

3. 自动审核决策
   ├── 得分 ≥ 90 且无错误
   │   └── 自动通过 → APPROVED → PUBLISHED
   ├── 得分 < 30 或错误过多
   │   └── 自动拒绝 → REJECTED
   └── 其他情况
       └── 进入人工审核 → IN_REVIEW

4. 人工审核 (如需要)
   └── 分配审核员
   └── 人工质量评估
   └── 审核决策:
       ├── 通过 → APPROVED → PUBLISHED
       ├── 需修改 → NEEDS_REVISION
       └── 拒绝 → REJECTED

5. 修改重提 (如需要)
   └── 提交者修改文档
   └── 重新提交
   └── 返回步骤 2
```

### 三级审核体系

#### Level 1: 自动审核
- **触发条件**: 日常更新、小修改
- **处理方式**: 全自动
- **通过标准**: 质量得分 ≥ 90，无错误
- **适用场景**: 内容补充、格式修正、链接更新

#### Level 2: 半自动审核
- **触发条件**: 重大更新、结构调整
- **处理方式**: 自动检查 + 人工确认
- **通过标准**: 1名审核员确认
- **适用场景**: 概念重写、新增章节、结构调整

#### Level 3: 完全人工审核
- **触发条件**: 关键内容、新分类
- **处理方式**: 完全人工
- **通过标准**: 2名审核员确认
- **适用场景**: 新建概念、核心定理、争议内容

## 质量检查规则

### 规则配置文件

规则配置在 `review_rules.yaml` 中定义：

```yaml
quality_rules:
  structure:
    - name: required_headers
      required: [concept_id, concept_name, category, created_date]
      severity: error
      
  content:
    - name: min_content_length
      min_length: 200
      severity: warning
      
  formatting:
    - name: markdown_lint
      rules: [no_trailing_spaces, proper_heading_hierarchy]
      severity: warning
```

### 检查类型

#### 结构检查
| 规则 | 说明 | 严重级别 |
|------|------|----------|
| required_headers | 必需字段检查 | Error |
| section_completeness | 章节完整性 | Warning |
| yaml_frontmatter | YAML格式 | Error |

#### 内容检查
| 规则 | 说明 | 严重级别 |
|------|------|----------|
| min_content_length | 最小长度 | Warning |
| max_content_length | 最大长度 | Info |
| terminology_check | 术语一致性 | Warning |
| formula_validation | 公式验证 | Error |

#### 格式检查
| 规则 | 说明 | 严重级别 |
|------|------|----------|
| markdown_lint | Markdown规范 | Warning |
| code_block_language | 代码块语言 | Info |
| link_validation | 链接有效性 | Warning |

### 质量得分计算

```
基础得分 = 100

扣分项:
- 错误 (Error): -10 分/个
- 警告 (Warning): -3 分/个  
- 信息 (Info): -1 分/个

最终得分 = max(0, 基础得分 - 总扣分)
```

## 人工审核指南

### 审核检查清单

#### 内容准确性 (权重 1.0)
- [ ] 数学概念定义准确
- [ ] 定理陈述正确
- [ ] 公式推导无误
- [ ] 引用来源可靠

#### 内容完整性 (权重 0.9)
- [ ] 包含清晰定义
- [ ] 提供充分示例
- [ ] 证明完整严谨
- [ ] 交叉引用适当

#### 表述清晰度 (权重 0.8)
- [ ] 语言简洁明了
- [ ] 逻辑结构清晰
- [ ] 符号使用一致
- [ ] 难度层次合理

#### 术语规范性 (权重 0.8)
- [ ] 使用标准术语
- [ ] 中英文对照准确
- [ ] 缩写规范统一
- [ ] 符合项目约定

#### 格式规范性 (权重 0.6)
- [ ] Markdown 格式正确
- [ ] 数学公式规范
- [ ] 代码块标记完整
- [ ] 标题层级合理

### 评分标准

每个检查项按 1-5 分评分：

| 分数 | 含义 | 说明 |
|------|------|------|
| 5 | 优秀 | 无可挑剔，可作为范例 |
| 4 | 良好 | 轻微瑕疵，不影响使用 |
| 3 | 合格 | 需要改进，基本可用 |
| 2 | 较差 | 需要大幅修改 |
| 1 | 不合格 | 无法接受，必须重写 |

### 决策标准

```
自动得分 × 0.7 + 人工得分 × 0.3 = 综合得分

综合得分 ≥ 80: 建议通过
综合得分 60-80: 建议修改后通过
综合得分 < 60: 建议拒绝
```

## 状态管理

### 状态定义

| 状态 | 说明 | 允许的操作 |
|------|------|------------|
| PENDING | 待审核 | 开始审核、拒绝 |
| IN_REVIEW | 审核中 | 批准、需修改、拒绝 |
| NEEDS_REVISION | 需修改 | 重新提交 |
| APPROVED | 已通过 | 发布 |
| PUBLISHED | 已发布 | 无 |
| REJECTED | 已拒绝 | 重新提交 |

### 状态转换矩阵

```
              │ PENDING │ IN_REVIEW │ NEEDS_REVISION │ APPROVED │ PUBLISHED │ REJECTED │
──────────────┼─────────┼───────────┼────────────────┼──────────┼───────────┼──────────┤
PENDING       │    -    │    ✓      │       -        │    -     │     -     │    ✓     │
IN_REVIEW     │    -    │    -      │       ✓        │    ✓     │     -     │    ✓     │
NEEDS_REVISION│    ✓    │    -      │       -        │    -     │     -     │    -     │
APPROVED      │    -    │    -      │       -        │    -     │     ✓     │    -     │
PUBLISHED     │    -    │    -      │       -        │    -     │     -     │    -     │
REJECTED      │    ✓    │    -      │       -        │    -     │     -     │    -     │
```

### 事件追踪

每个状态变更都会记录事件：

```json
{
  "timestamp": "2024-01-15T10:30:00",
  "status": "approved",
  "action": "status_change",
  "reviewer": "bob",
  "comment": "内容准确，格式规范"
}
```

## 报告系统

### 报告类型

#### 1. 汇总报告 (Summary Report)

**用途**: 了解整体审核状况

**包含内容**:
- 文档总数和状态分布
- 近期活动统计
- 积压项目数量
- 审核员工作量分布

**使用示例**:
```bash
python review_workflow.py report summary \
  --output weekly_report.html \
  --format html \
  --days 7
```

#### 2. 文档报告 (Document Report)

**用途**: 追踪单个文档的审核历史

**包含内容**:
- 文档基本信息
- 完整审核时间线
- 所有审核事件
- 质量检查详情

**使用示例**:
```bash
python review_workflow.py report document \
  --document-id abc123 \
  --output doc_report.md \
  --format md
```

#### 3. 审核员报告 (Reviewer Report)

**用途**: 评估审核员工作量和效率

**包含内容**:
- 审核数量统计
- 通过率分析
- 审核速度
- 最近活动列表

**使用示例**:
```bash
python review_workflow.py report reviewer \
  --reviewer bob \
  --output bob_report.json \
  --days 30
```

#### 4. 趋势报告 (Trend Report)

**用途**: 分析审核效率趋势

**包含内容**:
- 每日提交数量
- 每日完成数量
- 平均审核时间
- 趋势图表数据

**使用示例**:
```bash
python review_workflow.py report trend \
  --output trend.html \
  --format html \
  --days 30
```

### 输出格式

系统支持三种输出格式：

#### JSON 格式
- 机器可读
- 适合进一步处理
- 完整数据结构

#### HTML 格式
- 可视化展示
- 适合分享和展示
- 包含样式和交互

#### Markdown 格式
- 简洁易读
- 适合文档嵌入
- 版本控制友好

## 最佳实践

### 提交者指南

1. **预检清单**
   - [ ] 运行本地质量检查
   - [ ] 验证 YAML frontmatter
   - [ ] 检查所有链接
   - [ ] 预览渲染效果

2. **提交规范**
   - 使用描述性的提交说明
   - 指明审核级别
   - 提供必要的背景信息

3. **响应审核意见**
   - 及时响应修改请求
   - 逐一处理反馈意见
   - 重新提交时说明修改内容

### 审核员指南

1. **审核前准备**
   - 了解文档背景
   - 查看自动质量报告
   - 确认专业领域匹配

2. **审核过程**
   - 按检查清单逐项评估
   - 提供具体的修改建议
   - 保持客观和建设性

3. **决策原则**
   - 准确性优先
   - 一致性原则
   - 及时响应

### 系统管理

1. **定期维护**
   - 清理过期记录
   - 备份审核数据
   - 更新检查规则

2. **性能优化**
   - 监控审核积压
   - 平衡审核员工作量
   - 优化自动审核阈值

3. **持续改进**
   - 收集反馈意见
   - 分析审核数据
   - 优化审核流程

## 故障排除

### 常见问题

#### Q: 质量检查得分过低
**A**: 检查以下内容：
1. YAML frontmatter 是否完整
2. 内容长度是否达标
3. 格式是否符合规范
4. 链接是否有效

#### Q: 状态无法更新
**A**: 确认：
1. 文档ID存在
2. 状态转换合法
3. 有足够的权限

#### Q: 报告生成失败
**A**: 检查：
1. 输出目录可写
2. 数据记录完整
3. 模板文件存在

## 附录

### 命令参考

| 命令 | 说明 | 示例 |
|------|------|------|
| submit | 提交文档 | `python review_workflow.py submit doc.md --submitter alice` |
| review | 审核文档 | `python review_workflow.py review ID --reviewer bob --decision approve` |
| status | 查看状态 | `python review_workflow.py status ID` |
| pending | 待审核列表 | `python review_workflow.py pending` |
| batch | 批量审核 | `python review_workflow.py batch docs/ --reviewer bob` |
| report | 生成报告 | `python review_workflow.py report summary --output report.html` |

### 配置文件模板

```json
{
  "auto_approve_threshold": 90,
  "auto_reject_threshold": 30,
  "notification_enabled": true,
  "review_levels": {
    "level_1_auto": {
      "auto": true,
      "min_score": 80
    },
    "level_2_semi": {
      "auto": false,
      "min_approvers": 1
    },
    "level_3_manual": {
      "auto": false,
      "min_approvers": 2
    }
  },
  "notifications": {
    "email": {
      "enabled": false,
      "smtp_server": "",
      "from_address": ""
    },
    "webhook": {
      "enabled": false,
      "url": ""
    }
  }
}
```
