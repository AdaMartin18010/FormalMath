---
title: FormalMath 元数据管理系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 元数据管理系统

## 概述

FormalMath 元数据管理系统是一个统一的文档元数据管理解决方案，提供元数据提取、查询、版本控制和质量检查功能。

## 系统组件

```
metadata-system/
├── metadata-standard.md      # 元数据标准规范
├── metadata_extractor.py     # 元数据提取工具
├── metadata_query.py         # 元数据查询系统
├── version_control.py        # 版本控制系统
├── quality_control.py        # 质量控制系统
├── metadata_cli.py           # 统一CLI工具
└── README.md                 # 本文档
```

## 快速开始

### 1. 安装依赖

```bash
pip install pyyaml
```

### 2. 扫描文档提取元数据

```bash
python tools/metadata-system/metadata_cli.py scan
```

### 3. 查询文档

```bash
# 按分类查询
python tools/metadata-system/metadata_cli.py query --category "代数结构"

# 按难度查询
python tools/metadata-system/metadata_cli.py query --difficulty L2

# 组合条件查询
python tools/metadata-system/metadata_cli.py query --category "代数结构" --has-proofs true
```

### 4. 全文搜索

```bash
python tools/metadata-system/metadata_cli.py search "群论"
```

### 5. 质量检查

```bash
# 检查所有文档
python tools/metadata-system/metadata_cli.py quality-check

# 检查单个文件
python tools/metadata-system/metadata_cli.py check-file docs/02-代数结构/群论.md
```

## 元数据标准

### 必需字段

```yaml
---
title: 文档标题
created_date: 2025-01-15
version: 1.0.0
---
```

### 推荐字段

```yaml
---
title: 群论基础
created_date: 2025-01-15
version: 1.0.0
msc_primary: 20-01
msc_secondary: [20A05, 20B30]
category: 代数结构
difficulty: L2
depth_level: 深度扩展版
author: AI Assistant
status: published
quality_score: 95
related_concepts: [群, 子群, 同态]
prerequisites: [集合论]
has_proofs: true
has_examples: true
has_lean4: false
---
```

## CLI 命令参考

### scan - 扫描文档

```bash
python metadata_cli.py scan [选项]

选项:
  -p, --pattern    文件匹配模式 (默认: **/*.md)
  --no-stats       不显示统计信息
```

### query - 查询文档

```bash
python metadata_cli.py query [选项]

选项:
  --category       内容分类
  --difficulty     难度等级 (L0-L4)
  --status         文档状态
  --msc            MSC主分类
  --has-proofs     是否含证明 (true/false)
  --has-examples   是否含例子 (true/false)
  --has-lean4      是否含Lean4 (true/false)
  --min-score      最低质量分
```

### search - 全文搜索

```bash
python metadata_cli.py search <关键词>
```

### quality-check - 质量检查

```bash
python metadata_cli.py quality-check [选项]

选项:
  -p, --pattern    文件匹配模式
  -o, --output     输出报告文件
```

### check-file - 检查单个文件

```bash
python metadata_cli.py check-file <文件路径>
```

### version-update - 更新版本

```bash
python metadata_cli.py version-update <文件路径> <变更描述> [选项]

选项:
  --level          版本递增级别 (major/minor/patch)
```

### version-history - 查看版本历史

```bash
python metadata_cli.py version-history [--file <文件路径>]
```

### export - 导出元数据

```bash
python metadata_cli.py export [选项]

选项:
  --format         导出格式 (json/csv)
  -o, --output     输出文件路径
```

### stats - 显示统计信息

```bash
python metadata_cli.py stats
```

## 独立工具使用

### 元数据提取器

```python
from metadata_extractor import MetadataExtractor

extractor = MetadataExtractor('.')
records = extractor.scan_directory('**/*.md')
extractor.export_to_json('metadata.json')
extractor.export_to_csv('metadata.csv')
```

### 元数据查询

```python
from metadata_query import MetadataQuery

query = MetadataQuery('metadata.json')
results = query.query(
    category='代数结构',
    difficulty='L2',
    has_proofs=True
)
```

### 版本控制

```python
from version_control import MetadataVersionManager

manager = MetadataVersionManager('.')
new_version = manager.update_document_version(
    'docs/群论.md',
    '添加新定理证明',
    level='minor'
)
```

### 质量控制

```python
from quality_control import QualityControl

qc = QualityControl('.')
reports = qc.scan_directory('**/*.md')
qc.generate_report('quality_report.json')
```

## 质量检查维度

| 维度 | 权重 | 说明 |
|------|------|------|
| 元数据完整性 | 25% | 检查必需和推荐字段 |
| 内容结构 | 25% | 标题、段落、证明、例子 |
| 符号一致性 | 20% | LaTeX语法、术语标准 |
| 引用有效性 | 15% | 链接、图片、参考文献 |
| 格式合规性 | 10% | Markdown规范 |
| 可访问性 | 5% | 无障碍标准 |

## 版本控制策略

使用语义化版本控制 (SemVer):

- **MAJOR** (x.0.0): 重大结构变更
- **MINOR** (x.y.0): 功能新增
- **PATCH** (x.y.z): Bug修复

## 难度等级

| 等级 | 名称 | 描述 |
|------|------|------|
| L0 | 直观经验层 | 基于直觉的概念 |
| L1 | 形式化定义层 | 严格的数学定义 |
| L2 | 定理证明层 | 定理及其证明 |
| L3 | 理论建构层 | 理论体系构建 |
| L4 | 前沿研究层 | 前沿研究主题 |

## 状态定义

| 状态 | 说明 |
|------|------|
| draft | 草稿，尚未完成 |
| review | 审核中 |
| published | 已发布 |
| deprecated | 已弃用 |
| archived | 已归档 |

## 集成到工作流

### Git 钩子示例

```bash
# .git/hooks/pre-commit
#!/bin/bash
python tools/metadata-system/metadata_cli.py quality-check
```

### 定期质量报告

```bash
#!/bin/bash
# 生成每周质量报告
date=$(date +%Y%m%d)
python tools/metadata-system/metadata_cli.py quality-check -o "reports/quality_${date}.json"
```

## 故障排除

### YAML 解析错误

确保元数据使用正确的 YAML 格式：
- 使用空格缩进（非Tab）
- 字符串值使用引号包裹（如有特殊字符）
- 日期格式: YYYY-MM-DD

### 编码问题

所有工具默认使用 UTF-8 编码。如遇编码错误，检查文件编码：

```bash
file -i document.md
```

## 扩展开发

如需扩展系统功能：

1. 在相应模块中添加新方法
2. 在 `metadata_cli.py` 中添加命令处理
3. 更新本文档

## 许可证

MIT License - 参见项目根目录 LICENSE 文件
